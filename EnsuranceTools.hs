module EnsuranceTools where

import AnBOnP
import Ast
import Data.Char (isLower, isUpper)
import Msg

isAppProtocol :: Actions -> Bool
isAppProtocol [] = False
isAppProtocol (a : as) =
  let ((_, channeltype, _), _, _, _) = a
   in case channeltype of
        ChannelProtocol _ -> True
        _ -> isAppProtocol as

isAppCompliant :: Actions -> (Bool, Int)
isAppCompliant actions = (length actions == 2, length actions)

isChCompliant :: Actions -> (Bool, Int)
isChCompliant actions = (length actions == 1, length actions)

getPayloadFromTypes :: Types -> String -> Msg
getPayloadFromTypes [] name = error ("Protocol '" ++ name ++ "' has no payloads! Exactly one payload is required in the protocol!")
getPayloadFromTypes ((typ, idents) : resttypes) name =
  case typ of
    Payload -> if length idents /= 1 then error ("Protocol '" ++ name ++ "' has more than one payload! Exactly one payload is required in the protocol!") else Atom (head idents)
    _ -> getPayloadFromTypes resttypes name

getPayloadName :: Msg -> Types -> String -> String
getPayloadName msg types name = case msg of
  Atom p -> if msg /= getPayloadFromTypes types name then error ("The variable '" ++ p ++ "' of goal msg in Protocol '" ++ name ++ "' is not a variable of type Payload!") else p
  Comp _ _ -> error ("Goal msg in Protocol '" ++ name ++ "' has to be a variable of type Payload!")

msgStrListToCommaSepStrip :: [String] -> String
msgStrListToCommaSepStrip [] = ""
msgStrListToCommaSepStrip [msg] = msg
msgStrListToCommaSepStrip (msg : msgs) = msg ++ "," ++ msgStrListToCommaSepStrip msgs

msgtupletostring :: (Msg, Msg) -> [Char]
msgtupletostring (x, y) = "(" ++ getStringFromMsg x ++ "," ++ getStringFromMsg y ++ ")"

getfuncString :: Msg -> [Msg] -> String
getfuncString funcname msgs = getStringFromMsg funcname ++ "(" ++ msgStrListToCommaSepStrip (map getStringFromMsg msgs) ++ ")"

getStringFromMsg :: Msg -> String
getStringFromMsg msg = case msg of
  Atom x -> x
  Comp Apply msgs -> getfuncString (head msgs) (tail msgs)
  Comp Cat msgs -> msgStrListToCommaSepStrip (map getStringFromMsg msgs)
  Comp Crypt msgs -> "crypt(" ++ getStringFromMsg (head msgs) ++ ", " ++ msgStrListToCommaSepStrip (map getStringFromMsg (tail msgs)) ++ ")"
  Comp Scrypt msgs -> "scrypt(" ++ getStringFromMsg (head msgs) ++ ", " ++ msgStrListToCommaSepStrip (map getStringFromMsg (tail msgs)) ++ ")"
  Comp Exp msgs -> "exp(" ++ msgStrListToCommaSepStrip (map getStringFromMsg msgs) ++ ")"
  Comp Xor msgs -> "xor(" ++ msgStrListToCommaSepStrip (map getStringFromMsg msgs) ++ ")"
  Comp Inv msgs -> "inv(" ++ msgStrListToCommaSepStrip (map getStringFromMsg msgs) ++ ")"
  _ -> error ("Internal function 'getStringFromMsg' got an unexpected composed message! " ++ show msg)

printChannelType :: ChannelType -> String
printChannelType channeltype = case channeltype of
  Insecure -> "->"
  Authentic -> "*->"
  Confidential -> "->*"
  Secure -> "*->*"
  FreshAuthentic -> "*->>"
  FreshSecure -> "*->>*"
  ChannelProtocol ident -> "-" ++ ident ++ "->"

printPeer :: Peer -> String
printPeer p =
  let (printp, _, _) = p
   in printp

printChannel :: Channel -> String
printChannel channel =
  let (p1, channeltype, p2) = channel
   in printPeer p1 ++ printChannelType channeltype ++ printPeer p2

printGoal :: Goal -> String
printGoal goal = case goal of
  ChGoal channel msg -> printChannel channel ++ ":" ++ getStringFromMsg msg
  Secret msg peers _ -> getStringFromMsg msg ++ " secret between " ++ foldl (\x y -> x ++ "," ++ printPeer y) (printPeer (head peers)) (tail peers)
  Authentication p1 p2 msg -> printPeer p1 ++ " authenticates " ++ printPeer p2 ++ " on " ++ getStringFromMsg msg
  WAuthentication p1 p2 msg -> printPeer p1 ++ " weakly authenticates " ++ printPeer p2 ++ " on " ++ getStringFromMsg msg

getGoalTypeAndPayload :: Goals -> Types -> String -> (GoalType, Peer, Peer, Msg)
getGoalTypeAndPayload goals types name =
  let numberOfGoals = length goals
      isGoalCompliant = numberOfGoals == 1
   in if not isGoalCompliant
        then error ("Protocol does not have the correct number of goals! Got " ++ show numberOfGoals ++ " goals, expected 1.")
        else case head goals of
          ChGoal channel msg ->
            let (sender, channeltype, receiver) = channel
                goaltype = case channeltype of
                  FreshAuthentic -> Auth
                  FreshSecure -> Secc
                  Confidential -> error "Confidential goaltype is not supported! Please use either *-> or *->*."
                payloadName = getPayloadName msg types name
             in if length payloadName < -1 then error "Unreachable!" else (goaltype, sender, receiver, Atom payloadName)
          x -> error ("Protocol has the wrong goaltype '" ++ printGoal x ++ "'!\nExpected Agent1*->Agent2: Payload or using *->*!")

msgUsesPayload :: Msg -> Msg -> Bool
msgUsesPayload payload msg =
  case msg of
    Atom x -> payload == msg
    Comp op msgs -> foldl (\x y -> x || msgUsesPayload payload y) False msgs

getMsgFromAction :: Action -> Msg
getMsgFromAction (_, msg, _, _) = msg

correctUseOfAgents :: Bool -> Peer -> Peer -> Actions -> Bool
correctUseOfAgents True goalsender goalreceiver actions =
  -- app
  let (receiverString, _, _) = goalreceiver
      (senderString, _, _) = goalsender
      isEqual = receiverString == senderString
      receiverIsServer = isLower (head receiverString) && isUpper (head senderString)
      actionsIsRight = case actions of
        [ ((p11, ChannelProtocol _, p12), _, _, _),
          ((p21, ChannelProtocol _, p22), _, _, _)
          ] -> p11 == p22 && p12 == p21 && p11 == goalreceiver && p12 == goalsender
        _ -> False
   in if isEqual
        then error ("Expected two different agents in goal specification!")
        else
          if not receiverIsServer
            then error ("Expected sender '" ++ senderString ++ "' to be a client (variable should be capitalized), and receiver '" ++ receiverString ++ "' to be a server (variable should NOT be capitalized) in App protocol goal specification.")
            else
              if not actionsIsRight
                then error ("Expected action structure of App protocol to be:\naction1: server -Ch-> Client\naction2. Client -Ch-> server\ngoal:Client *->[*] server\nPlease make sure only two agents are used in total and that they align with this structure!")
                else True
correctUseOfAgents False goalsender goalreceiver actions =
  -- ch
  let (receiverString, _, _) = goalreceiver
      (senderString, _, _) = goalsender
      isEqual = receiverString == senderString
      senderreceiverCapitalized = isUpper (head receiverString) && isUpper (head senderString)
      actionsIsRight = case actions of
        [((p11, Insecure, p12), _, _, _)] -> p11 == goalsender && p12 == goalreceiver
        _ -> False
   in if isEqual
        then error ("Expected two different agents in goal specification!")
        else
          if not senderreceiverCapitalized
            then error ("Expected agents in Ch protocol to be emulatable agents (both variables names must be capitalized).")
            else
              if not actionsIsRight
                then error ("Expected action structure of Ch protocol to be:\naction1: AgentA -> AgentB\ngoal:AgentA *->[*] AgentB\nPlease make sure only two agents are used in total and that they align with this structure!")
                else True

hasCorrectKnowledgeInequalities :: Bool -> Peer -> Peer -> Knowledge -> Bool
hasCorrectKnowledgeInequalities True goalsender goalreceiver knowledge =
  -- app
  let (receiverString, _, _) = goalreceiver
      (senderString, _, _) = goalsender
      correctKnowledge = case knowledge of
        (_, [(Atom p11string, Atom p12string)]) -> p11string == senderString && p12string == receiverString
        _ -> False
   in if not correctKnowledge
        then error ("Expected App protcool to include 'where Client!=server' in knowledge section (and no other inequalities).")
        else True
hasCorrectKnowledgeInequalities False goalsender goalreceiver knowledge =
  -- ch
  let (receiverString, _, _) = goalreceiver
      (senderString, _, _) = goalsender
      correctKnowledge = case knowledge of
        (_, [(Atom p11string, Atom "i"), (Atom p21string, Atom "i")]) -> p11string /= p21string && (p11string == receiverString || p11string == senderString) && (p21string == receiverString || p21string == senderString)
        _ -> False
   in if not correctKnowledge
        then error "Expected Ch protocol to include 'where AgentA!=i, AgentB!=i' in knowledge section (and no other inequalities)."
        else True

getNonceFromTypes :: Bool -> Types -> String -> Msg
getNonceFromTypes isApp [] name =
  if isApp
    then error ("Protocol '" ++ name ++ "' has no nonces (Number)! Exactly one nonce is required in the App protocol!")
    else Atom "TEMP"
getNonceFromTypes isApp ((typ, idents) : resttypes) name =
  case typ of
    Number ->
      if isApp && length idents /= 1
        then error ("Protocol '" ++ name ++ "' has more than one nonce (Number)! Exactly one nonce is required for an App protocol!")
        else
          if not isApp && length idents /= 0
            then error ("Protocol '" ++ name ++ "' has more than zero nonces (Number)! Exactly zero nonces are required for a Ch protocol!")
            else Atom (head idents)
    _ -> getNonceFromTypes isApp resttypes name

hasCorrectNonceUsage :: Bool -> String -> Types -> Actions -> Bool
hasCorrectNonceUsage True name types actions =
  -- app
  let nonce = getNonceFromTypes True types name
      Atom n = nonce
      action1 = getMsgFromAction (head actions)
      action2 = getMsgFromAction (head (tail actions))
      check = msgUsesPayload nonce action1 && msgUsesPayload nonce action2
   in if not check then error ("App protocol has incorrect usage of nonce (Number) '" ++ n ++ "': The nonce should appear in both actions!") else True
hasCorrectNonceUsage False name types actions =
  -- ch
  let nonce = getNonceFromTypes False types name
      action = getMsgFromAction (head actions)
   in if nonce /= Atom "TEMP"
        then error "Unreachable!"
        else True

hasNoSetUsage :: Types -> Bool
hasNoSetUsage [] = True
hasNoSetUsage ((typ, _) : resttypes) = if typ == Set then error ("Please do not use the Set type! No set operations are possible anyway!") else hasNoSetUsage resttypes

throwIfVertErrors :: Protocol -> Bool
-- throwIfVertErrors protocol@(_, _, _, _, actions, goals) | trace ("isApp: " ++ show (isAppProtocol actions) ++ ", length of actions: " ++ show (length actions)) False = undefined
throwIfVertErrors protocol@(name, types, knowledge, _, actions, goals) =
  let isApp = isAppProtocol actions
      (isCompliant, numActions) = if isApp then isAppCompliant actions else isChCompliant actions
      protocolType = if isApp then "App" else "Ch"
      expectedNumActions = if isApp then 2 else 1
      (goaltype, goalsender, goalreceiver, payload) = getGoalTypeAndPayload goals types name
      goaltypecheck = goaltype /= Conf -- Will throw error in getGoalType if it's not Auth or Secc, but is used below to avoid it being overlook by haskell lazy evaluation
      hascompliancyissues =
        if not isCompliant
          then error ("Protocol is not compliant with " ++ protocolType ++ " protocol: Protocol has " ++ show numActions ++ " actions, expected " ++ show expectedNumActions)
          else False

      setusagecheck = hasNoSetUsage types

      payloadusagecheck
        | not isCompliant = False -- Will trigger another error anyway
        | isApp =
            let actionmsg1 = getMsgFromAction (head actions)
                actionmsg2 = getMsgFromAction (head (tail actions))
             in if msgUsesPayload payload actionmsg1
                  then error "App protocol's first action may not use the Payload in its message! The client is supposed to send that to the server!"
                  else
                    if not (msgUsesPayload payload actionmsg2) then error "App protocol's second action must include the Payload in its message!" else True
        | otherwise =
            let actionmsg = getMsgFromAction (head actions)
             in if not (msgUsesPayload payload actionmsg) then error "Ch protocol's action must include the Payload in its message!" else True

      actiongoalstructurecheck =
        if not (payloadusagecheck)
          then False -- Will trigger another error anyway
          else correctUseOfAgents isApp goalsender goalreceiver actions

      correctKnowledge =
        if not actiongoalstructurecheck
          then False -- Will trigger another error anyway
          else hasCorrectKnowledgeInequalities isApp goalsender goalreceiver knowledge

      correctNonceUsage =
        if not correctKnowledge
          then False -- Will trigger another error anyway
          else hasCorrectNonceUsage isApp name types actions

      extractChannelNameFromActions :: Action -> String
      extractChannelNameFromActions action =
        case action of
          ((sp@(_, _, _), ChannelProtocol id, _), _, _, _) -> id
          _ -> error "Unexpectedly got an Ch protcol - Was expecting an App protocol"

      hasChannelNameErrors :: Actions -> String -> Bool
      hasChannelNameErrors actions protname
        | hascompliancyissues = error "Unreachable!1"
        | otherwise = case actions of
            [action1, action2] ->
              let id1 = extractChannelNameFromActions action1
                  id2 = extractChannelNameFromActions action2
               in if id1 /= id2
                    then error ("App protocol may not use two different channel protocols! Please make sure -" ++ id1 ++ "-> matches with -" ++ id2 ++ "->")
                    else
                      if id1 == protname
                        then error ("Disallowed use of -" ++ id1 ++ "->: The channel protocol used may not share name with the app protocol!")
                        else False
            _ -> error "Unreachable!2"
      haschannelnameerrors = if isApp then hasChannelNameErrors actions name else False
   in (not (not hascompliancyissues && not haschannelnameerrors && goaltypecheck && setusagecheck && payloadusagecheck && actiongoalstructurecheck && correctKnowledge && correctNonceUsage) && error "Unreachable!3")