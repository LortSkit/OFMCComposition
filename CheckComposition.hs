module CheckComposition where

import AnBOnP
import AnBParser
import Ast
import Data.Char (isLower, toLower, toUpper)
import Data.List
import Data.Maybe (isNothing)
import Debug.Trace
import EnsuranceTools
import Lexer
import Msg

data ComposableResult = Composable | Uncomposable
  deriving (Eq, Show)

trycompose :: Protocol -> Protocol -> AnBOptsAndPars -> (ComposableResult, [String], [String], [String])
trycompose protocol1@(_, typdec1, knowledge1, _, actions1, goals1) protocol2@(_, typdec2, knowledge2, _, actions2, goals2) args =
  let noErrors = not (allErrors protocol1 protocol2)
      stuff1 = getBasePubSec typdec1 knowledge1
      stuff2 = getBasePubSec typdec2 knowledge2
      (pub, sec) = getFinalPubSec stuff1 stuff2 (actions1, actions2)
      (typeflawresresult, compterms, compsetops, faults) = typeflawresistancecheck (actions1, actions2) (goals1, goals2) (typdec1, typdec2)
      msgtupletostring (x, y) = "(" ++ getStringFromMsg x ++ "," ++ getStringFromMsg y ++ ")"
      msgtupletostringforfaults (x, y) = "{" ++ getStringFromMsg x ++ "; " ++ getStringFromMsg y ++ "}"
      finalsec = sec ++ map getStringFromMsg compterms ++ map msgtupletostring compsetops
      finalfaults = map msgtupletostringforfaults faults
      result = if typeflawresresult then Composable else Uncomposable
   in if noErrors
        then (result, pub, finalsec, finalfaults)
        else error "This is unreachable!"

-------------------------------------PUB SEC STUFF-------------------------------------

msgStrListToCommaSepStrip :: [String] -> String
msgStrListToCommaSepStrip [] = ""
msgStrListToCommaSepStrip [msg] = msg
msgStrListToCommaSepStrip (msg : msgs) = msg ++ "," ++ msgStrListToCommaSepStrip msgs

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

getfuncString :: Msg -> [Msg] -> String
getfuncString funcname msgs = getStringFromMsg funcname ++ "(" ++ msgStrListToCommaSepStrip (map getStringFromMsg msgs) ++ ")"

removeDuplicates [] = []
removeDuplicates (a : as) = if a `elem` as then removeDuplicates as else a : removeDuplicates as

getFinalPubSec :: ([String], [String], ([String], [String])) -> ([String], [String], ([String], [String])) -> (Actions, Actions) -> ([String], [String])
-- getFinalPubSec (flattypes1, pub1, sec1) (flattypes2, pub2, sec2) (actions1, actions2) | trace ("Actions: " ++ show actions2) False = undefined
getFinalPubSec (flattypes1, pub1, sec1) (flattypes2, pub2, sec2) (actions1, actions2) =
  let isAnyInSec :: [([String], [String], String)] -> (Bool, String)
      isAnyInSec [] = (False, "")
      isAnyInSec ((pub, sec, lastadded) : stuff) = if length sec > 0 && lastadded == head sec then (True, lastadded) else isAnyInSec stuff

      combinepubsec :: [([String], [String], String)] -> ([String], [String], String)
      combinepubsec [] = ([], [], "")
      combinepubsec ((pub, sec, lastadded) : stuff) =
        let (currpub, currsec, _) = combinepubsec stuff
         in (pub ++ currpub, sec ++ currsec, "")

      combinepubseccorrectlastadded :: [([String], [String], String)] -> Bool -> String -> ([String], [String])
      combinepubseccorrectlastadded stuff isSec lastadded =
        let (combinedpub, combinedsec, _) = combinepubsec stuff
            (correctpub, correctedsec) =
              if isSec
                then (combinedpub, lastadded : (filter (\x -> x /= lastadded) combinedsec))
                else (lastadded : (filter (\x -> x /= lastadded) combinedpub), combinedsec)
         in (correctpub, correctedsec)

      __fstInTriple (x, _, _) = x

      getMsgSubterms :: Msg -> ([String], [String], String)
      getMsgSubterms msg =
        let cryptScryptcase op keystring innermsg =
              let invkeystring = "inv(" ++ keystring ++ ")"
                  (currpub, currsec, lastadded) = getMsgSubterms innermsg
                  opname =
                    let (firstchar : restofstring) = show op
                     in toLower firstchar : restofstring
                  tobeadded = opname ++ "(" ++ keystring ++ "," ++ lastadded ++ ")"
               in (currpub, tobeadded : currsec ++ [keystring, invkeystring], tobeadded)
            catExpXorcase op msgs =
              let pubseclastaddedlist = map getMsgSubterms msgs
                  (isSec, lastadded) = isAnyInSec pubseclastaddedlist
                  actuallastadded = if isSec then lastadded else head (__fstInTriple (head pubseclastaddedlist))
                  (currpub, currsec) = combinepubseccorrectlastadded pubseclastaddedlist isSec actuallastadded
                  opname =
                    let (firstchar : restofstring) = show op
                     in toLower firstchar : restofstring
                  funcstring = getfuncString (Atom opname) msgs
               in if opname == "cat"
                    then (currpub, currsec, actuallastadded)
                    else (currpub, funcstring : currsec, funcstring)
         in case msg of
              Atom x -> if x `elem` pub1 || x `elem` pub2 then ([x], [], x) else ([], [x], x)
              Comp Apply (funcname : msgs) ->
                let (currpub, currsec, lastadded) = getMsgSubterms (head msgs) -- assuming here that the next message is a Comp Cat [stuff,stuff]
                    tobeadded = getfuncString funcname msgs
                    isObviouslyPub = tobeadded `elem` pub1 || tobeadded `elem` pub2
                    isObviouslySec = tobeadded `elem` fst sec1 || tobeadded `elem` snd sec1 || tobeadded `elem` fst sec2 || tobeadded `elem` snd sec2
                    insidePub = head currpub == lastadded
                 in if isObviouslyPub
                      then (tobeadded : currpub, currsec, tobeadded)
                      else
                        if isObviouslySec || not insidePub
                          then (currpub, tobeadded : currsec, tobeadded)
                          else (currpub, currsec, lastadded)
              Comp op msgs | op `elem` [Cat, Exp, Xor] -> catExpXorcase op msgs
              Comp op [key, innermsg]
                | op `elem` [Scrypt, Crypt] ->
                    case key of
                      Atom k ->
                        let keystring = k
                         in cryptScryptcase op keystring innermsg
                      Comp Apply (keyname : keyinputs) ->
                        let keystring = getfuncString keyname keyinputs
                         in cryptScryptcase op keystring innermsg
                      Comp Inv [Comp Apply (keyname : keyinputs)] ->
                        let keystring = getfuncString keyname keyinputs
                         in cryptScryptcase op keystring innermsg
              _ -> error ("Internal function 'getMsgSubterms' got an unexpected composed message! " ++ show msg)

      actionToMsg :: Action -> Msg
      actionToMsg (((sender, _, _), _, (receiver, _, _)), msg, _, _) = msg

      getActionsSubterms :: Actions -> ([String], [String], String)
      getActionsSubterms [] = ([], [], "")
      getActionsSubterms actions =
        let msgs = map actionToMsg actions
            pubseclist = map getMsgSubterms msgs
            (pub, sec, _) = combinepubsec pubseclist
         in (pub, sec, "")
      (opub1, osec1, _) = getActionsSubterms actions1
      (opub2, osec2, _) = getActionsSubterms actions2
   in (removeDuplicates opub1 ++ removeDuplicates opub2, removeDuplicates osec1 ++ removeDuplicates osec2)

getBasePubSec :: Types -> Knowledge -> ([String], [String], ([String], [String]))
getBasePubSec types knowledge =
  let concatTupleFst e1 ([], l2) = ([e1], l2)
      concatTupleFst e1 (x1 : x1s, l2) = (e1 : x1 : x1s, l2)
      concatTupleSnd e2 (l1, x2 : x2s) = (l1, e2 : x2 : x2s)
      concatTupleSnd e2 (l1, []) = (l1, [e2])

      getFlatTypes :: Types -> [String]
      getFlatTypes [] = []
      getFlatTypes ((_, flats) : ts) = flats ++ getFlatTypes ts

      _getFlatKnowledge :: Knowledge -> [Msg]
      _getFlatKnowledge ([], _) = []
      _getFlatKnowledge ((_, msgs) : ks, _) = msgs ++ getFlatKnowledge (ks, [])
      getFlatKnowledge knowledge = removeDuplicates (_getFlatKnowledge knowledge)

      _getKnowledgeAtomComp :: [Msg] -> ([String], [(String, String)])
      _getKnowledgeAtomComp [] = ([], [])
      _getKnowledgeAtomComp (msg : msgs) = case msg of
        Atom x -> concatTupleFst x (_getKnowledgeAtomComp msgs)
        Comp Apply othermsgs ->
          let recursiveBit = (_getKnowledgeAtomComp msgs)
              fstBit = getStringFromMsg (head othermsgs)
              sndBit = getStringFromMsg (head (tail othermsgs))
           in concatTupleSnd (fstBit, sndBit) recursiveBit
      getKnowledgeAtomComp knowledge = _getKnowledgeAtomComp (getFlatKnowledge knowledge)

      atomCompToString :: (String, String) -> String
      atomCompToString (funcname, concatedmsgs) = funcname ++ "(" ++ concatedmsgs ++ ")"

      flattypes = getFlatTypes types
      knowledgeatomcomp = getKnowledgeAtomComp knowledge
      pub = filter (`elem` fst knowledgeatomcomp) flattypes
      atomsec = filter (`notElem` fst knowledgeatomcomp) flattypes
      compsec = map atomCompToString (snd knowledgeatomcomp)
      sec = (atomsec, compsec)
   in (flattypes, pub, sec)

-------------------------------------BELOW ARE TYPE-FLAW RESISTANCE CHECKING STUFF-------------------------------------

getMsgFromAction :: Action -> Msg
getMsgFromAction (_, msg, _, _) = msg

getNFromTypes :: Types -> Msg
-- getNFromTypes ((typ, idents) : resttypes) | trace ("Wtf?" ++ show (typ, idents)) False = undefined
getNFromTypes [] = error "App protocol has no nonces! Exactly one nonce is required in the App protocol!"
getNFromTypes ((typ, idents) : resttypes) =
  case typ of
    Number -> if length idents /= 1 then error "App protocol more than one nonce! Exactly one nonce is required in the App protocol!" else Atom (head idents)
    _ -> getNFromTypes resttypes

getXFromTypes :: Types -> Msg
getXFromTypes [] = error "Ch protocol has no payloads! Exactly one payload is required in the Ch protocol!"
getXFromTypes ((typ, idents) : resttypes) =
  case typ of
    Payload -> if length idents /= 1 then error "Ch protocol more than one payload! Exactly one payload is required in the Ch protocol!" else Atom (head idents)
    _ -> getXFromTypes resttypes

getCSFromActions :: Actions -> (Msg, Msg)
getCSFromActions
  [ (((s1, b11, _), _, (c1, b12, _)), _, _, _),
    (((c2, b21, _), _, (s2, b22, _)), _, _, _)
    ]
    | b11 || b12 || b21 || b22 = error "App protocol has pseudonomous messages! Nothing has been proved about pseudonomous structures so we cannot say anything about App protocols with them!"
    | s1 /= s2 || c1 /= c2 = error "App protocol has wrong agent structure! Please make sure s->C then C->s (naming scheme can be changed)."
    | not (isLower (head s1)) = error ("Server has to have the not-immitatable structure, which is an agent starting with lower case. Please change '" ++ s1 ++ "' to '" ++ show (toLower (head s1)) ++ show (tail s1) ++ "'")
    | isLower (head c1) = error ("Client has to have the immitatable structure, which is an agent starting with upper case. Please change '" ++ c1 ++ "' to '" ++ show (toUpper (head c1)) ++ show (tail c1) ++ "'")
    | otherwise = (Atom s1, Atom c1)
getCSFromActions _ = error "App protocol has an incorrect number of actions! Exactly two actions is required in the App protocol!"

getABFromActions :: Actions -> (Msg, Msg)
getABFromActions
  [(((a, b1, _), _, (b, b2, _)), _, _, _)]
    | b1 || b2 = error "Ch protocol has pseudonomous messages! Nothing has been proved about pseudonomous structures so we cannot say anything about Ch protocols with them!"
    | isLower (head a) = error ("Agent A has to have the immitatable structure, which is an agent starting with upper case. Please change '" ++ a ++ "' to '" ++ show (toUpper (head a)) ++ show (tail a) ++ "'")
    | isLower (head b) = error ("Agent B has to have the immitatable structure, which is an agent starting with upper case. Please change '" ++ b ++ "' to '" ++ show (toUpper (head b)) ++ show (tail b) ++ "'")
    | otherwise = (Atom a, Atom b)
getABFromActions _ = error "Ch protocol has an incorrect number of actions! Exactly one action is required in the Ch protocol!"

listOverlap :: (Eq a) => [a] -> [a] -> Bool
listOverlap [] _ = False
listOverlap (id : restids) addedIdents = (id `elem` addedIdents) || listOverlap restids addedIdents

-- TODO: Better handeling of overlap? Example, if A is agent in both, then that's probably fine?
getIdTypeList :: Bool -> (Types, Types) -> [Ident] -> [(Ident, Type)]
getIdTypeList firstIsApp ([], []) addedIdents = []
getIdTypeList firstIsApp ([], (typ, ids) : resttypes) addedIdents
  | listOverlap ids addedIdents = error "App protocol and Ch protocol share variable names! Please make sure there is no overlap!"
  | not firstIsApp && typ == Payload = map (\id -> (id, Custom "_AppPayload")) ids ++ getIdTypeList firstIsApp ([], resttypes) (addedIdents ++ ids)
  | otherwise = map (\id -> (id, typ)) ids ++ getIdTypeList firstIsApp ([], resttypes) (addedIdents ++ ids)
getIdTypeList firstIsApp ((typ, ids) : resttypes, types2) addedIdents
  | listOverlap ids addedIdents = error "App protocol and Ch protocol share variable names! Please make sure there is no overlap!"
  | firstIsApp && typ == Payload = map (\id -> (id, Custom "_AppPayload")) ids ++ getIdTypeList firstIsApp (resttypes, types2) (addedIdents ++ ids)
  | otherwise = map (\id -> (id, typ)) ids ++ getIdTypeList firstIsApp (resttypes, types2) (addedIdents ++ ids)

tryEasyLookup :: Bool -> (Types, Types) -> Ident -> Maybe Type
tryEasyLookup firstIsApp (types1, types2) id =
  let idTypeList = getIdTypeList firstIsApp (types1, types2) []
      tryLookup :: [(Ident, Type)] -> Ident -> Maybe Type
      tryLookup [] id = Nothing
      tryLookup ((mid, typ) : rest) id = if id == mid then Just typ else tryLookup rest id
   in if id == "i" then Just (Agent False False) else tryLookup idTypeList id

matchableOperators :: Operator -> Operator -> Bool
matchableOperators op1 op2 =
  if op1 == op2
    then True
    else case (op1, op2) of
      (Userdef _, Userdef _) -> True
      _ -> False

matchableMsgs :: Msg -> Msg -> Bool
matchableMsgs msg1 msg2 =
  case (msg1, msg2) of
    (Atom _, Atom _) -> True
    (Comp _ _, Comp _ _) -> True
    _ -> False

noCats :: [Msg] -> Bool
noCats [] = True
noCats (msg : restmsgs) = case msg of
  Atom _ -> noCats restmsgs
  Comp op _ -> case op of
    Cat -> False
    _ -> noCats restmsgs

unrollCat :: Msg -> [Msg]
unrollCat msg =
  case msg of
    Comp Cat [Comp Cat _, _] -> error "Unexpected concatenation structure encountered!"
    Comp Cat [elem, Comp Cat nextmsgs] -> elem : unrollCat (Comp Cat nextmsgs)
    Comp Cat [elem1, elem2] -> [elem1, elem2]
    Comp Cat l ->
      if length l >= 3 && noCats l
        then l
        else error ("Expected concatenation, instead got " ++ show msg)

hasUndesirableMsgStructure :: Msg -> Bool
hasUndesirableMsgStructure msg = isCat msg || isAtom msg

getsubtermsofmsg :: Msg -> [Msg]
getsubtermsofmsg msg =
  let cryptScryptcase msg msgs = case msgs of
        [key, encrypted] -> case key of
          Comp Inv _ ->
            if isCat key
              then error "Unexpected key structure!"
              else
                if isAtom key
                  then
                    if hasUndesirableMsgStructure encrypted
                      then msg : getsubtermsofmsg key ++ getsubtermsofmsg encrypted
                      else msg : encrypted : getsubtermsofmsg key ++ getsubtermsofmsg encrypted
                  else
                    if hasUndesirableMsgStructure encrypted
                      then msg : key : getsubtermsofmsg key ++ getsubtermsofmsg encrypted
                      else msg : key : encrypted : getsubtermsofmsg key ++ getsubtermsofmsg encrypted
          _ ->
            if isCat key
              then error "Unexpected key structure!"
              else
                if isAtom key
                  then
                    if hasUndesirableMsgStructure encrypted
                      then msg : Comp Inv [key] : getsubtermsofmsg key ++ getsubtermsofmsg encrypted
                      else msg : Comp Inv [key] : encrypted : getsubtermsofmsg key ++ getsubtermsofmsg encrypted
                  else
                    if hasUndesirableMsgStructure encrypted
                      then msg : Comp Inv [key] : key : getsubtermsofmsg key ++ getsubtermsofmsg encrypted
                      else msg : Comp Inv [key] : key : encrypted : getsubtermsofmsg key ++ getsubtermsofmsg encrypted
        _ -> error "Unexpected structure encountered!"
      invExpXorcase op msgs =
        if length msgs /= 1
          then error ("Unexpected " ++ show op ++ "structure encountered!")
          else getsubtermsofmsg (head msgs)
   in case msg of
        Atom _ -> []
        Comp op msgs ->
          case op of
            Crypt -> cryptScryptcase msg msgs
            Scrypt -> cryptScryptcase msg msgs
            Cat -> case msgs of
              [Comp Cat _, _] -> error "Unexpected concatenation structure encountered!"
              [elem, Comp Cat nextmsgs] ->
                if hasUndesirableMsgStructure elem
                  then getsubtermsofmsg elem ++ getsubtermsofmsg (Comp Cat nextmsgs)
                  else elem : getsubtermsofmsg elem ++ getsubtermsofmsg (Comp Cat nextmsgs)
              [elem1, elem2] ->
                if hasUndesirableMsgStructure elem1 && hasUndesirableMsgStructure elem2
                  then getsubtermsofmsg elem1 ++ getsubtermsofmsg elem2
                  else
                    if hasUndesirableMsgStructure elem1
                      then elem2 : getsubtermsofmsg elem1 ++ getsubtermsofmsg elem2
                      else
                        if hasUndesirableMsgStructure elem2
                          then elem1 : getsubtermsofmsg elem1 ++ getsubtermsofmsg elem2
                          else elem1 : elem2 : getsubtermsofmsg elem1 ++ getsubtermsofmsg elem2
              l ->
                if length l >= 3 && noCats l
                  then filter (not . hasUndesirableMsgStructure) l ++ concat (map getsubtermsofmsg l)
                  else error ("Expected concatenation, instead got " ++ show msg)
            op | op `elem` [Inv, Exp, Xor] -> invExpXorcase op msgs
            Apply ->
              if length msgs /= 2
                then error "Unexpected function structure encountered!"
                else getsubtermsofmsg (head (tail msgs))
            Userdef func1 -> error "I have no idea how this error was triggered..."
            _ -> error "Unreachable!" -- Pseudonym, AuthChan, ConfChan, Neq

tryunify :: Bool -> (Types, Types) -> (Actions, Actions) -> Msg -> Msg -> Maybe Bool
tryunify firstIsApp (types1, types2) (actions1, actions2) msg1 msg2 =
  let compAtomPaircase id msg
        | firstIsApp && tryEasyLookup firstIsApp (types1, types2) id == Just Payload && msg `elem` map getMsgFromAction actions1 = Just True
        | not firstIsApp && tryEasyLookup firstIsApp (types1, types2) id == Just Payload && msg `elem` map getMsgFromAction actions2 = Just True
        | otherwise = Nothing
      invExpXorcase msgs1 msgs2 =
        if length msgs1 /= 1 || length msgs2 /= 1
          then error ("Unhandled exception: Expected list of length 1 in internal function 'tryunify', got length " ++ show (length msgs2))
          else tryunify firstIsApp (types1, types2) (actions1, actions2) (head msgs1) (head msgs2)
      cryptScryptcase msgs1 msgs2 =
        let keyRecursion = tryunify firstIsApp (types1, types2) (actions1, actions2) (head msgs1) (head msgs2)
            bodyRecursion = tryunify firstIsApp (types1, types2) (actions1, actions2) (head (tail msgs1)) (head (tail msgs2))
         in if isNothing keyRecursion
              then Nothing
              else
                if keyRecursion == Just False
                  then Just False
                  else bodyRecursion
   in case msg1 of
        Atom id1 -> case msg2 of
          Atom id2 -> Just (tryEasyLookup firstIsApp (types1, types2) id1 == tryEasyLookup firstIsApp (types1, types2) id2)
          Comp op msgs ->
            compAtomPaircase id1 msg2
        Comp op1 msgs1 -> case msg2 of
          Atom id2 ->
            compAtomPaircase id2 msg1
          Comp op2 msgs2 ->
            if not (matchableOperators op1 op2)
              then Nothing
              else case op1 of
                op | op `elem` [Crypt, Scrypt] -> cryptScryptcase msgs1 msgs2
                Cat ->
                  let firstunroll = unrollCat msg1
                      secondunroll = unrollCat msg2
                      zipped = zip firstunroll secondunroll
                      unifications = map (uncurry (tryunify firstIsApp (types1, types2) (actions1, actions2))) zipped
                   in if length firstunroll /= length secondunroll
                        then Just False
                        else
                          foldl (\mb elem -> if elem /= Just False && mb /= Just False then mb else Just False) (Just True) unifications
                op | op `elem` [Inv, Exp, Xor] -> invExpXorcase msgs1 msgs2
                Apply ->
                  let b = head msgs1 /= head msgs2
                      recursion = tryunify firstIsApp (types1, types2) (actions1, actions2) (head (tail msgs1)) (head (tail msgs2))
                   in if b then Nothing else if recursion /= Just True then Just False else recursion
                Userdef func1 -> error "I have no idea how this error was triggered..."
                _ -> error "Unreachable!" -- Pseudonym, AuthChan, ConfChan, Neq

typeflawresistancecheck :: (Actions, Actions) -> (Goals, Goals) -> (Types, Types) -> (Bool, [Msg], [(Msg, Msg)], [(Msg, Msg)])
-- typeflawresistancecheck (actions1, actions2) (goals1, goals2) (types1, types2) | trace ("omgwtfseriously: " ++ show (isAppProtocol actions1) ++ " " ++ show (if isAppProtocol actions1 then types1 else types2)) False = undefined
typeflawresistancecheck (actions1, actions2) (goals1, goals2) (types1, types2) =
  let firstIsApp = isAppProtocol actions1
      chgoaltype = if firstIsApp then getGoalType goals2 else getGoalType goals1
      -----------------------------DEFINED IN ANB------------------------------
      appprotN = getNFromTypes (if firstIsApp then types1 else types2)
      (appprotC, appprotS) = getCSFromActions (if firstIsApp then actions1 else actions2)
      appmsg1 = getMsgFromAction (if firstIsApp then head actions1 else head actions2)
      appmsg2 = getMsgFromAction (if firstIsApp then head (tail actions1) else head (tail actions2))
      chprotX = getXFromTypes (if firstIsApp then types2 else types1)
      (chprotA, chprotB) = getABFromActions (if firstIsApp then actions2 else actions1)
      chmsg3 = getMsgFromAction (if firstIsApp then head actions2 else head actions1)
      chprotSet = if chgoaltype == Secc then Atom "secCh" else Atom "authCh"
      --------------------------FROM FORMAL PROTOCOLS--------------------------
      compterms =
        [ -- appprotN, -- N
          -- appprotS, -- S
          -- appprotC, -- C
          applysent appprotS appprotC, -- sent(S,C)
          applyoutbox appprotS appprotC, -- outbox(S,C)
          applyinbox appprotS appprotC, -- inbox(S,C)
          applyoutbox appprotC appprotS, -- outbox(C,S)
          applyinbox appprotC appprotS, -- inbox(C,S)
          applyinbox appproti appprotS, -- inbox(i,S)
          applysent appprotS appproti, -- sent(S,i)
          -- chprotX, -- X
          -- chprotA, -- A
          -- chprotB, -- B
          applyoutbox chprotA chprotB, -- outbox(A,B)
          applychprotSet chprotA chprotB, -- secCh(A,B) [OR authCh(A,B)]
          applyinbox chprotA chprotB -- inbox(A,B)
        ]
      compsetops =
        [ (appprotN, applysent appprotS appprotC), -- N->sent(S,C) && N<-sent(S,C)
          (appmsg1, applyoutbox appprotS appprotC), -- [m1]->outbox(S,C)
          (appmsg1, applyinbox appprotS appprotC), -- [m1]<-inbox(S,C)
          (appmsg2, applyoutbox appprotC appprotS), -- [m2]->outbox(C,S)
          (appmsg2, applyinbox appprotC appprotS), -- [m2]<-inbox(C,S)
          (appmsg2, applyinbox appproti appprotS), -- [m2]<-inbox(i,S)
          (appprotN, applysent appprotS appproti), -- N \in sent(S,i)
          (chprotX, applyoutbox chprotA chprotB), -- X<-outbox(A,B)
          (chprotX, applychprotSet chprotA chprotB), -- wsw X->secCh(A,B) && X \in secCh(A,B) && X \notin secCh(A,B) [OR authCh -||-]
          (chprotX, applyinbox chprotA chprotB) -- x->inbox(A,B)
        ]
      appproti = Atom "i"
      applyoutbox agent1 agent2 = Comp Apply [Atom "outbox", Comp Cat [agent1, agent2]]
      applyinbox agent1 agent2 = Comp Apply [Atom "inbox", Comp Cat [agent1, agent2]]
      applysent agent1 agent2 = Comp Apply [Atom "sent", Comp Cat [agent1, agent2]]
      applychprotSet agent1 agent2 = Comp Apply [chprotSet, Comp Cat [agent1, agent2]]
      getMsgAndSubterms msg =
        if hasUndesirableMsgStructure msg
          then removeDuplicates (getsubtermsofmsg msg)
          else msg : removeDuplicates (getsubtermsofmsg msg)
      appmsg1AndSubterms = getMsgAndSubterms appmsg1
      appmsg2AndSubterms = getMsgAndSubterms appmsg2
      chmsg3AndSubterms = getMsgAndSubterms chmsg3
      allMsgs = removeDuplicates (appmsg1AndSubterms ++ appmsg2AndSubterms ++ chmsg3AndSubterms) -- trace ("Seriously, wtf? chmsg3: " ++ show chmsg3AndSubterms)
      assemblyLine :: [Msg] -> [Msg] -> [(Maybe Bool, Msg, Msg)]
      assemblyLine [] [] = []
      assemblyLine (currChecking : rest) [] = if (length rest) == 0 then [] else assemblyLine rest (tail rest)
      assemblyLine (currChecking : rest) (h : t) = (tryunify firstIsApp (types1, types2) (actions1, actions2) currChecking h, currChecking, h) : assemblyLine (currChecking : rest) t

      tobechecked = assemblyLine allMsgs (tail allMsgs) -- trace ("Seriously, wtf? Allmsgs: " ++ show allMsgs) -- ++ assemblyLine allMsgs compterms)
      -- result = foldl (\b (mbool, _, _) -> if mbool /= Just False && b /= False then b else False) True tobechecked -- trace ("Seriously, wtf? " ++ show tobechecked)
      faults = map (\(_, x, y) -> (x, y)) (filter (\(mbool, _, _) -> mbool == Just False) tobechecked)
      result = length faults == 0
   in (result, compterms, compsetops, faults)

-------------------------------------OTHER STUFF-------------------------------------

secGSMPDisjoint :: Protocol -> Protocol -> AnBOptsAndPars -> Bool
secGSMPDisjoint protocol1@(_, types1, knowledge1, _, actions1, goals1) protocol2@(_, types2, knowledge2, _, actions2, goals2) args =
  let gsmp_p1compp2star = [""]
      gsmp_p1starcompp2 = [""]
   in False

allErrors :: Protocol -> Protocol -> Bool
-- allErrors protocol1 protocol2 | trace ("Wtf?" ++ show (throwIfVertErrors protocol1 && throwIfVertErrors protocol2)) False = undefined
allErrors protocol1@(_, _, _, _, actions1, goals1) protocol2@(_, _, _, _, actions2, goals2) =
  let structureErrors = (throwIfVertErrors protocol1 || throwIfVertErrors protocol2)
      protocolTypeError = isAppProtocol actions1 == isAppProtocol actions2
      protocolTypeStr = if isAppProtocol actions1 then "App" else "Ch"
      goalType1 = getGoalType goals1
      goalType2 = getGoalType goals2
      goalTypeError = goalType1 /= goalType2
   in if structureErrors
        then error "This is unreachable!"
        else
          if protocolTypeError
            then error ("The two input protocols cannot both be " ++ protocolTypeStr ++ "! Make sure you have one App and one Ch protocol!")
            else
              if goalTypeError
                then error ("The two input protocols do not agree on their goals! OFMC input has goaltype " ++ show goalType1 ++ " and --comp input has goaltype " ++ show goalType2)
                else False

newcheckcompositionmain :: String -> String -> AnBOptsAndPars -> (ComposableResult, [String], [String], [String])
newcheckcompositionmain filestr1 filestr2 otp =
  trycompose (anbparser (alexScanTokens filestr1)) (anbparser (alexScanTokens filestr2)) otp