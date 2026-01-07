{-

Open Source Fixedpoint Model-Checker version 2024

(C) Copyright Sebastian Moedersheim 2003,2024
(C) Copyright Jakub Janaszkiewicz 2022
(C) Copyright Paolo Modesti 2012
(C) Copyright Nicklas Bo Jensen 2012
(C) Copyright IBM Corp. 2009
(C) Copyright ETH Zurich (Swiss Federal Institute of Technology) 2003,2007

All Rights Reserved.

-}
-- Alexander Laukamp created this file, though most things are taken from Translator.hs

module VertTranslator where

import AnBOnP
import Ast
import Data.List
import Data.Maybe
import LMsg (LMsg)
import Msg
import MsgPat
import Translator

vertformats :: ProtocolTranslationState -> ProtocolTranslationState
vertformats pts =
  let (name, types, knowledge, abstractions, actions, goals) = protocol pts
      formats = concatMap snd ((filter (\(x, y) -> x == Format)) types)
      knowledge' = fKnow formats knowledge
      abstractions' = map (fAbs formats) abstractions
      actions' = map (vertfAct formats) actions
      goals' = map (fGoal formats) goals
   in pts {protocol = (name, types, knowledge', abstractions', actions', goals')}

vertfAct formats ((sp@(sender, False, Nothing), ChannelProtocol _, rp@(receiver, False, Nothing)), m, Nothing, Nothing) =
  ((sp, Insecure, rp), fMsg formats m, Nothing, Nothing)
vertfAct formats ((sp@(_, _, _), ChannelProtocol id, _), _, _, _) = error ("Unexpected app protocol error encountered: -" ++ id ++ "-> cannot be used like this!")
vertfAct formats struct = fAct formats struct

-- fChan :: (Monad m1, Monad m2) => [Ident] -> ((a1, b1, m1 Msg), b2, (a2, b3, m2 Msg)) -> ((a1, b1, m1 Msg), b2, (a2, b3, m2 Msg))
-- fChan formats (p1, chtype, p2) = (fPeer formats p1, chtype, fPeer formats p2)

-- fGoal formats (ChGoal ch m) = ChGoal (fChan formats ch) (fMsg formats m)
-- fGoal formats (Secret m ps b) = Secret (fMsg formats m) (map (fPeer formats) ps) b
-- fGoal formats (Authentication p1 p2 m) = Authentication (fPeer formats p1) (fPeer formats p2) (fMsg formats m)
-- fGoal formats (WAuthentication p1 p2 m) = WAuthentication (fPeer formats p1) (fPeer formats p2) (fMsg formats m)

---- Translation Stage 1: Creating Rules
----------------------------------------

vertcreateRules :: Bool -> GoalType -> ProtocolTranslationState -> ProtocolTranslationState
vertcreateRules isappprot goaltype pts =
  let (p@(_, types, knowledge, abstractions, actions, goals)) = protocol pts
      frMsg = fresh p
      pks = concatMap snd ((filter (\(x, y) -> x == PublicKey)) types)
      roles =
        ( snd
            . head
            . (filter (\x -> case (fst x) of Agent _ _ -> True; _ -> False))
        )
          types
   in pts {rules = vertmanageRules 0 frMsg (\x -> initialState (lookupL x knowledge)) actions pks (length actions) isappprot goaltype frMsg}

vertmanageRules step fresh states actions pks totalnrsteps isappprot goaltype firstfresh =
  --- about step number (=list index+1)
  --- initially 0: there is no incoming message
  --- finally (length actions): there is no outgoing message
  let ((a, ctin, b, min, minp, minzk), (b', ctout, c, mout, _, _)) =
        if step == (length actions)
          then (toJust (Just (last actions)), toJust Nothing)
          else
            if step == 0
              then (toJust Nothing, toJust (Just (head actions)))
              else
                ( toJust (Just (actions !! (step - 1))),
                  toJust (Just (actions !! step))
                )
      thisfresh = case mout of
        Nothing -> []
        Just (_, _, _, mout', _) ->
          intersect fresh (idents mout')
      freshpks = intersect pks thisfresh
      ub =
        if b == Nothing
          then
            if b' == Nothing
              then error ("Undefined Receiver in step" ++ (show step))
              else fromJust b'
          else
            if b' == Nothing
              then fromJust b
              else
                if b /= b'
                  then
                    error
                      ( "Receiver: "
                          ++ (show b)
                          ++ " and Sender/NextMsg is "
                          ++ (show b')
                      )
                  else fromJust b
      (rule, state') = vertcreateRule thisfresh freshpks ub (states ub) min mout step totalnrsteps isappprot goaltype firstfresh
   in rule
        : ( if step == (length actions)
              then []
              else
                vertmanageRules
                  (step + 1)
                  (fresh \\ thisfresh)
                  (\x -> if x == ub then state' else states x)
                  actions
                  pks
                  totalnrsteps
                  isappprot
                  goaltype
                  firstfresh
          )

vertcreateRule :: (Num p, Eq p) => [Ident] -> [Ident] -> Ident -> [LMsg] -> Maybe (Peer, ChannelType, Peer, Msg, Maybe Msg) -> Maybe (Peer, ChannelType, Peer, Msg, e) -> p -> p -> Bool -> GoalType -> [Ident] -> (([Fact], [a], [Ident], [Fact]), [LMsg])
vertcreateRule fresh freshpks role state incomin outgoin step totalnrsteps isappprot goaltype firstfresh =
  let (state1, msg1) =
        case incomin of
          Nothing -> (state, Atom "i")
          Just (sender, ct, receiver, recm, Nothing) ->
            let st = (receiveMsg recm state)
             in (state, chtrafo False sender ct receiver (snd (last st)))
          Just (sender, ct, receiver, recm, Just recmp) ->
            let st = (receiveLMsg (recm, recmp) state)
             in (state, chtrafo False sender ct receiver (snd (last st)))
      (state2, msg2) =
        case outgoin of
          Nothing -> (state1, Atom "i")
          Just (sender, ct, receiver, sndm, _) ->
            let state1' = peertrafo receiver msg1 state1
                st = sendMsgAnyway sndm (state1' ++ (map (\x -> (Atom x, Atom x)) fresh) ++ (map (\x -> (Comp Inv [Atom x], Comp Inv [Atom x])) freshpks))
             in (st, chtrafo True sender ct receiver (snd (last st)))
      getsenderreceiver coming =
        case coming of
          Just ((senderident, _, _), _, (receiverident, _, _), _, _) -> (senderident, receiverident)
          _ -> ("", "")
      senderreceiver = if msg2 == Atom "i" then getsenderreceiver incomin else getsenderreceiver outgoin
      setName
        | goaltype == Secc = "secCh"
        | goaltype == Auth = "authCh"
        | otherwise = error "This cannot happen!"
      gets = if step == totalnrsteps then snd else fst
      getc = if step == totalnrsteps then fst else snd
      getsetnamesender = if msg1 /= (Atom "i") && msg2 /= (Atom "i") then snd else fst
      getsetnamereceiver = if msg1 /= (Atom "i") && msg2 /= (Atom "i") then fst else snd

      firstfact = Fact "contains" [Comp Apply [Atom "counter", Atom "TUniqueVar"], Atom "globalcounter"]
      secondfact = Fact "contains" [Atom "TUniqueVar", Atom "globalcounter"]
      msgstruct msg getsender getreceiver = if isappprot then [Fact "contains" [msg, Comp Apply [Atom setName, Comp Cat [Atom (getsender senderreceiver), Atom (getreceiver senderreceiver)]]]] else [Iknows msg] -- is removed from app3b in ruleSplit later
      incommingmsg = if msg1 == (Atom "i") then [] else msgstruct msg1 getsetnamesender getsetnamereceiver
      outgoingmsg = if msg2 == (Atom "i") then [] else if step == 0 then msgstruct msg2 getsetnamesender getsetnamereceiver else msgstruct msg2 getsetnamereceiver getsetnamesender

      sentappfact = Fact "contains" [Atom (head firstfresh), Comp Apply [Atom "sent", Comp Cat [Atom (gets senderreceiver), Atom (getc senderreceiver)]]]
      sentchfact = Fact "TEMP" [Comp Cat [Atom (gets senderreceiver), Atom (getc senderreceiver)]]
      sentfact = if isappprot then sentappfact else sentchfact

      firstfactlist =
        if step == totalnrsteps
          then firstfact : sentfact : incommingmsg
          else firstfact : incommingmsg
      secondfactlist =
        if step == 0 || not isappprot
          then secondfact : sentfact : outgoingmsg
          else secondfact : outgoingmsg
   in ( ( ( State
              role
              ( ( (nubBy eqSnd)
                    -- . (\x -> (Atom "SID", Atom "SID") : (x ++ [(Atom "0", Atom "0")]))
                    . (\x -> (Atom role, Atom role) : (x ++ [(Atom "SID", Atom "SID")]))
                )
                  state1
              )
          )
            : (firstfactlist),
          [],
          fresh,
          ( State
              role
              ( ( (nubBy eqSnd)
                    -- . (\x -> (Atom "SID", Atom "SID") : (x ++ [(Atom "0", Atom "0")]))
                    . (\x -> (Atom role, Atom role) : (x ++ [(Atom "SID", Atom "SID")]))
                )
                  state1
              )
          )
            : (secondfactlist)
        ),
        state1
      )

sendMsgAnyway :: Msg -> ProtocolState -> ProtocolState
sendMsgAnyway msg state =
  case synthesisPattern state msg of
    Nothing -> state ++ [(msg, msg)] -- i have no idea what I'm doing
    Just p -> state ++ [(msg, p)]

isAgent (Agent _ _) = True
isAgent _ = False

gettype :: Types -> Ident -> Type
gettype types id =
  let typedec = map fst $ filter (elem id . snd) types
   in if (length typedec) == 0
        then error $ id ++ " has no declared type."
        else
          if (length typedec) > 1
            then error $ id ++ " has conflicting type declarations: " ++ (show typedec)
            else head typedec

---------- Channel Transformation ---------
-- {Nothing added to this section compared to in Translator.hs}

----- Translation Stage 2: add steps
------------------------------------

vertrulesAddSteps :: ProtocolTranslationState -> ProtocolTranslationState
vertrulesAddSteps pts =
  let counter inc (State role (player : ids)) (facts, db) =
        ( (State role (player : (((\x -> (x, x)) . Atom . show) (db role)) : ids)) : facts,
          \x -> if x == role then (db role) else db x
        )
      counter inc fact (facts, db) = (fact : facts, db)
      adds [] db = []
      adds ((l, [], f, r) : xs) db =
        let (l', db') = foldr (counter 1) ([], db) l
            (r', db'') = foldr (counter 0) ([], db') r
         in (l', [], f, r') : (adds xs db'')
   in pts {rules = adds (rules pts) (\x -> 0)}

--- Stage 4: Adding the initial state
-------------------------------------

vertaddInit :: Bool -> GoalType -> Int -> ProtocolTranslationState -> ProtocolTranslationState
vertaddInit isappprot goaltype maxDep pts =
  let (_, typdec, knowledge, _, _, _) = protocol pts
      args = options pts
      absInit = getinitials (rules pts) knowledge
      jn = numSess args
      n :: Int
      n =
        if (jn == Nothing)
          then error "Unbounded sessions currently not supported."
          else fromJust jn
      (_, ineq) = knowledge
      (facts0, honest, aglili, agents0, ik0, ineq') = instantiate n absInit ineq
      facts =
        facts0
          ++ ik0
          ++ (getCrypto agents0)
      agents = ((++) ["i", "A", "B"]) agents0

      setName
        | goaltype == Secc = "secCh"
        | goaltype == Auth = "authCh"
        | otherwise = error "This cannot happen!"

      addedtypes =
        if isappprot
          then vertprintTypes [(Function, ["sent", setName])]
          else
            ( if goaltype == Secc
                then vertprintTypes [(Set, ["opened", "closed"])]
                else vertprintTypes [(Set, ["opened"])]
            )
              ++ vertprintTypes [(Function, [setName])]
      addedcounter = createGlobalCounter maxDep "counter"
      addeddummy = "state_dummy(dummy,1,0).\n"
   in pts
        { initial =
            ( if typed args
                then
                  ( "section types:\n"
                      ++ (ppIdList agents)
                      ++ ":agent\n"
                      ++ (vertprintTypes typdec)
                      ++ addedtypes
                      ++ (vertprintTypes [(Function, ["counter"])])
                      ++ (vertprintTypes [(Set, ["globalcounter"])])
                      ++ "\n"
                  )
                else ""
            )
              ++ "section inits:\n"
              ++ " initial_state init1 :=\n"
              ++ addedcounter
              ++ addeddummy
              ++ (vertppFactListBetter IF facts)
              ++ (concatMap (\x -> " & " ++ (ppId x) ++ "/=i") honest)
              ++
              ---    (concatMap (\ (x,y) -> " & "++(ppId x)++"/="++(ppId y)) [(x,y) | x<-agents0, y<-agents0, x/=y])++
              ---    (error $ (show aglili) ++ (show (concatMap (\ (x,y) -> " & "++(ppId x)++"/="++(ppId y)) [(x,y) | l<-aglili, x<-l, y<-l, x/=y])))++
              (concatMap (\(s, t) -> " & " ++ (ppMsg IF s) ++ "/=" ++ (ppMsg IF t)) ineq')
              ++ "\n\n"
              ++ "section rules:\n"
        }

createCounter len countername countersetname =
  let applyRecursion len countername =
        case compare len 0 of
          GT -> "apply(" ++ countername ++ "," ++ applyRecursion (len - 1) countername ++ ")"
          _ -> "0"
   in "contains(" ++ applyRecursion len countername ++ "," ++ countersetname ++ ").\n"

createGlobalCounter len funcname = createCounter len funcname "globalcounter"

vertprintTypes :: Types -> String
vertprintTypes =
  let f (Agent _ _, ids) = (ppIdList ids) ++ ":agent\n"
      f (Number, ids) = (ppIdList ids) ++ ":text\n"
      f (SeqNumber, _) = ""
      f (PublicKey, ids) = (ppIdList ids) ++ ":public_key\n"
      f (SymmetricKey, ids) = (ppIdList ids) ++ ":symmetric_key\n"
      f (Function, ids) = (ppIdList ids) ++ ":function\n"
      -------Differs from Translator.hs-------
      f (Set, ids) = (ppIdList ids) ++ ":set\n"
      f (Payload, ids) = (ppIdList ids) ++ ":payload\n"
      ----------------------------------------
      f (Custom x, ids) = (ppIdList ids) ++ ":t_" ++ x ++ "\n"
      f (Untyped, _) = ""
      f (Format, ids) = (ppIdList ids) ++ ":text" ++ "\n"
   in concatMap f

--- Stage 5: printing the rules
--------------------------------

-- <paolo>
vertppRule outf (l, [], f, r) =
  (vertppFactListBetter outf l) -- usage of ppFactListBetter instead of ppFactList
    ++ "\n"
    ++ (if f == [] then "=>" else "=[exists " ++ (ppIdList f) ++ "]=>")
    ++ "\n"
    ++ (vertppFactListBetter outf r) -- usage of ppFactListBetter instead of ppFactList
    -- ++ "\n"

vertruleList :: Bool -> Bool -> GoalType -> ProtocolTranslationState -> String
vertruleList if2cif isappprot goaltype pts =
  -- pass the list of SQNs
  vertruleListIF (initial pts, rules pts, goals pts) (trTypes2Ids (getTypes (protocol pts)) SeqNumber) if2cif isappprot goaltype

vertruleListIF :: (String, [Rule], String) -> [Ident] -> Bool -> Bool -> GoalType -> String
vertruleListIF (init, rules, goals) sqns if2cif isappprot goaltype =
  let ruleIF [] _ _ = ""
      ruleIF (x : xs) (n, name) lastrulenr =
        let -- rule hacked SQN
            nr1 = ppRuleIFHack x sqns
            -- IF2CIF
            nr2 = if if2cif then ppRuleIF2CIF nr1 else nr1
            nextnrnm 0 "a" = if isappprot then (1, "b") else if goaltype == Secc then (1, "a") else (2, "auth")
            nextnrnm nr nm = if isappprot then ((nr + 1), "") else if (not isappprot && goaltype == Auth) then ((nr + 1), "auth") else if nm == "a" then (nr, "b") else ((nr + 1), "a")
            appliednr2 = vertppRule IF nr2
            stepname = if isappprot then if n == 0 || n == 1 then "i" else "app" else "ch"
            rulenr = if isappprot then if n == 0 || n == 1 then n + 5 else n + 1 else if n == 0 then -1 else if n == 1 then lastrulenr else n + 1
            authaddendum = if goaltype == Auth && stepname == "i" && rulenr == 5 then "3" else ""
            namenr = if rulenr == -1 then "chnew" else if isappprot then stepname ++ authaddendum ++ (show rulenr) else stepname ++ (show rulenr) ++ (name)
            stepandnamenr = "step " ++ namenr
            iknowspart = if (isappprot && n /= 0) || (rulenr == -1 && goaltype == Secc) then ".\niknows(" ++ namenr ++ ")\n\n" else "\n\n"
         in stepandnamenr ++ ":=\n" ++ appliednr2 ++ iknowspart ++ (ruleIF xs (nextnrnm n name) lastrulenr)
   in init ++ (ruleIF (ruleSplit rules isappprot goaltype) (0, "a") (getlastrulenr rules)) ++ "\n" ++ goals

getlastrulenr rules = length rules + 3 -- OBS: is this legal?

replaceatommsg :: String -> String -> Msg -> Msg
replaceatommsg ident replacement msg =
  case msg of
    Atom x -> (if x == ident then Atom replacement else Atom x)
    Comp op ms -> Comp op (replaceatommsglist ident replacement ms)

replaceatommsglist :: String -> String -> [Msg] -> [Msg]
replaceatommsglist ident replacement [] = []
replaceatommsglist ident replacement (msg : msgs) = replaceatommsg ident replacement msg : replaceatommsglist ident replacement msgs

replaceatomlmsglist :: String -> String -> [LMsg] -> [LMsg]
replaceatomlmsglist ident replacement [] = []
replaceatomlmsglist ident replacement ((m1, m2) : lmsgs) = (replaceatommsg ident replacement m1, replaceatommsg ident replacement m2) : replaceatomlmsglist ident replacement lmsgs

replaceatomfact :: String -> String -> Fact -> Fact
replaceatomfact ident replacement fact =
  case fact of
    State statename lmsgs -> State statename (replaceatomlmsglist ident replacement lmsgs)
    FPState _ _ -> error "ruleSplit: The --vert flag is not made for use with FP format!"
    Iknows msg -> Iknows (replaceatommsg ident replacement msg)
    Fact factident msgs -> Fact factident (replaceatommsglist ident replacement msgs)

replaceatomfactlist :: String -> String -> [Fact] -> [Fact]
replaceatomfactlist ident replacement [] = []
-- replaceatomfactlist ident replacement (fact : facts) | trace ("replaceatomfactlist " ++ ident ++ " " ++ replacement ++ "\n" ++ (show fact)) False = undefined
replaceatomfactlist ident replacement (fact : facts) = replaceatomfact ident replacement fact : replaceatomfactlist ident replacement facts

ruleSplit :: [Rule] -> Bool -> GoalType -> [Rule]
-- ruleSplit rules | trace ("ruleSplit\n" ++ show (last ((\(l,_,_,_) -> l) (head rules)))) False = undefined
ruleSplit rules False goaltype =
  -- ch
  let (l, eq, eqid, r) = head rules
      ch3a = (l1, eq, [], r1)
      payloadident = head eqid
      append a [] = [a]
      append a (x : xs) = x : append a xs
      l1 = append (Fact "contains" [Atom payloadident, Atom "opened"]) l
      l2 = append (Fact "contains" [Atom payloadident, Atom "closed"]) l
      lastelem [] = error "ruleSplit: cannot use internal function 'lastelem' on empty list!"
      lastelem (elem : []) = elem
      lastelem (x : xs) = lastelem xs
      getabfromfacts [] = error ("ruleSplit failed! Guess I'm an idiot :c lastelem = ")
      getabfromfacts (fact : facts) =
        case fact of
          Fact "TEMP" [Comp Cat [Atom a, Atom b]] -> (a, b)
          _ -> getabfromfacts facts
      ab = getabfromfacts r

      replacetemp [] _ = error "ruleSplit: cannot use internal function 'replacetemp' on empty list!"
      replacetemp (x : xs) [e1, e2] = case x of
        Fact "TEMP" _ -> e1 : e2 : xs
        _ -> x : replacetemp xs [e1, e2]
      replacetemp _ _ = error "ruleSplit: cannot use internal function 'replacetemp' with elem list of length other than 2!"

      setName
        | goaltype == Secc = "secCh"
        | goaltype == Auth = "authCh"
        | otherwise = error "This cannot happen!"

      setnamefact = Fact "contains" [Atom payloadident, Comp Apply [Atom setName, Comp Cat [Atom (fst ab), Atom (snd ab)]]]
      chopenedpart = [Fact "contains" [Atom payloadident, Atom "opened"], setnamefact]
      chclosedpart = [Fact "contains" [Atom payloadident, Atom "closed"], setnamefact]
      r1 = replacetemp r chopenedpart
      r2 = replacetemp r chclosedpart
      ch3b = (l2, eq, [], r2)

      (l', eq', equid', r') = head (tail rules)
      iknowspart = lastelem l'
      l3 = replacetemp l' chopenedpart
      l4 = replacetemp l' chclosedpart
      r'' = append iknowspart r'
      r3 = replacetemp r'' chopenedpart
      r4 = replacetemp r'' chclosedpart
      ch4a = (l3, eq', equid', r3)
      ch4b = (l4, eq', equid', r4)

      dummy_state = State "dummy" [(Atom "dummy", Atom "dummy"), (Atom "0", Atom "0"), (Atom "SID", Atom "SID")]
      firstfact = Fact "contains" [Comp Apply [Atom "counter", Atom "TUniqueVar"], Atom "globalcounter"]
      secondfact = Fact "contains" [Atom "TUniqueVar", Atom "globalcounter"]
      openedpart = Fact "contains" [Atom payloadident, Atom "opened"]
      closedpart = Fact "contains" [Atom payloadident, Atom "closed"]
      iknowspayload = Iknows (Atom payloadident)

      chnew = ([dummy_state, firstfact], [], [payloadident], [dummy_state, secondfact, closedpart])
      ch5a = ([dummy_state, firstfact, openedpart], [], [], [dummy_state, secondfact, openedpart, iknowspayload])
      ch5b = ([dummy_state, firstfact, closedpart], [], [], [dummy_state, secondfact, openedpart, iknowspayload])

      chauthnew = ([dummy_state, firstfact], [], [payloadident], [dummy_state, secondfact, openedpart, iknowspayload])
      chauth3 = ch3a
      chauth4 = (l3, eq', equid', replacetemp r' chopenedpart)
   in if goaltype == Secc then [chnew, ch5a, ch5b, ch3a, ch3b, ch4a, ch4b] else [chauthnew, chauth3, chauth4]
ruleSplit rules True goaltype =
  -- app
  let app3 = head rules
      (l, eq, eqid, r) = head (tail rules)
      (l2, eq2, eqid2, r2) = head (tail (tail rules))
      lastelem [] = error "ruleSplit: cannot use internal function 'lastelem' on empty list!"
      lastelem (elem : []) = elem
      lastelem (x : xs) = lastelem xs
      keepinsetname = lastelem l
      macscrtapply = lastelem r

      append a [] = [a]
      append a (x : xs) = x : append a xs
      r' = append keepinsetname r
      app4 = (l, eq, eqid, r')

      removelastelem [] = error "ruleSplit: cannot use internal function 'removelastelem' on empty list!"
      removelastelem [_] = []
      removelastelem (x : xs) = x : removelastelem xs
      replacelastelem elem listt = append elem (removelastelem listt)
      l2' = replacelastelem macscrtapply l2
      r2' = append macscrtapply r2
      app5 = (l2', eq2, eqid2, r2')

      dummy_state = State "dummy" [(Atom "dummy", Atom "dummy"), (Atom "0", Atom "0"), (Atom "SID", Atom "SID")]
      firstfact = Fact "contains" [Comp Apply [Atom "counter", Atom "TUniqueVar"], Atom "globalcounter"]
      secondfact = Fact "contains" [Atom "TUniqueVar", Atom "globalcounter"]

      setName
        | goaltype == Secc = "secCh"
        | goaltype == Auth = "authCh"
        | otherwise = error "This cannot happen!"

      setnamepart frst sndd = Fact "contains" [Atom "Xxx", Comp Apply [Atom setName, Comp Cat [Atom frst, Atom sndd]]]
      i5setnamepart = if goaltype == Secc then setnamepart "Yyy" "i" else setnamepart "Yyy" "Zzz"
      i6setnamepart = setnamepart "i" "Yyy"
      iknowspart = Iknows (Atom "Xxx")

      i5 = ([dummy_state, firstfact, i5setnamepart], [], [], [dummy_state, secondfact, i5setnamepart, iknowspart])
      i6 = ([dummy_state, firstfact, iknowspart], [], [], [dummy_state, secondfact, i6setnamepart])
   in [i5, i6, app3, app4, app5]

-------------------------------------
vertendstr :: Bool -> String
vertendstr noowngoal =
  "section attack_states:\n"
    ++ "  attack_state temp :=\n"
    ++ "    secret(AnB_M,AnB_A).\n"
    ++ "    iknows(AnB_M)\n"

vertppFactListBetter outf =
  let firstelem [] = error "vertppFactListBetter: cannot use internal function 'firstelem' on empty list!"
      firstelem (x : _) = x
      ppXListBetter :: (Fact -> String) -> String -> [Fact] -> String
      ppXListBetter ppX sp (fact1 : []) = case fact1 of
        Fact "&" _ ->
          let updatedsp = if sp == "" then "" else "\n"
           in updatedsp ++ ppX fact1
        _ -> sp ++ ppX fact1
      ppXListBetter ppX sp (fact1 : facts) = case fact1 of
        Fact "&" _ ->
          let updatedsp = if sp == "" then "" else "\n"
           in updatedsp ++ ppX fact1 ++ ppX fact1 ++ ppXListBetter ppX ".\n" facts
        _ -> sp ++ ppX fact1 ++ ppXListBetter ppX ".\n" facts
   in (ppXListBetter (ppFact outf) "") . (filter isntIknowsFunction)

vertmakegoals :: Bool -> GoalType -> ProtocolTranslationState -> ProtocolTranslationState
-- vertmakegoals isappprot pts | trace ("vertmakegoals\n" ++ (show (ruleSplit (rules pts) isappprot))) False = undefined
vertmakegoals False goaltype pts =
  -- ch
  let lasttwoelems [] = error "vertmakegoals: cannot use internal function 'lasttwoelems' on empty list!"
      lasttwoelems [_] = error "vertmakegoals: cannot use internal function 'lasttwoelems' on list with only one element!"
      lasttwoelems [x1, x2] = [x1, x2]
      lasttwoelems (x : xs) = lasttwoelems xs

      vertrules = ruleSplit (rules pts) False goaltype
      chgoalrules = lasttwoelems vertrules

      getfactlist :: [Rule] -> [[Fact]]
      getfactlist [] = []
      getfactlist [(_, _, _, r)] = [r]
      getfactlist ((_, _, _, r) : rs) = r : getfactlist rs
      chgoalfacts = getfactlist chgoalrules

      removesndelem listt = head listt : tail (tail listt)
      chgoalnoglobalcounter = map removesndelem chgoalfacts

      setName
        | goaltype == Secc = "secCh"
        | goaltype == Auth = "authCh"
        | otherwise = error "This cannot happen!"

      applynot :: String -> Fact -> String
      applynot output fact =
        let trueoutput = (if output == "" then "" else output ++ ".\n")
         in case fact of
              Fact "contains" [Atom _, Comp Apply [Atom setName, _]] -> trueoutput ++ "    not(" ++ vertppFactListBetter IF [fact] ++ ")"
              f -> trueoutput ++ "    " ++ vertppFactListBetter IF [fact]

      attacknr = getlastrulenr (rules pts) + 2
      chgoal1 = "  attack_state ch" ++ (show attacknr) ++ (if goaltype == Secc then "a:=\n" else "auth:=\n") ++ foldl applynot "" (head chgoalnoglobalcounter) ++ "\n\n"
      chgoal2 = "  attack_state ch" ++ (show attacknr) ++ "b:=\n" ++ foldl applynot "" (head (tail chgoalnoglobalcounter)) ++ "\n\n"

      sndfacttogoalbody facts =
        let sndfact = head (tail facts)
            getpayloadatom fact =
              case fact of
                Fact "contains" [Atom x, _] -> x
                _ -> error "vertmakegoals: Local function 'getpayloadatom' --- This error should not be possible!"
            payloadident = getpayloadatom sndfact
         in "    " ++ vertppFactListBetter IF [sndfact] ++ " &\n    iknows(" ++ payloadident ++ ")"

      chgoal3 = "  attack_state closed_leak:=\n" ++ sndfacttogoalbody (head (tail chgoalnoglobalcounter))
      output = if goaltype == Secc then "section attack_states:\n" ++ chgoal1 ++ chgoal2 ++ chgoal3 else "section attack_states:\n" ++ chgoal1
   in pts {goals = output}
vertmakegoals True goaltype pts =
  -- app
  let (l, eq, eqid, r) = head (rules pts)
      thirdelem listt = head (tail (tail listt))
      getscfromfact fact =
        case fact of
          Fact "contains" [Atom n, Comp Apply [Atom "sent", Comp Cat [Atom s, Atom c]]] -> (s, c)
          _ -> error ("ruleSplit failed! Guess I'm an idiot :c lastelem = " ++ show (fact))
      sc = getscfromfact (thirdelem r)
      lastelem [] = error "vertmakegoals: cannot use internal function 'lastelem' on empty list!"
      lastelem (elem : []) = elem
      lastelem (x : xs) = lastelem xs

      vertrules = ruleSplit (rules pts) True goaltype
      appgoalrules = lastelem vertrules

      removesnd listt = head listt : tail (tail listt)

      getfactlist :: Rule -> [Fact]
      getfactlist (l, _, _, _) = l

      replacewithi [] = []
      replacewithi (fact : facts) =
        case fact of
          Fact "contains" [Comp Cat x, msg] -> Fact "contains" [Comp Cat x, replaceatommsg (snd sc) "i" msg] : replacewithi facts
          f -> replaceatomfact (snd sc) "i" f : replacewithi facts

      append a [] = [a]
      append a (x : xs) = x : append a xs

      appgoalfacts = append (Fact "&" [Comp Neq [Atom (snd sc), Atom "i"]]) (replacewithi (removesnd (getfactlist appgoalrules)))
      attacknr = getlastrulenr (rules pts)

      addspacing :: [String] -> [String]
      addspacing [] = []
      addspacing (x : xs) = ("    " ++ x) : addspacing xs
      relinklist [] = []
      relinklist (x : xs) = x ++ "\n" ++ relinklist xs

      appgoal = "  attack_state app" ++ (show attacknr) ++ ":=\n" ++ relinklist (addspacing (lines (vertppFactListBetter IF (appgoalfacts))))
   in pts {goals = "section attack_states:\n" ++ appgoal}
