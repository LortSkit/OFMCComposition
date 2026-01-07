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

-- | AppIncompatible
data ComposableResult = Composable | TypeflawSucceptible | AbstractChIncompatible | InvalidPayloadAsKeyUsage
  deriving
    ( Eq,
      Show
    )

trycompose :: Protocol -> Protocol -> AnBOptsAndPars -> (ComposableResult, [String], [String], [String], [String])
-- trycompose protocol1@(_, typdec1, knowledge1, _, actions1, goals1) protocol2@(_, typdec2, knowledge2, _, actions2, goals2) args | trace ("stuff1: " ++ show (getBasePubSec typdec1 knowledge1) ++ "\nstuff2: " ++ show (getBasePubSec typdec2 knowledge2)) False = undefined
trycompose protocol1@(_, typdec1, knowledge1, _, actions1, goals1) protocol2@(_, typdec2, knowledge2, _, actions2, goals2) args =
  let stuff1 = getBasePubSec typdec1 knowledge1
      stuff2 = getBasePubSec typdec2 knowledge2
      (pub, sec) = getFinalPubSec stuff1 stuff2 (actions1, actions2)
      (chmsg3, compterms, compsetops, (gsmpappterms, gsmpappsetops), (gsmpabstractchterms, gsmpabstractchsetops)) = getProtocolTermsSetops (actions1, actions2) (goals1, goals2) (typdec1, typdec2)
      (typeflawresresult, typeflawfaults) = typeflawresistancecheck (actions1, actions2) (goals1, goals2) (typdec1, typdec2) compterms
      msgtupletostringforfaults (x, y) = "{" ++ getStringFromMsg x ++ "; " ++ getStringFromMsg y ++ "}"
      finalsec = sec ++ map getStringFromMsg compterms ++ map msgtupletostring compsetops

      nowrongoverlap = noWrongOverlap (isAppProtocol actions1) (typdec1, typdec2)
      noErrors = not (allErrors protocol1 protocol2) && nowrongoverlap

      -- apprequirementresult = gsmpAppSubseteqSecUnionPub (gsmpappterms, gsmpappsetops) (pub, finalsec) -- since we build sec from the app messages, this cannot trigger?
      (abstractpayloadrequirementresult, payloadfaults) = gsmpAbstractChIntersectionAppSubseteqPub (gsmpappterms, gsmpappsetops) (gsmpabstractchterms, gsmpabstractchsetops) pub
      (channelkeyrequirementresult, keyfaults) = noKeyHasAppLabel chmsg3 gsmpappterms -- I don't think this can trigger either, but leaving it in for now
      result
        | not typeflawresresult = TypeflawSucceptible
        -- \| not apprequirementresult = AppIncompatible
        | not abstractpayloadrequirementresult = AbstractChIncompatible
        | not channelkeyrequirementresult = InvalidPayloadAsKeyUsage
        | otherwise = Composable

      finalgsmpappterms = map getStringFromMsg gsmpappterms

      finalfaults
        | not typeflawresresult = map msgtupletostringforfaults typeflawfaults
        | not abstractpayloadrequirementresult = payloadfaults
        | not channelkeyrequirementresult = map getStringFromMsg keyfaults
        | otherwise = []
   in if noErrors
        then (result, pub, finalsec, finalfaults, finalgsmpappterms)
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

msgtupletostring :: (Msg, Msg) -> [Char]
msgtupletostring (x, y) = "(" ++ getStringFromMsg x ++ "," ++ getStringFromMsg y ++ ")"

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
        let -- cryptScryptcase op keystring innermsg | trace ("keystuff: " ++ show (getMsgSubterms innermsg) ++ "keymsg: " ++ keystring ++ show (innermsg)) False = undefined
            cryptScryptcase op keystring innermsg =
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
                         in cryptScryptcase op keystring (Comp Cat (innermsg : keyinputs))
                      Comp Inv [Comp Apply (keyname : keyinputs)] ->
                        let keystring = getfuncString keyname keyinputs
                         in cryptScryptcase op keystring (Comp Cat (innermsg : keyinputs))
              _ -> error ("Internal function 'getMsgSubterms' got an unexpected composed message! " ++ show msg)

      actionToMsg :: Action -> Msg
      actionToMsg (((sender, _, _), _, (receiver, _, _)), msg, _, _) = msg

      getActionsSubterms :: Actions -> ([String], [String], String)
      -- getActionsSubterms actions | trace ("msgs: " ++ show (map actionToMsg actions) ++ "\npubseclist: " ++ show (map getMsgSubterms (map actionToMsg actions))) False = undefined
      getActionsSubterms [] = ([], [], "")
      getActionsSubterms actions =
        let msgs = map actionToMsg actions
            pubseclist = map getMsgSubterms msgs
            (pub, sec, _) = combinepubsec pubseclist
         in (pub, sec, "")
      (opub1, osec1, _) = getActionsSubterms actions1
      (opub2, osec2, _) = getActionsSubterms actions2
   in (removeDuplicates (opub1 ++ opub2), removeDuplicates (osec1 ++ osec2))

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
-- getNFromTypes ((typ, idents) : resttypes) | trace ("???" ++ show (typ, idents)) False = undefined
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

haslistOverlapTypeMismatchElem :: [(Ident, Type)] -> (Ident, Type) -> Bool
haslistOverlapTypeMismatchElem addedIdents (id, typ) =
  let justIdents = map fst addedIdents
   in id `elem` justIdents && not ((id, typ) `elem` addedIdents)

haslistOverlapTypeMismatch :: [Ident] -> Type -> [(Ident, Type)] -> Bool
haslistOverlapTypeMismatch ids typ addedIdents =
  let idtyplist = map (\id -> (id, typ)) ids
      faults = filter (haslistOverlapTypeMismatchElem addedIdents) idtyplist
   in length faults > 0

getIdTypeList :: Bool -> (Types, Types) -> [(Ident, Type)] -> [(Ident, Type)]
getIdTypeList firstIsApp ([], []) addedIdents = []
getIdTypeList firstIsApp ([], (typ, ids) : resttypes) addedIdents
  | haslistOverlapTypeMismatch ids typ addedIdents = error "App protocol and Ch protocol share variable names that have a mismatch in type!"
  | not firstIsApp && typ == Payload = map (\id -> (id, Custom "_AppPayload")) ids ++ getIdTypeList firstIsApp ([], resttypes) (addedIdents ++ (map (\id -> (id, typ)) ids))
  | otherwise = map (\id -> (id, typ)) ids ++ getIdTypeList firstIsApp ([], resttypes) (addedIdents ++ (map (\id -> (id, typ)) ids))
getIdTypeList firstIsApp ((typ, ids) : resttypes, types2) addedIdents
  | haslistOverlapTypeMismatch ids typ addedIdents = error "App protocol and Ch protocol share variable names that have a mismatch in type!"
  | firstIsApp && typ == Payload = map (\id -> (id, Custom "_AppPayload")) ids ++ getIdTypeList firstIsApp (resttypes, types2) (addedIdents ++ (map (\id -> (id, typ)) ids))
  | otherwise = map (\id -> (id, typ)) ids ++ getIdTypeList firstIsApp (resttypes, types2) (addedIdents ++ (map (\id -> (id, typ)) ids))

tryEasyLookup :: Bool -> (Types, Types) -> Ident -> Maybe Type
tryEasyLookup firstIsApp (types1, types2) id =
  let idTypeList = getIdTypeList firstIsApp (types1, types2) []
      tryLookup :: [(Ident, Type)] -> Ident -> Maybe Type -> Maybe Type
      tryLookup [] _ result = result
      tryLookup ((mid, typ) : rest) id result = if id == mid then tryLookup rest id (Just typ) else tryLookup rest id result -- trying to make sure no lazy eval
   in if id == "i" then Just (Agent False False) else tryLookup idTypeList id Nothing

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

getsubtermsofmsg :: (Msg -> Bool) -> Msg -> [Msg]
getsubtermsofmsg hasUndesireable msg =
  let cryptScryptcase msg msgs = case msgs of
        [key, encrypted] -> case key of
          Comp Inv _ ->
            if isCat key
              then error "Unexpected key structure!"
              else
                if isAtom key
                  then
                    if hasUndesireable encrypted
                      then msg : getsubtermsofmsg hasUndesireable key ++ getsubtermsofmsg hasUndesireable encrypted
                      else msg : encrypted : getsubtermsofmsg hasUndesireable key ++ getsubtermsofmsg hasUndesireable encrypted
                  else
                    if hasUndesireable encrypted
                      then msg : key : getsubtermsofmsg hasUndesireable key ++ getsubtermsofmsg hasUndesireable encrypted
                      else msg : key : encrypted : getsubtermsofmsg hasUndesireable key ++ getsubtermsofmsg hasUndesireable encrypted
          _ ->
            if isCat key
              then error "Unexpected key structure!"
              else
                if isAtom key
                  then
                    if hasUndesireable encrypted
                      then msg : Comp Inv [key] : getsubtermsofmsg hasUndesireable key ++ getsubtermsofmsg hasUndesireable encrypted
                      else msg : Comp Inv [key] : encrypted : getsubtermsofmsg hasUndesireable key ++ getsubtermsofmsg hasUndesireable encrypted
                  else
                    if hasUndesireable encrypted
                      then msg : Comp Inv [key] : key : getsubtermsofmsg hasUndesireable key ++ getsubtermsofmsg hasUndesireable encrypted
                      else msg : Comp Inv [key] : key : encrypted : getsubtermsofmsg hasUndesireable key ++ getsubtermsofmsg hasUndesireable encrypted
        _ -> error "Unexpected structure encountered!"
      invExpXorcase op msgs =
        if length msgs /= 1
          then error ("Unexpected " ++ show op ++ "structure encountered!")
          else getsubtermsofmsg hasUndesireable (head msgs)
   in case msg of
        Atom _ -> []
        Comp op msgs ->
          case op of
            Crypt -> cryptScryptcase msg msgs
            Scrypt -> cryptScryptcase msg msgs
            Cat -> case msgs of
              [Comp Cat _, _] -> error "Unexpected concatenation structure encountered!"
              [elem, Comp Cat nextmsgs] ->
                if hasUndesireable elem
                  then getsubtermsofmsg hasUndesireable elem ++ getsubtermsofmsg hasUndesireable (Comp Cat nextmsgs)
                  else elem : getsubtermsofmsg hasUndesireable elem ++ getsubtermsofmsg hasUndesireable (Comp Cat nextmsgs)
              [elem1, elem2] ->
                if hasUndesireable elem1 && hasUndesireable elem2
                  then getsubtermsofmsg hasUndesireable elem1 ++ getsubtermsofmsg hasUndesireable elem2
                  else
                    if hasUndesireable elem1
                      then elem2 : getsubtermsofmsg hasUndesireable elem1 ++ getsubtermsofmsg hasUndesireable elem2
                      else
                        if hasUndesireable elem2
                          then elem1 : getsubtermsofmsg hasUndesireable elem1 ++ getsubtermsofmsg hasUndesireable elem2
                          else elem1 : elem2 : getsubtermsofmsg hasUndesireable elem1 ++ getsubtermsofmsg hasUndesireable elem2
              l ->
                if length l >= 3 && noCats l
                  then filter (not . hasUndesireable) l ++ concat (map (getsubtermsofmsg hasUndesireable) l)
                  else error ("Expected concatenation, instead got " ++ show msg)
            op | op `elem` [Inv, Exp, Xor] -> invExpXorcase op msgs
            Apply ->
              if length msgs /= 2
                then error "Unexpected function structure encountered!"
                else getsubtermsofmsg hasUndesireable (head (tail msgs))
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

getmessages :: Bool -> (Actions, Actions) -> (Msg, Msg, Msg)
getmessages firstIsApp (actions1, actions2) =
  let appmsg1 = getMsgFromAction (if firstIsApp then head actions1 else head actions2)
      appmsg2 = getMsgFromAction (if firstIsApp then head (tail actions1) else head (tail actions2))
      chmsg3 = getMsgFromAction (if firstIsApp then head actions2 else head actions1)
   in (appmsg1, appmsg2, chmsg3)

getMsgAndSubtermsNotAtoms :: Msg -> [Msg]
getMsgAndSubtermsNotAtoms msg =
  if hasUndesirableMsgStructure msg
    then removeDuplicates (getsubtermsofmsg hasUndesirableMsgStructure msg)
    else removeDuplicates (msg : getsubtermsofmsg hasUndesirableMsgStructure msg)

getMsgAndSubtermsWithAtoms :: Msg -> [Msg]
getMsgAndSubtermsWithAtoms msg =
  if isCat msg
    then removeDuplicates (getsubtermsofmsg isCat msg)
    else removeDuplicates (msg : getsubtermsofmsg isCat msg)

getProtocolTermsSetops :: (Actions, Actions) -> (Goals, Goals) -> (Types, Types) -> (Msg, [Msg], [(Msg, Msg)], ([Msg], [(Msg, Msg)]), ([Msg], [(Msg, Msg)]))
getProtocolTermsSetops (actions1, actions2) (goals1, goals2) (types1, types2) =
  let firstIsApp = isAppProtocol actions1
      chgoaltype = if firstIsApp then getGoalType goals2 else getGoalType goals1
      -----------------------------DEFINED IN ANB------------------------------
      appprotN = getNFromTypes (if firstIsApp then types1 else types2)
      (appprotC, appprotS) = getCSFromActions (if firstIsApp then actions1 else actions2)
      chprotX = getXFromTypes (if firstIsApp then types2 else types1)
      (chprotA, chprotB) = getABFromActions (if firstIsApp then actions2 else actions1)
      chprotSet = if chgoaltype == Secc then Atom "secCh" else Atom "authCh"
      (appmsg1, appmsg2, chmsg3) = getmessages firstIsApp (actions1, actions2)
      --------------------------FROM FORMAL PROTOCOLS--------------------------
      appproti = Atom "i"
      applyoutbox agent1 agent2 = Comp Apply [Atom "outbox", Comp Cat [agent1, agent2]]
      applyinbox agent1 agent2 = Comp Apply [Atom "inbox", Comp Cat [agent1, agent2]]
      applysent agent1 agent2 = Comp Apply [Atom "sent", Comp Cat [agent1, agent2]]
      applychprotSet agent1 agent2 = Comp Apply [chprotSet, Comp Cat [agent1, agent2]]
      compterms =
        -- SMP(App)\V U SMP(Ch)\V
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
        -- setops(App) U setops(Ch)
        [ (appprotN, applysent appprotS appprotC), -- N->sent(S,C) && N<-sent(S,C)
          (appmsg1, applyoutbox appprotS appprotC), -- [m1]->outbox(S,C)
          (appmsg1, applyinbox appprotS appprotC), -- [m1]<-inbox(S,C)
          (appmsg2, applyoutbox appprotC appprotS), -- [m2]->outbox(C,S)
          (appmsg2, applyinbox appprotC appprotS), -- [m2]<-inbox(C,S)
          (appmsg2, applyinbox appproti appprotS), -- [m2]<-inbox(i,S)
          (appprotN, applysent appprotS appproti), -- N \in sent(S,i)
          (chprotX, applyoutbox chprotA chprotB), -- X<-outbox(A,B)
          (chprotX, applychprotSet chprotA chprotB), -- X->secCh(A,B) && X \in secCh(A,B) && X \notin secCh(A,B) [OR authCh -||-]
          (chprotX, applyinbox chprotA chprotB) -- x->inbox(A,B)
        ]
      gsmpappterms =
        removeDuplicates
          ( [ appprotN, -- N
              appprotS, -- S
              appprotC, -- C
              applysent appprotS appprotC, -- sent(S,C)
              applyoutbox appprotS appprotC, -- outbox(S,C)
              applyinbox appprotS appprotC, -- inbox(S,C)
              applyoutbox appprotC appprotS, -- outbox(C,S)
              applyinbox appprotC appprotS, -- inbox(C,S)
              applyinbox appproti appprotS, -- inbox(i,S)
              applysent appprotS appproti -- sent(S,i)
            ]
              ++ (getMsgAndSubtermsWithAtoms appmsg1 ++ getMsgAndSubtermsWithAtoms appmsg2)
          )
      gsmpappsetops =
        [ (appprotN, applysent appprotS appprotC), -- N->sent(S,C) && N<-sent(S,C)
          (appmsg1, applyoutbox appprotS appprotC), -- [m1]->outbox(S,C)
          (appmsg1, applyinbox appprotS appprotC), -- [m1]<-inbox(S,C)
          (appmsg2, applyoutbox appprotC appprotS), -- [m2]->outbox(C,S)
          (appmsg2, applyinbox appprotC appprotS), -- [m2]<-inbox(C,S)
          (appmsg2, applyinbox appproti appprotS), -- [m2]<-inbox(i,S)
          (appprotN, applysent appprotS appproti) -- N \in sent(S,i)
        ]
      gsmpabstractchterms =
        removeDuplicates
          ( [ Atom "TEMP", -- This is abstract payload G of type \mathfrak{a}. Cannot coincide with anything anyway (therefore using protected keyword "TEMP"), since they are by definition disjoint with both App and Ch.
              Atom "opened", -- opened
              Atom "closed", -- closed
              applychprotSet chprotA chprotB -- secCh(A,B)
            ]
              ++ (getMsgAndSubtermsWithAtoms chmsg3)
          )
      gsmpabstractchsetops =
        [ (Atom "TEMP", applychprotSet chprotA chprotB), -- G->secCh(A,B) && G \in secCh(A,B) && G \notin secCh(A,B) [OR authCh -||-]
          (Atom "TEMP", Atom "opened"), -- G->opened && G \in opened
          (Atom "TEMP", Atom "closed") -- G->closed && G<-closed && G \in closed
        ]
   in (chmsg3, compterms, compsetops, (gsmpappterms, gsmpappsetops), (gsmpabstractchterms, gsmpabstractchsetops))

typeflawresistancecheck :: (Actions, Actions) -> (Goals, Goals) -> (Types, Types) -> [Msg] -> (Bool, [(Msg, Msg)])
-- typeflawresistancecheck (actions1, actions2) (goals1, goals2) (types1, types2) | trace ("whatishappening: " ++ show (isAppProtocol actions1) ++ " " ++ show (if isAppProtocol actions1 then types1 else types2)) False = undefined
typeflawresistancecheck (actions1, actions2) (goals1, goals2) (types1, types2) compterms =
  let firstIsApp = isAppProtocol actions1
      (appmsg1, appmsg2, chmsg3) = getmessages firstIsApp (actions1, actions2)
      appmsg1AndSubterms = getMsgAndSubtermsNotAtoms appmsg1
      appmsg2AndSubterms = getMsgAndSubtermsNotAtoms appmsg2
      chmsg3AndSubterms = getMsgAndSubtermsNotAtoms chmsg3
      allMsgs = removeDuplicates (appmsg1AndSubterms ++ appmsg2AndSubterms ++ chmsg3AndSubterms) -- trace ("Seriously ??? chmsg3: " ++ show chmsg3AndSubterms)
      assemblyLine :: [Msg] -> [Msg] -> [(Maybe Bool, Msg, Msg)]
      assemblyLine [] [] = []
      assemblyLine (currChecking : rest) [] = if (length rest) == 0 then [] else assemblyLine rest (tail rest)
      assemblyLine (currChecking : rest) (h : t) = (tryunify firstIsApp (types1, types2) (actions1, actions2) currChecking h, currChecking, h) : assemblyLine (currChecking : rest) t

      tobechecked = assemblyLine allMsgs (tail allMsgs) -- trace ("Seriously ??? Allmsgs: " ++ show allMsgs) -- ++ assemblyLine allMsgs compterms)
      -- result = foldl (\b (mbool, _, _) -> if mbool /= Just False && b /= False then b else False) True tobechecked -- trace ("Seriously ??? " ++ show tobechecked)
      faults = map (\(_, x, y) -> (x, y)) (filter (\(mbool, _, _) -> mbool == Just False) tobechecked)
      result = length faults == 0
   in (result, faults)

-------------------------------------BELOW IS FOR CONDITION 2, 3, AND 4 FOR VERITCAL COMPOSABILITY-------------------------------------

subseteq :: (Eq a) => [a] -> [a] -> Bool
subseteq _ [] = error "Error in internal function 'subseteq': Cannot take subseteq of empty list!"
subseteq [] _ = True
subseteq (e : rest) list2 = if notElem e list2 then False else subseteq rest list2

intersetion :: (Eq a) => [a] -> [a] -> [a]
intersetion _ [] = []
intersetion [] _ = []
intersetion (e : rest) list2 = if e `elem` list2 then e : intersetion rest list2 else intersetion rest list2

haslistOverlap :: (Eq a) => [a] -> [a] -> Bool
haslistOverlap [] _ = False
haslistOverlap (id : restids) addedIdents = (id `elem` addedIdents) || haslistOverlap restids addedIdents

gsmpAppSubseteqSecUnionPub :: ([Msg], [(Msg, Msg)]) -> ([String], [String]) -> Bool
gsmpAppSubseteqSecUnionPub (gsmpappterms, gsmpappsetops) (pub, sec) =
  let gsmpappstringlist = map getStringFromMsg gsmpappterms ++ map msgtupletostring gsmpappsetops
      pubsec = pub ++ sec
   in subseteq gsmpappstringlist pubsec

gsmpAbstractChIntersectionAppSubseteqPub :: ([Msg], [(Msg, Msg)]) -> ([Msg], [(Msg, Msg)]) -> [String] -> (Bool, [String])
-- gsmpAbstractChIntersectionAppSubseteqPub (gsmpappterms, gsmpappsetops) (gsmpabstractchterms, gsmpabstractchsetops) pub | trace ("app: " ++ show (map getStringFromMsg gsmpappterms ++ map msgtupletostring gsmpappsetops) ++ "\nch#: " ++ show (map getStringFromMsg gsmpabstractchterms ++ map msgtupletostring gsmpabstractchsetops)) False = undefined
gsmpAbstractChIntersectionAppSubseteqPub (gsmpappterms, gsmpappsetops) (gsmpabstractchterms, gsmpabstractchsetops) pub =
  let gsmpappstringlist = map getStringFromMsg gsmpappterms ++ map msgtupletostring gsmpappsetops
      gsmpabstractchlist = map getStringFromMsg gsmpabstractchterms ++ map msgtupletostring gsmpabstractchsetops
      intersectionofgsmps = intersetion gsmpappstringlist gsmpabstractchlist
      faults = filter (\x -> x `notElem` pub) intersectionofgsmps
   in (subseteq intersectionofgsmps pub, faults)

getKeysAndSubterms :: Msg -> [Msg]
getKeysAndSubterms msg =
  case msg of
    Atom _ -> []
    Comp op msgs -> case op of
      Scrypt -> getMsgAndSubtermsWithAtoms (head msgs)
      Crypt -> getMsgAndSubtermsWithAtoms (head msgs)
      _ -> []

noKeyHasAppLabel :: Msg -> [Msg] -> (Bool, [Msg])
-- noKeyHasAppLabel chmsg3 gsmpappterms | trace ("app: " ++ show (gsmpappterms) ++ "\nch: " ++ show (concat (map getKeysAndSubterms (getMsgAndSubtermsWithAtoms chmsg3)))) False = undefined
noKeyHasAppLabel chmsg3 gsmpappterms =
  let termsandsubterms = getMsgAndSubtermsWithAtoms chmsg3
      keyandsubterms = concat (map getKeysAndSubterms termsandsubterms)
      faults = filter (\x -> x `elem` gsmpappterms) keyandsubterms
   in (not (haslistOverlap keyandsubterms gsmpappterms), faults)

-------------------------------------OTHER STUFF-------------------------------------

allErrors :: Protocol -> Protocol -> Bool
-- allErrors protocol1 protocol2 | trace ("???" ++ show (throwIfVertErrors protocol1 && throwIfVertErrors protocol2)) False = undefined
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

getaroundLazyEval :: [(Ident, Type)] -> Bool
getaroundLazyEval idTypeList =
  let checkEveryElem :: (Eq a) => [a] -> a -> Bool -> Bool
      checkEveryElem [] _ result = result
      checkEveryElem (e : t) checke result = if e == checke then checkEveryElem t checke False else checkEveryElem t checke result
   in checkEveryElem idTypeList ("TEMP", Set) True

noWrongOverlap :: Bool -> (Types, Types) -> Bool
noWrongOverlap firstIsApp (types1, types2) =
  let idTypeList = getIdTypeList firstIsApp (types1, types2) []
   in getaroundLazyEval idTypeList

newcheckcompositionmain :: String -> String -> AnBOptsAndPars -> (ComposableResult, [String], [String], [String], [String])
newcheckcompositionmain filestr1 filestr2 otp =
  trycompose (anbparser (alexScanTokens filestr1)) (anbparser (alexScanTokens filestr2)) otp