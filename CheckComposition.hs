module CheckComposition where

import AnBOnP
import AnBParser
import AnBmain
import Ast
import Data.Char (toLower)
import Data.List
import Debug.Trace
import EnsuranceTools
import Lexer
import Msg

trycompose :: Protocol -> Protocol -> AnBOptsAndPars -> String
-- trycompose protocol1@(_, typdec1, knowledge1, _, actions1, goals1) protocol2@(_, typdec2, knowledge2, _, actions2, goals2) _ | trace ("1:\n" ++ show (getBasePubSec typdec1 knowledge1) ++ "\n2:\n" ++ show (getBasePubSec typdec2 knowledge2)) False = undefined
trycompose protocol1@(_, typdec1, knowledge1, _, actions1, goals1) protocol2@(_, typdec2, knowledge2, _, actions2, goals2) _ | trace ("Output: " ++ show (getFinalPubSec (getBasePubSec typdec1 knowledge1) (getBasePubSec typdec2 knowledge2) (actions1, actions2))) False = undefined
trycompose protocol1@(_, typdec1, knowledge1, _, actions1, goals1) protocol2@(_, typdec2, knowledge2, _, actions2, goals2) args =
  let noErrors = not (allErrors protocol1 protocol2)
      stuff1 = getBasePubSec typdec1 knowledge1
      stuff2 = getBasePubSec typdec2 knowledge2
      (pub, sec) = getFinalPubSec stuff1 stuff2 (actions1, actions2)
   in if noErrors then show (pub, sec) else error "This is unreachable!" -- TODO: Actually return meaningful variable

__msgStrListToCommaSepStrip :: [String] -> String
__msgStrListToCommaSepStrip [] = ""
__msgStrListToCommaSepStrip [msg] = msg
__msgStrListToCommaSepStrip (msg : msgs) = msg ++ "," ++ __msgStrListToCommaSepStrip msgs

__getStringFromAtom :: Msg -> String
__getStringFromAtom msg = case msg of
  Atom x -> x
  Comp Apply msgs -> __getStringFromAtom (head msgs) ++ "(" ++ __msgStrListToCommaSepStrip (map __getStringFromAtom (tail msgs)) ++ ")"
  Comp Cat msgs -> __msgStrListToCommaSepStrip (map __getStringFromAtom msgs)
  _ -> error ("Internal function '_getMsgSubterms' got an unexpected composed message! " ++ show msg)

_getfuncString :: Msg -> [Msg] -> String
_getfuncString funcname msgs = __getStringFromAtom funcname ++ "(" ++ __msgStrListToCommaSepStrip (map __getStringFromAtom msgs) ++ ")"

removeDuplicates [] = []
removeDuplicates (a : as) = if a `elem` as then removeDuplicates as else a : removeDuplicates as

getFinalPubSec :: ([String], [String], ([String], [String])) -> ([String], [String], ([String], [String])) -> (Actions, Actions) -> (([String], [String]), ([String], [String]))
-- getFinalPubSec (flattypes1, pub1, sec1) (flattypes2, pub2, sec2) (actions1, actions2) | trace ("Actions: " ++ show actions2) False = undefined
getFinalPubSec (flattypes1, pub1, sec1) (flattypes2, pub2, sec2) (actions1, actions2) =
  let __isAnyInSec :: [([String], [String], String)] -> (Bool, String)
      -- __isAnyInSec ((pub, sec, lastadded) : stuff) | trace (if length sec > 0 && lastadded == head sec then "pub: " ++ show pub ++ ", sec: " ++ show sec ++ ", lastadded: " ++ lastadded else "") False = undefined
      __isAnyInSec [] = (False, "")
      __isAnyInSec ((pub, sec, lastadded) : stuff) = if length sec > 0 && lastadded == head sec then (True, lastadded) else __isAnyInSec stuff

      ___combinepubsec :: [([String], [String], String)] -> ([String], [String], String)
      ___combinepubsec [] = ([], [], "")
      ___combinepubsec ((pub, sec, lastadded) : stuff) =
        let (currpub, currsec, _) = ___combinepubsec stuff
         in (pub ++ currpub, sec ++ currsec, "")

      __combinepubseccorrectlastadded :: [([String], [String], String)] -> Bool -> String -> ([String], [String])
      __combinepubseccorrectlastadded stuff isSec lastadded =
        let (combinedpub, combinedsec, _) = ___combinepubsec stuff
            (correctpub, correctedsec) =
              if isSec
                then (combinedpub, lastadded : (filter (\x -> x /= lastadded) combinedsec))
                else (lastadded : (filter (\x -> x /= lastadded) combinedpub), combinedsec)
         in (correctpub, correctedsec)

      __fstInTriple :: ([String], [String], String) -> [String]
      __fstInTriple (x, _, _) = x

      _getMsgSubterms :: Msg -> ([String], [String], String)
      _getMsgSubterms msg = case msg of
        Atom x -> if x `elem` pub1 || x `elem` pub2 then ([x], [], x) else ([], [x], x)
        Comp Apply (funcname : msgs) ->
          let (currpub, currsec, lastadded) = _getMsgSubterms (head msgs) -- assuming here that the next message is a Comp Cat [stuff,stuff]
              tobeadded = _getfuncString funcname msgs
              isObviouslyPub = tobeadded `elem` pub1 || tobeadded `elem` pub2
              isObviouslySec = tobeadded `elem` fst sec1 || tobeadded `elem` snd sec1 || tobeadded `elem` fst sec2 || tobeadded `elem` snd sec2
              insidePub = head currpub == lastadded
           in if isObviouslyPub
                then (tobeadded : currpub, currsec, tobeadded)
                else
                  if isObviouslySec || not insidePub
                    then (currpub, tobeadded : currsec, tobeadded)
                    else (currpub, currsec, lastadded)
        Comp Cat msgs ->
          let pubseclastaddedlist = map _getMsgSubterms msgs
              (isSec, lastadded) = __isAnyInSec pubseclastaddedlist
              actuallastadded = if isSec then lastadded else head (__fstInTriple (head pubseclastaddedlist))
              (currpub, currsec) = __combinepubseccorrectlastadded pubseclastaddedlist isSec actuallastadded
           in (currpub, currsec, actuallastadded)
        Comp op [Comp Apply (keyname : keyinputs), msg]
          | op `elem` [Scrypt, Crypt] ->
              let (currpub, currsec, lastadded) = _getMsgSubterms msg
                  keystring = _getfuncString keyname keyinputs
                  invkeystring = "inv(" ++ keystring ++ ")"
                  opname =
                    let (firstchar : restofstring) = show op
                     in toLower firstchar : restofstring
                  tobeadded = opname ++ "(" ++ keystring ++ "," ++ lastadded ++ ")"
               in (currpub, tobeadded : currsec ++ [keystring, invkeystring], tobeadded)
        _ -> error ("Internal function '_getMsgSubterms' got an unexpected composed message! " ++ show msg)

      _actionToMsg :: Action -> Msg
      _actionToMsg (((sender, _, _), _, (receiver, _, _)), msg, _, _) = msg

      getActionsSubterms :: Actions -> ([String], [String], String)
      getActionsSubterms [] = ([], [], "")
      getActionsSubterms actions =
        let msgs = map _actionToMsg actions
            pubseclist = map _getMsgSubterms msgs
            (pub, sec, _) = ___combinepubsec pubseclist
         in (pub, sec, "")
      (opub1, osec1, _) = getActionsSubterms actions1
      (opub2, osec2, _) = getActionsSubterms actions2
   in ((removeDuplicates opub1, removeDuplicates opub2), (removeDuplicates osec1, removeDuplicates osec2))

getBasePubSec :: Types -> Knowledge -> ([String], [String], ([String], [String]))
getBasePubSec types knowledge =
  let concatTupleFst e1 ([], l2) = ([e1], l2)
      concatTupleFst e1 (x1 : x1s, l2) = (e1 : x1 : x1s, l2)
      concatTupleSnd e2 (l1, x2 : x2s) = (l1, e2 : x2 : x2s)
      concatTupleSnd e2 (l1, []) = (l1, [e2])

      getFlatTypes :: Types -> [String]
      getFlatTypes [] = []
      getFlatTypes ((_, flats) : ts) = flats ++ getFlatTypes ts

      __getFlatKnowledge :: Knowledge -> [Msg]
      __getFlatKnowledge ([], _) = []
      __getFlatKnowledge ((_, msgs) : ks, _) = msgs ++ _getFlatKnowledge (ks, [])
      _getFlatKnowledge knowledge = removeDuplicates (__getFlatKnowledge knowledge)

      _getKnowledgeAtomComp :: [Msg] -> ([String], [(String, String)])
      _getKnowledgeAtomComp [] = ([], [])
      _getKnowledgeAtomComp (msg : msgs) = case msg of
        Atom x -> concatTupleFst x (_getKnowledgeAtomComp msgs)
        Comp Apply othermsgs ->
          let recursiveBit = (_getKnowledgeAtomComp msgs)
              fstBit = __getStringFromAtom (head othermsgs)
              sndBit = __getStringFromAtom (head (tail othermsgs))
           in concatTupleSnd (fstBit, sndBit) recursiveBit
      getKnowledgeAtomComp knowledge = _getKnowledgeAtomComp (_getFlatKnowledge knowledge)

      atomCompToString :: (String, String) -> String
      atomCompToString (funcname, concatedmsgs) = funcname ++ "(" ++ concatedmsgs ++ ")"

      flattypes = getFlatTypes types
      knowledgeatomcomp = getKnowledgeAtomComp knowledge
      pub = filter (`elem` fst knowledgeatomcomp) flattypes
      atomsec = filter (`notElem` fst knowledgeatomcomp) flattypes
      compsec = map atomCompToString (snd knowledgeatomcomp)
      sec = (atomsec, compsec)
   in (flattypes, pub, sec)

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

newcheckcompositionmain :: String -> String -> AnBOptsAndPars -> String
newcheckcompositionmain filestr1 filestr2 otp =
  trycompose (anbparser (alexScanTokens filestr1)) (anbparser (alexScanTokens filestr2)) otp