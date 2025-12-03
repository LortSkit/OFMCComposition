module CheckComposition where

import AnBOnP
import AnBParser
import AnBmain
import Ast
import Debug.Trace
import EnsuranceTools
import Lexer
import Msg
import Search (xexec_check)
import Text.Read (Lexeme (String))

trycompose :: Protocol -> Protocol -> AnBOptsAndPars -> String
-- trycompose protocol1@(_, typdec1, knowledge1, _, actions1, goals1) protocol2@(_, typdec2, knowledge2, _, actions2, goals2) _ | trace ("1:\n" ++ show (getBasePubSec typdec1 knowledge1) ++ "\n2:\n" ++ show (getBasePubSec typdec2 knowledge2)) False = undefined
trycompose protocol1@(_, typdec1, knowledge1, _, actions1, goals1) protocol2@(_, typdec2, knowledge2, _, actions2, goals2) args =
  let noErrors = not (allErrors protocol1 protocol2)
      (pub1, sec1) = getBasePubSec typdec1 knowledge1
      (pub2, sec2) = getBasePubSec typdec2 knowledge2
   in if noErrors then show pub2 else error "This is unreachable!" -- TODO: Actually return meaningful variable

getBasePubSec :: Types -> Knowledge -> ([String], [String])
getBasePubSec types knowledge =
  let removeDuplicates [] = []
      removeDuplicates (a : as) = if a `elem` as then removeDuplicates as else a : removeDuplicates as

      concatTupleFst e1 ([], l2) = ([e1], l2)
      concatTupleFst e1 (x1 : x1s, l2) = (e1 : x1 : x1s, l2)
      concatTupleSnd e2 (l1, x2 : x2s) = (l1, e2 : x2 : x2s)
      concatTupleSnd e2 (l1, []) = (l1, [e2])

      getFlatTypes :: Types -> [String]
      getFlatTypes [] = []
      getFlatTypes ((_, flats) : ts) = concat (flats : [getFlatTypes ts])

      __getFlatKnowledge :: Knowledge -> [Msg]
      __getFlatKnowledge ([], _) = []
      __getFlatKnowledge ((_, msgs) : ks, _) = concat (msgs : [_getFlatKnowledge (ks, [])])
      _getFlatKnowledge knowledge = removeDuplicates (__getFlatKnowledge knowledge)

      __getStringFromAtom :: Msg -> String
      __getStringFromAtom msg = case msg of
        Atom x -> x
        Comp _ msgs -> __getStringFromAtom (head msgs)
      -- _ -> error "Internal function '__getStringFromAtom' got an unexpected composed message! "

      _getKnowledgeAtomComp :: [Msg] -> ([String], [(String, [String])])
      _getKnowledgeAtomComp [] = ([], [])
      _getKnowledgeAtomComp (msg : msgs) = case msg of
        Atom x -> concatTupleFst x (_getKnowledgeAtomComp msgs)
        Comp Apply othermsgs ->
          let recursiveBit = (_getKnowledgeAtomComp msgs)
              fstBit = __getStringFromAtom (head othermsgs)
              sndBit = map __getStringFromAtom (tail othermsgs)
           in concatTupleSnd (fstBit, sndBit) recursiveBit
      getKnowledgeAtomComp knowledge = _getKnowledgeAtomComp (_getFlatKnowledge knowledge)

      flattypes = getFlatTypes types
      knowledgeatomcomp = getKnowledgeAtomComp knowledge
      pub = filter (`elem` fst knowledgeatomcomp) flattypes
      sec = filter (`elem` map fst (snd knowledgeatomcomp)) flattypes
   in (pub, sec)

secGSMPDisjoint :: Protocol -> Protocol -> AnBOptsAndPars -> Bool
secGSMPDisjoint protocol1@(_, types1, knowledge1, _, actions1, goals1) protocol2@(_, types2, knowledge2, _, actions2, goals2) args =
  let gsmp_p1compp2star = [""]
      gsmp_p1starcompp2 = [""]
   in False

allErrors :: Protocol -> Protocol -> Bool
allErrors protocol1@(_, _, _, _, actions1, goals1) protocol2@(_, _, _, _, actions2, goals2) =
  let structureErros = (throwIfVertErrors protocol1 && throwIfVertErrors protocol2)
      protocolTypeError = isAppProtocol actions1 == isAppProtocol actions2
      protocolTypeStr = if isAppProtocol actions1 then "App" else "Ch"
      goalType1 = getGoalType goals1
      goalType2 = getGoalType goals2
      goalTypeError = goalType1 /= goalType2
   in if structureErros
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