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

module PaoloTranslator where

import AnBOnP
import Ast
import Data.List
import Msg
import ProtocolTranslationTypes

-- </paolo>

isntIknowsFunction (Iknows msg) = isntFunction msg
isntIknowsFunction _ = True

isIknows (Iknows _) = True
isIknows _ = False

reorder :: [Msg] -> [Msg]
reorder l =
  let name = head l
      step = head . tail $ l
      session = last l
      rest = init $ drop 2 l
   in name : session : step : rest

ppFact Isa (State role msgs) = error "State-Fact in ISA mode"
ppFact Isa (FPState role msgs) = "State (r" ++ (ppId role) ++ ",[" ++ (ppMsgList Isa (filter isntFunction msgs)) ++ "])"
ppFact outf (State "dummy" msgs) = "state_dummy" ++ "(" ++ (ppMsgList outf (reorder (map snd msgs))) ++ ")"
ppFact outf (State role msgs) = "state_r" ++ (ppId role) ++ "(" ++ (ppMsgList outf (reorder (map snd msgs))) ++ ")"
ppFact outf (FPState role msgs) = error "ppFact: should not have FPState" --- "state_r"++(ppId role)++"("++(ppMsgList outf msgs)++")"
ppFact outf (Iknows msg) = "iknows(" ++ (ppMsg outf msg) ++ ")"
ppFact outf (Fact "&" m) = "& " ++ ppMsgListAnds outf m -- only for use with --vert flag!
ppFact outf (Fact i m) = (ppId i) ++ "(" ++ (ppMsgList outf m) ++ ")"

ppFactList outf = (ppXList (ppFact outf) ".\n") . (filter isntIknowsFunction)

-- meant to fix some things when using, e.g., & C/=i with the --vert flag, but should affect normal usage
ppFactListBetter outf =
  let firstelem [] = error "ppFactListBetter: cannot use internal function 'firstelem' on empty list!"
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

ppEq outf (x, y) = (ppMsg outf x) ++ "/=" ++ (ppMsg outf y)

ppRule Isa (l, eq, f, r) =
  (ppXList (ppFact Isa) ";\n" (filter isntIknowsFunction l))
    ++ "\n"
    ++ (if eq == [] then "" else " | " ++ (ppXList (ppEq Isa) ";\n" eq))
    ++ "\n"
    ++ (if f == [] then "=>" else error "fresh variable remaining")
    ++ "\n"
    ++ (ppXList (ppFact Isa) ";\n" (filter isntIknowsFunction r))
    ++ "\n"
ppRule outf (l, [], f, r) =
  (ppFactListBetter outf l) -- usage of ppFactListBetter instead of ppFactList
    ++ "\n"
    ++ (if f == [] then "=>" else "=[exists " ++ (ppIdList f) ++ "]=>")
    ++ "\n"
    ++ (ppFactListBetter outf r) -- usage of ppFactListBetter instead of ppFactList
    -- ++ "\n"

ppRuleList :: OutputType -> [([Fact], [(Msg, Msg)], [Ident], [Fact])] -> [Char]
ppRuleList Isa list =
  let ppRL Isa (x : xs) c = "step rule_" ++ (show c) ++ ":\n" ++ (ppRule Isa x) ++ "\n" ++ (ppRL Isa xs (c + 1))
      ppRL Isa [] _ = ""
   in ppRL Isa list 0
ppRuleList outf list = ppXList (ppRule outf) "\n" list

ppInit str ot list =
  let ppFP0 ot (x : xs) c = str ++ "_" ++ (show c) ++ ": " ++ (ppFact ot x) ++ ";\n" ++ (ppFP0 ot xs (c + 1))
      ppFP0 ot [] _ = ""
   in ppFP0 ot (filter isntIknowsFunction list) 0

ppFP str ot list =
  let ppFP0 ot (x : xs) c = str ++ "_" ++ (show c) ++ ": " ++ (ppFact ot x) ++ ";\n" ++ (ppFP0 ot xs (c + 1))
      ppFP0 ot [] _ = ""
   in ppFP0 ot list 0

subfact :: Substitution -> Fact -> Fact
subfact sub (FPState r msgs) = FPState r (map sub msgs)
subfact sub (State r msgs) = State r (map (\(x, y) -> (sub x, sub y)) msgs)
subfact sub (Iknows msg) = Iknows (sub msg)
subfact sub (Fact ident msgs) = Fact ident (map sub msgs)

subrule sub (l, eq, f, r) =
  ( map (subfact sub) l,
    map (\(x, y) -> (sub x, sub y)) eq,
    f,
    map (subfact sub) r
  )

-- <Paolo> --
-- hack to handle sequence numbers

-- sample
--  A *->B : sn(N,B),Msg
--  L => R
--  where sn(X,Y) occuring in L.
--  L . not(contains(X,seen(B)))  => R.contains(X,seen(B)))

-- example
-- step trans1:=
-- state_rB(B,0,inv(apply(sk,B)),inv(apply(pk,B)),sk,pk,A,SID).
-- iknows(crypt(inv(apply(sk,A)),pair(B,pair(SQN,Msg)))).not(contains(SQN,seen(B)))
-- =>
-- request(B,A,purposeMsg,Msg,SID).
-- state_rB(B,1,inv(apply(sk,B)),inv(apply(pk,B)),sk,pk,A,Msg,SQN,crypt(inv(apply(sk,A)),pair(B,pair(SQN,Msg))),SID).contains(SQN,seen(B))

ppRuleIFHack :: Rule -> [Ident] -> Rule
-- apply sqn hack [Ident]=list of SQNs
ppRuleIFHack ([], [], f, r) _ = ([], [], f, r)
ppRuleIFHack (l, [], f, r) sqns =
  let a = getRule2Agent l
      sqnList = nub (getFacts2SQN l sqns)
      nl = l ++ (map (\x -> (notcsterm x a)) sqnList)
      nr = r ++ (map (\x -> (csterm x a)) sqnList)
   in (nl, [], f, nr)
ppRuleIFHack _ _ = error "Sequence Number translation error"

getRule2Agent :: [Fact] -> Ident
getRule2Agent xs = getFact2Agent (head (xs))

getFact2Agent :: Fact -> Ident
getFact2Agent f = case f of
  State id _ -> id
  _ -> ""

-- retuns a list of SQNs
getFacts2SQN :: [Fact] -> [Ident] -> [Ident]
getFacts2SQN [] _ = []
getFacts2SQN (x : xs) sqns = getFact2SQN x sqns ++ getFacts2SQN xs sqns

getFact2SQN :: Fact -> [Ident] -> [Ident]
getFact2SQN f sqns = case f of
  State _ _ -> []
  FPState _ _ -> []
  Fact _ _ -> []
  Iknows m -> getMsg2SQN m sqns

getMsg2SQN :: Msg -> [Ident] -> [Ident]
getMsg2SQN (Atom id) sqns = if (elem id sqns) then [id] else []
getMsg2SQN (Comp _ []) _ = []
getMsg2SQN (Comp _ (m : ms)) sqns = getMsg2SQN m sqns ++ getMsgs2SQN ms sqns

getMsgs2SQN :: [Msg] -> [Ident] -> [Ident]
getMsgs2SQN ([]) _ = []
getMsgs2SQN (m : ms) sqns = getMsg2SQN m sqns ++ getMsgs2SQN ms sqns

-- SQN, AgentName .contains(SQN,seen(B))
csterm :: Ident -> Ident -> Fact
csterm sqn agent = Fact "contains" [Atom sqn, Comp (Userdef "seen") [Atom agent]]

-- SQN, AgentName .not(contains(SQN,seen(B)))
notcsterm :: Ident -> Ident -> Fact
notcsterm sqn agent = Fact "not" [Comp (Userdef "contains") [Atom sqn, Comp (Userdef "seen") [Atom agent]]]

-- adjust the Types to translate the SQNs in Numbers
trAdjTypes :: Types -> Type -> Type -> Types
trAdjTypes t from_t to_t =
  let idents = trTypes2Ids t from_t
      t1 = trTypesMoveIds t from_t idents to_t
   in t1

-- extract the list of ids from Type
-- used in preprocessing of Protocol

trTypes2Ids :: Types -> Type -> [Ident]
trTypes2Ids [] _ = []
trTypes2Ids types t = concatMap snd ((filter (\(x, _) -> x == t)) types)

trTypesMoveIds :: Types -> Type -> [Ident] -> Type -> Types
trTypesMoveIds [] _ _ _ = []
trTypesMoveIds t _ [] _ = t
trTypesMoveIds (x : xs) from_t idents to_t = [(trTypeMoveIds x from_t idents to_t)] ++ (trTypesMoveIds xs from_t idents to_t)

trTypeMoveIds :: (Type, [Ident]) -> Type -> [Ident] -> Type -> (Type, [Ident])
trTypeMoveIds (t, idents) from_t idents1 to_t = if t == to_t then (t, nub (idents ++ idents1)) else if t == from_t then (t, []) else (t, idents)

-- </Paolo> --