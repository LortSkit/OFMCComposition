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
--Alexander Laukamp created this file, though most things are taken from Translator.hs

module VertTranslator where

import AnBOnP
import Ast
import Control.Monad
import Data.List
import Data.Maybe
import LMsg
import Msg
import MsgPat
import PaoloTranslator
import ProtocolTranslationTypes
import LMsg (LMsg)
import Debug.Trace

vertformats :: ProtocolTranslationState -> ProtocolTranslationState
vertformats pts =
  let (name, types, knowledge, abstractions, actions, goals) = protocol pts
      formats = concatMap snd ((filter (\(x, y) -> x == Format)) types)
      knowledge' = fKnow formats knowledge
      abstractions' = map (fAbs formats) abstractions
      actions' = map (fAct formats) actions
      goals' = map (fGoal formats) goals
   in pts {protocol = (name, types, knowledge', abstractions', actions', goals')}

fKnow formats (typings, diseqs) =
  ( [(a, nub $ Atom a : chanKnow a ++ (map Atom formats) ++ map (fMsg formats) ms) | (a, ms) <- typings],
    [(fMsg formats s, fMsg formats t) | (s, t) <- diseqs]
  )
  where
    chanKnow a =
      [ Comp Pseudonym [Atom a],
        Comp Inv [Comp AuthChan [Atom a]],
        Comp Inv [Comp ConfChan [Atom a]],
        Comp Inv [Comp Pseudonym [Atom a]]
      ]

fAct formats ((sp@(sender, False, Nothing), Insecure, rp@(receiver, False, Nothing)), m, Nothing, Nothing) =
  ((sp, Insecure, rp), fMsg formats m, Nothing, Nothing)
fAct formats ((sp@(sender, _, Nothing), Insecure, rp@(receiver, _, Nothing)), m, Nothing, Nothing) =
  error "Pseudonymous endpoint at an insecure channel. Why?\n"
fAct formats ((sp@(sender, b, Nothing), Authentic, rp@(receiver, False, Nothing)), m, Nothing, Nothing) =
  let senderpk = if b then Comp Pseudonym [Atom sender] else Comp AuthChan [Atom sender]
      m' =
        if b
          then Comp Cat [senderpk, Comp Crypt [Comp Inv [senderpk], m]]
          else Comp Crypt [Comp Inv [senderpk], m]
   in (((sender, False, Nothing), Authentic, rp), fMsg formats m', Nothing, Nothing)
fAct formats ((sp@(sender, b, Nothing), Authentic, rp@(receiver, _, Nothing)), m, Nothing, Nothing) =
  error "Pseudonymous receiver at an authentic channel. Why?\n"
fAct formats ((sp@(sender, False, Nothing), Confidential, rp@(receiver, b, Nothing)), m, Nothing, Nothing) =
  let receiverpk = if b then Comp Pseudonym [Atom receiver] else Comp ConfChan [Atom receiver]
      m' = Comp Crypt [receiverpk, m]
   in ((sp, Insecure, (receiver, False, Nothing)), fMsg formats m', Nothing, Nothing)
fAct formats ((sp@(sender, True, Nothing), Confidential, rp@(receiver, b, Nothing)), m, Nothing, Nothing) =
  error "Pseudonymous sender at a confidential channel. Why?\n"
fAct formats ((sp@(sender, b1, Nothing), Secure, rp@(receiver, b2, Nothing)), m, Nothing, Nothing) =
  if b1 && b2
    then error "Both endpoints of a secure channel pseudonymous. Why?\n"
    else
      let senderpk = if b1 then Comp Pseudonym [Atom sender] else Comp AuthChan [Atom sender]
          receiverpk = if b2 then Comp Pseudonym [Atom receiver] else Comp ConfChan [Atom receiver]
          m' =
            if b1
              then Comp Cat [senderpk, Comp Crypt [receiverpk, Comp Crypt [Comp Inv [senderpk], m]]]
              else Comp Crypt [receiverpk, Comp Crypt [Comp Inv [senderpk], m]]
       in (((sender, False, Nothing), Insecure, (receiver, False, Nothing)), fMsg formats m', Nothing, Nothing)
fAct formats ((sp@(sender, False, Nothing), ChannelProtocol, rp@(receiver, False, Nothing)), m, Nothing, Nothing) =
  ((sp, Insecure, rp), fMsg formats m, Nothing, Nothing)
fAct formats ((sp@(_,_,_),ChannelProtocol,_),_,_,_) = error "Wtf? unaccounted channel protcol error encountered: -Ch-> cannot be used like this!"
fAct formats ((sp@(sender, b1, Just _), _, _), _, _, _) = error "Explicit pseudonyms not supported right now."
fAct formats ((_, _, rp@(receiver, b2, Just _)), _, _, _) = error "Explicit pseudonyms not supported right now."
-- (fChan formats channel,fMsg formats m,Nothing,Nothing)
fAct formats (_, _, _, _) = error "zero knowledge not supported here\n"

fChan :: (Monad m1, Monad m2) => [Ident] -> ((a1, b1, m1 Msg), b2, (a2, b3, m2 Msg)) -> ((a1, b1, m1 Msg), b2, (a2, b3, m2 Msg))
fChan formats (p1, chtype, p2) = (fPeer formats p1, chtype, fPeer formats p2)

fPeer formats (id, b, mm) = (id, b, liftM (fMsg formats) mm)

fAbs formats (id, m) = (id, fMsg formats m)

fGoal formats (ChGoal ch m) = ChGoal (fChan formats ch) (fMsg formats m)
fGoal formats (Secret m ps b) = Secret (fMsg formats m) (map (fPeer formats) ps) b
fGoal formats (Authentication p1 p2 m) = Authentication (fPeer formats p1) (fPeer formats p2) (fMsg formats m)
fGoal formats (WAuthentication p1 p2 m) = WAuthentication (fPeer formats p1) (fPeer formats p2) (fMsg formats m)

fMsg :: [Ident] -> Msg -> Msg
fMsg formats (Comp Apply [Atom f, Comp Cat args])
  | f `elem` formats = Comp Cat $ Atom f : map (fMsg formats) args
  | otherwise = Comp Apply [Atom f, Comp Cat $ map (fMsg formats) args]
fMsg formats (Comp Apply [Atom f, arg])
  | f `elem` formats = Comp Cat $ Atom f : [fMsg formats arg]
  | otherwise = Comp Apply $ Atom f : [fMsg formats arg]
fMsg formats (Comp f args) = Comp f $ map (fMsg formats) args
fMsg formats (Atom a) = Atom a

---- Translation Stage 1: Creating Rules
----------------------------------------

vertcreateRules :: ProtocolTranslationState -> ProtocolTranslationState
vertcreateRules pts =
  let (p@(_, types, knowledge, abstractions, actions, goals)) = protocol pts
      frMsg = fresh p
      pks = concatMap snd ((filter (\(x, y) -> x == PublicKey)) types)
      roles =
        ( snd
            . head
            . (filter (\x -> case (fst x) of Agent _ _ -> True; _ -> False))
        )
          types
   in pts {rules = manageRules 0 frMsg (\x -> initialState (lookupL x knowledge)) actions pks}

manageRules step fresh states actions pks =
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
      (rule, state') = createRule thisfresh freshpks ub (states ub) min mout
   in rule
        : ( if step == (length actions)
              then []
              else
                manageRules
                  (step + 1)
                  (fresh \\ thisfresh)
                  (\x -> if x == ub then state' else states x)
                  actions
                  pks
          )

createRule fresh freshpks role state incomin outgoin =
  let (state1, msg1) =
        case incomin of
          Nothing -> (state, Atom "i")
          Just (sender, ct, receiver, recm, Nothing) -> (state, Atom "i")
            -- let st = (receiveMsg recm state)
            --  in (state, chtrafo False sender ct receiver (snd (last st)))
          Just (sender, ct, receiver, recm, Just recmp) ->
            let st = (receiveLMsg (recm, recmp) state)
             in (state, chtrafo False sender ct receiver (snd (last st)))
      (state2, msg2) =
        case outgoin of
          Nothing -> (state1, Atom "i")
          Just (sender, ct, receiver, sndm, _) -> (state1, Atom "i")
            -- let state1' = peertrafo receiver msg1 state1
            --     st = sendMsgAnyway sndm (state1' ++ (map (\x -> (Atom x, Atom x)) fresh) ++ (map (\x -> (Comp Inv [Atom x], Comp Inv [Atom x])) freshpks))
            --  in (st, chtrafo True sender ct receiver (snd (last st)))
   in ( ( ( State
              role
              ( ( (nubBy eqSnd)
                    . (\x -> (Atom role, Atom role) : (x ++ [(Atom "SID", Atom "SID")]))
                    . (take (length state))
                )
                  state1
              )
          )
            : (if msg1 == (Atom "i") then [Fact "contains" [Comp Apply [Atom "c", Atom "T"],Atom "globalcounter"]] else [Iknows msg1]),
          [],
          fresh,
          ( State
              role
              (((nubBy eqSnd) . (\x -> (Atom role, Atom role) : (x ++ [(Atom "SID", Atom "SID")]))) state1)
          )
            : (if msg2 == (Atom "i") then [Fact "contains" [Atom "T", Atom "globalcounter"]] else [Iknows msg2])
        ),
        state1
      )

sendMsgAnyway :: Msg -> ProtocolState -> ProtocolState
sendMsgAnyway msg state =
  case synthesisPattern state msg of
    Nothing ->state ++ [(msg, msg)] -- i have no idea what I'm doing
    Just p -> state ++ [(msg, p)]

eqSnd (_, a) (_, b) = a == b

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

fresh :: Protocol -> [Ident]
fresh (_, types, (knowl, _), _, actions, _) =
  let longterm = nub $ concatMap ((concatMap idents) . snd) knowl
      all = nub $ concatMap (\(_, m, _, _) -> idents m) actions
      --- here we don't count sender/receiver names (can't be fresh)
      fresh = nub (all \\ longterm)
      longterm_fresh = filter (not . isAgent . (gettype types)) (filter isVariable longterm)
      const_fresh = filter (not . isVariable) fresh
      declarednonsense = filter (\x -> elem x ["inv", "exp", "xor"]) (nub $ [a | (_, l) <- knowl, (Atom a) <- l] ++ concatMap snd types)
   in if declarednonsense /= []
        then error $ "Error: the following functions: " ++ show declarednonsense ++ " are predefined. They cannot be declared in the type section or declared as an element of the knowledge of an agent. (Function values can be used though.)\n"
        else
          if const_fresh /= []
            then error $ "Error: the following constant(s) are not contained in initial knowledge of any role: " ++ (ppIdList const_fresh)
            else
              if longterm_fresh /= []
                then error $ "Error: the following variable(s) occur in the initial knowledge but are not of type agent: " ++ (ppIdList longterm_fresh)
                else fresh

toJust ::
  Maybe Action ->
  ( Maybe Ident,
    ChannelType,
    Maybe Ident,
    Maybe (Peer, ChannelType, Peer, Msg, Maybe Msg),
    Maybe Msg,
    Maybe Msg
  )
toJust Nothing = (Nothing, Secure, Nothing, Nothing, Nothing, Nothing)
toJust (Just ((sp@(a, _, _), ct, rp@(b, _, _)), m, mp, zk)) =
  (Just a, Secure, Just b, Just (sp, ct, rp, m, mp), mp, zk)

---------- Channel Transformation ---------

chtrafo :: Bool -> Peer -> ChannelType -> Peer -> Msg -> Msg
chtrafo _ (_, False, _) _ (_, False, _) msg = msg
chtrafo _ _ _ _ _ = error "This can't be happening!"

{- Long comment was here in Translator.hs - I removed it from here-}

peertrafo :: Peer -> Msg -> ProtocolState -> ProtocolState
peertrafo (receiver, ispseudo, Just nym) inmsg protostate = 
  protostate ++ [(nym, nym)]
-- error "Not yet implemented: alternative pseudos in protocol."
peertrafo (receiver, ispseudo, Nothing) inmsg protostate =
  let pseus =
        ( nub
            . (filter (isPrefixOf "Pseudonym"))
            . idents
        )
          inmsg
      pseusbackup = nub . (filter (isPrefixOf "Pseudonym")) . concatMap idents $ map snd protostate
   in if (length pseus) > 1
        then
          error
            ( "Too much pseudo in inmsgs="
                ++ (show inmsg)
                ++ " namely "
                ++ (show pseus)
            )
        else
          if (length pseus) == 0
            then
              if ispseudo
                then
                  if (length pseusbackup == 1)
                    then
                      protostate
                    else
                      error ("Sending to a pseudonymous endpoint requires that the previous step was from that pseudonymous endpoint")
                else
                  protostate
            else
              let [pseu] = pseus
               in if (Atom pseu) `elem` (map snd protostate)
                    then protostate
                    else protostate ++ [(Atom pseu, Atom pseu)]

peerToMsgKnwn :: Peer -> Msg
peerToMsgKnwn (a, False, _) = Atom a
peerToMsgKnwn (a, True, Nothing) = Comp Apply [Atom "pseudonym", Atom a]
peerToMsgKnwn (a, True, Just _) = error "N/A"

peerToMsgUKnwn :: Peer -> Msg
peerToMsgUKnwn (a, False, _) = Atom a
peerToMsgUKnwn (a, True, Just _) = error "N/A"
peerToMsgUKnwn (a, True, Nothing) = Atom ("Pseudonym" ++ a)

lookupL :: Ident -> Knowledge -> [Msg]
lookupL x ([], _) = error ("Initial knowledge of role " ++ (show x) ++ " not specified.")
lookupL x (((y, k) : ys), ineq) = if x == y then k else lookupL x (ys, ineq)

--- Stage 4: Adding the initial state
-------------------------------------

vertaddInit :: ProtocolTranslationState -> ProtocolTranslationState
vertaddInit pts =
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
   in pts
        { initial =
            ( if typed args
                then
                  ( "section types:\n"
                      ++ (ppIdList agents)
                      ++ ":agent\n"
                      ++ (printTypes typdec)
                      ++ (printTypes [(Function, ["sent","secCh"])]) -- only have this if App protocol!!! -- Should i make them protected keywords like "secret" is?
                      -- ++ (printTypes [(Set, ["opened","closed"])]) -- only have this if Ch protocol
                      ++ (printTypes [(Function, ["c"])])
                      ++ (printTypes [(Set, ["globalcounter"])])
                      ++ "\n"
                  )
                else ""
            )
              ++ "section inits:\n"
              ++ " initial_state init1 :=\n"
              ++ "contains(apply(c,apply(c,apply(c,apply(c,apply(c,apply(c,apply(c,0))))))),globalcounter).\n" -- TODO: Make sure it contains as many steps as specified (somewhere)! 
              ++ (ppFactList IF facts)
              ++ (concatMap (\x -> " & " ++ (ppId x) ++ "/=i") honest)
              ++
              ---    (concatMap (\ (x,y) -> " & "++(ppId x)++"/="++(ppId y)) [(x,y) | x<-agents0, y<-agents0, x/=y])++
              ---    (error $ (show aglili) ++ (show (concatMap (\ (x,y) -> " & "++(ppId x)++"/="++(ppId y)) [(x,y) | l<-aglili, x<-l, y<-l, x/=y])))++
              (concatMap (\(s, t) -> " & " ++ (ppMsg IF s) ++ "/=" ++ (ppMsg IF t)) ineq')
              ++ "\n\n"
              ++ "section rules:\n"
        }

getCrypto :: [Ident] -> [Fact]
getCrypto agents =
  map
    Iknows
    ( (Atom "confChCr")
        : (Atom "authChCr")
        : (Comp Inv [Comp Apply [Atom "authChCr", Atom "i"]])
        : (Comp Inv [Comp Apply [Atom "confChCr", Atom "i"]])
        : []
    )

printTypes :: Types -> String
printTypes =
  let f (Agent _ _, ids) = (ppIdList ids) ++ ":agent\n"
      f (Number, ids) = (ppIdList ids) ++ ":text\n"
      f (SeqNumber, _) = ""
      f (PublicKey, ids) = (ppIdList ids) ++ ":public_key\n"
      f (SymmetricKey, ids) = (ppIdList ids) ++ ":symmetric_key\n"
      f (Function, ids) = (ppIdList ids) ++ ":function\n"
      f (Set, ids) = (ppIdList ids) ++ ":set\n" -- should only be used when using --vert!
      f (Payload, ids) = (ppIdList ids) ++ ":payload\n"
      f (Custom x, ids) = (ppIdList ids) ++ ":t_" ++ x ++ "\n"
      f (Untyped, _) = ""
      f (Format, ids) = (ppIdList ids) ++ ":text" ++ "\n"
   in concatMap f

getIK0 :: [Fact] -> [Fact]
getIK0 states =
  let f (Atom a) =
        if (isVariable a) && (a /= "SID")
          then Atom "i"
          else Atom a
      f (Comp o as) = Comp o (map f as)
   in ( (map (Iknows . f))
          . nub
          . (concatMap getMsgs)
          . (filter (\(State role msgs) -> isVariable role))
      )
        states

getMsgs :: Fact -> [Msg]
getMsgs (State role msgs) = map snd msgs
getMsgs (FPState role msgs) = msgs
getMsgs (Iknows msg) = [msg]
getMsgs (Fact _ msgs) = msgs

getinitials :: [Rule] -> Knowledge -> [Fact]
getinitials rules =
  (map (\(x, y) -> State x (map (\z -> (z, z)) ((Atom x) : (Atom "0") : (((analysis y) \\ [Atom x]) ++ [Atom "SID"]))))) . fst

instantiate :: Int -> [Fact] -> [(Msg, Msg)] -> ([Fact], [Ident], [[Ident]], [Ident], [Fact], [(Msg, Msg)])
instantiate n states ineq =
  let nstates = zip states [1 ..]
      inst0 i n (State role msgs) =
        let f (Atom a) =
              if (isVariable a) && (a /= "SID")
                then Atom (a ++ "_" ++ (show i) ++ "_" ++ (show n))
                else Atom a
            f (Comp o as) = Comp o (map f as)
            varcheck = (nub (concatMap vars (map snd msgs))) \\ (nub (filter isVariable (map (\(Atom x) -> x) (filter isAtom (map snd msgs)))))
         in if varcheck == []
              then insSid n (State role (map (\(x, y) -> (f x, f y)) msgs))
              else
                error
                  ( "Currently not supported:\n "
                      ++ " role "
                      ++ role
                      ++ " does not know "
                      ++ (show varcheck)
                      ++ "\n"
                      ++ " but functions of "
                      ++ (show varcheck)
                      ++ "\n."
                  )
      ik0 i n (State role msgs) =
        let f (Atom a) =
              if (isVariable a) && (a /= "SID")
                then
                  if a == role
                    then (Atom "i")
                    else Atom (a ++ "_" ++ (show i) ++ "_" ++ (show n))
                else Atom a
            f (Comp o as) = Comp o (map f as)
         in if isVariable role
              then map (Iknows . f) (map snd msgs)
              else []
      ik = nub (concat [ik0 i k f | k <- [1 .. n], (f, i) <- nstates])
      insSid i (State r m) =
        State r ((init m) ++ (map (\x -> (x, x)) [Atom (show (2 * i))]))
      instfacts = [inst0 i k f | k <- [1 .. n], (f, i) <- nstates]
      instineq0 i n (s, t) =
        let f (Atom a) =
              if (isVariable a) && (a /= "SID")
                then Atom (a ++ "_" ++ (show i) ++ "_" ++ (show n))
                else Atom a
            f (Comp o as) = Comp o (map f as)
         in (f s, f t)
      instineq = [instineq0 i k e | k <- [1 .. n], (_, i) <- nstates, e <- ineq]
      aglili =
        [ nub [name ++ "_" ++ (show (i)) ++ "_" ++ (show k) | k <- [1 .. n]]
          | (State r msgs, i) <- nstates,
            name <-
              ( (filter ((/=) "SID"))
                  . (filter isVariable)
                  . (concatMap idents)
                  . (concatMap getMsgs)
              )
                [(State r msgs)],
            isVariable name
        ]
      honestNames =
        nub
          [ name ++ "_" ++ (show (i)) ++ "_" ++ (show k)
            | (State _ ((_, Atom name) : _), i) <- nstates,
              k <- [1 .. n],
              isVariable name
          ]
      allNames =
        ( nub
            . (filter ((/=) "SID"))
            . (filter isVariable)
            . (concatMap idents)
            . (concatMap getMsgs)
        )
          instfacts
   in ( instfacts,
        honestNames,
        aglili,
        allNames,
        (Iknows $ Atom "guessPW") : ik,
        instineq
      )

--- Stage 5: printing the rules
--------------------------------

getTypes :: Protocol -> Types
getTypes (_, t, _, _, _, _) = t

-- <paolo>
vertruleList :: Bool -> ProtocolTranslationState -> String
vertruleList if2cif pts =
  -- pass the list of SQNs
  ruleListIF (initial pts, rules pts) (trTypes2Ids (getTypes (protocol pts)) SeqNumber) if2cif

ruleListIF :: (String, [Rule]) -> [Ident] -> Bool -> String
-- ruleListIF (init,rules) _ _ | trace ("ruleListIF\n" ++ init ++ "\n" ++ foldr (\a s ->(ppRule IF a ++"\n") ++s ) ""  rules) False = undefined
-- ruleListIF (init,rules) _ _ | trace ("ruleListIF\n" ++ foldr (\a s ->show a ++ (ppRule IF a ++"\n") ++s ) ""  rules) False = undefined -- debug for --vert
ruleListIF (init, rules) sqns if2cif =
  let ruleIF [] _ = ""
      ruleIF (x : xs) n =
        let -- rule hacked SQN
            nr1 = ppRuleIFHack x sqns
            -- IF2CIF
            nr2 = if if2cif then ppRuleIF2CIF nr1 else nr1
         in "step app" ++ (show (n+3)) ++ ":=\n" ++ (ppRule IF nr2) ++ "\n" ++ (ruleIF xs (n + 1)) -- TODO: make sure the name is app or ch based on the protocol!
   in init ++ (ruleIF (firstRuleSplitApp rules) 0)

firstRuleSplitApp :: [Rule] -> [Rule]
firstRuleSplitApp rules | trace ("firstRuleSplitApp\n" ++ show (last ((\(l,_,_,_) -> l) (head rules)))) False = undefined
firstRuleSplitApp rules = 
  let (l,eq,eqid,r) = head rules 
      append a [] = [a]
      append a (x:xs) = x:append a xs
      l1 = append (Fact "&" [Comp Neq [Atom "C", Atom "i"]]) l -- TODO: Grab C from knowledge s.t. it is not hard-coded!!!
  in (l1,eq,eqid,r) : tail rules

ppRuleIF2CIF :: Rule -> Rule
-- ppRuleIF2CIF r | trace ("ppRuleIF2CIF\n\tr: " ++ ppRule IF r) False = undefined
ppRuleIF2CIF (l, eq, f, r) =
  let l1 = map (\x -> subfactIF2CIFik subMsgIF2CIF x) l
      l2 = map (\x -> subfactIF2CIFik subMsgIF2CIFLabel x) l1
      r1 = map (\x -> subfactIF2CIFik subMsgIF2CIF x) r
      r2 = map (\x -> subfactIF2CIFik subMsgIF2CIFLabel x) r1
   in (l2, eq, f, r2)

subMsgIF2CIF :: Msg -> Msg
-- subMsgIF2CIF m | trace ("subMsgIF2CIF\n\tm: " ++ show m) False = undefined
-- rewrite messages IF/Annotated AnB -> CryptIF
subMsgIF2CIF (Comp Cat (Atom "atag" : [Comp Cat [Atom a, msg]])) = Comp Crypt [Comp Inv [Comp Apply [Atom "sk", Atom a]], msg]
subMsgIF2CIF (Comp Cat (Atom "fatag" : [Comp Cat [Atom a, msg]])) = Comp Crypt [Comp Inv [Comp Apply [Atom "sk", Atom a]], msg]
subMsgIF2CIF (Comp Cat (Atom "ctag" : [Comp Crypt [Comp Apply [Atom "blind", Atom b], msg]])) = Comp Crypt [Comp Apply [Atom "pk", Atom b], msg]
subMsgIF2CIF (Comp Cat (Atom "stag" : [Comp Crypt [Comp Apply [Atom "blind", Atom b], Comp Cat [Atom a, msg]]])) = Comp Crypt [Comp Apply [Atom "pk", Atom b], Comp Crypt [Comp Inv [Comp Apply [Atom "sk", Atom a]], msg]]
subMsgIF2CIF (Comp Cat (Atom "fstag" : [Comp Crypt [Comp Apply [Atom "blind", Atom b], Comp Cat [Atom a, msg]]])) = Comp Crypt [Comp Apply [Atom "pk", Atom b], Comp Crypt [Comp Inv [Comp Apply [Atom "sk", Atom a]], msg]]
subMsgIF2CIF (Comp Cat (Atom "plain" : [Atom msg])) = Atom msg
subMsgIF2CIF (Comp Cat (Atom "ctag" : [Atom msg])) = Atom msg
subMsgIF2CIF (Comp Cat (Atom "stag" : [Atom msg])) = Atom msg
subMsgIF2CIF (Comp Cat (Atom "fstag" : [Atom msg])) = Atom msg
subMsgIF2CIF (Comp Cat (Atom "plain" : x : [])) = x
subMsgIF2CIF (Comp Cat (Atom "ctag" : x : [])) = x
subMsgIF2CIF (Comp Cat (Atom "stag" : x : [])) = x
subMsgIF2CIF (Comp Cat (Atom "fstag" : x : [])) = x
subMsgIF2CIF (Comp Cat (Atom "plain" : xs)) = (Comp Cat xs)
subMsgIF2CIF (Comp Cat (Atom "ctag" : xs)) = (Comp Cat xs)
subMsgIF2CIF (Comp Cat (Atom "stag" : xs)) = (Comp Cat xs)
subMsgIF2CIF (Comp Cat (Atom "fstag" : xs)) = (Comp Cat xs)
-- subMsgIF2CIF (Comp Crypt [Comp Apply [Atom "blind",_],_]) = Atom "blind"   -- blind cleanup  iknows(pair(stag,crypt(apply(blind,A),pair(B,pair(A,Msg))))) => stateR(... crypt(apply(blind,A),pair(B,pair(A,Msg))),pair(stag,crypt(apply(blind,A),pair(B,pair(A,Msg))))
-- subMsgIF2CIF (Comp op xs) = Comp op (map (\x -> (subMsgIF2CIF x)) xs)
subMsgIF2CIF m = m

replace old new l = mijoin new . split old $ l

mijoin sep [] = []
mijoin sep lists = foldr1 (\x y -> x ++ sep ++ y) lists

split sep list =
  let split0 accword acclist sep [] = reverse ((reverse accword) : acclist)
      split0 accword acclist sep list =
        if isPrefixOf sep list
          then split0 "" ((reverse accword) : acclist) sep (drop (length sep) list)
          else split0 ((head list) : accword) acclist sep (tail list)
   in split0 [] [] sep list

subMsgIF2CIFLabel :: Msg -> Msg
-- subMsgIF2CIFLabel (Atom a) | trace ("subMsgIF2CIFLabel\n\tAtom a: " ++ show a) False = undefined
subMsgIF2CIFLabel (Atom a) = Atom (replace "XCryptblind" "XCryptpk" a) -- blind cleanup
subMsgIF2CIFLabel (Comp op xs) = Comp op (map subMsgIF2CIFLabel xs)

filterLMsg :: [LMsg] -> [LMsg]
-- filterLMsg msgs | trace ("filterLMsg\n\tmsgs: " ++ show msgs) False = undefined
filterLMsg [] = []
filterLMsg (x : []) = [x]
filterLMsg (x@(Atom "blind", Atom "blind") : xs) = [x] ++ filterLMsg xs
filterLMsg ((Atom "blind", _) : xs) = filterLMsg xs -- blind cleanup
filterLMsg (x : xs) = if elem (snd (x)) (map snd xs) then xs else [x] ++ (filterLMsg xs)

-- subfactIF2CIF :: Substitution -> Fact -> Fact
---- subfactIF2CIF _ (State r msgs)| trace ("subfactIF2CIF\n\tr: " ++ show r ++ "\n\tmsgs: " ++ show msgs) False = undefined
-- subfactIF2CIF sub (FPState r msgs) = FPState r (nub(map sub msgs))
-- subfactIF2CIF sub (State r msgs) = let
--                                        msgs1 = filterLMsg (map (\ (x,y)-> (sub x, sub y)) msgs)
--                                   in State r msgs1
-- subfactIF2CIF sub (Iknows msg) = Iknows (sub msg)
-- subfactIF2CIF sub (Fact ident msgs) = Fact ident (nub(map sub msgs))
---- subfactIF2CIF _ f = f

subfactIF2CIFik :: Substitution -> Fact -> Fact
-- subfactIF2CIFIK _ (State r msgs)| trace ("subfactIF2CIFIK\n\tr: " ++ show r ++ "\n\tmsgs: " ++ show msgs) False = undefined
subfactIF2CIFik sub (Iknows msg) = Iknows (sub msg)
subfactIF2CIFik _ f = f

-------------------------------------
vertendstr :: Bool -> String
vertendstr noowngoal =
  "section attack_states:\n"
    ++ "  attack_state temp :=\n"
    ++ "    secret(AnB_M,AnB_A).\n"
    ++ "    iknows(AnB_M)\n"