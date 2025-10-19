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
import Msg
import PaoloTranslator
import ProtocolTranslationTypes

vertformats :: ProtocolTranslationState -> ProtocolTranslationState
vertformats pts =
  let (name, types, knowledge, abstractions, actions, goals) = protocol pts
      formats = concatMap snd ((filter (\(x, y) -> x == Format)) types)
      knowledge' = fKnow formats knowledge
      abstractions' = map (fAbs formats) abstractions
      actions' = (if vert (options pts) then map (fACt formats) actions else map (fAct formats) actions)
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
fAct formats ((sp@(sender, _, _), ChannelProtocol, _), _, _, _) = error "Channel protocols only supported when using --vert flag!"
fAct formats ((sp@(sender, b1, Just _), _, _), _, _, _) = error "Explicit pseudonyms not supported right now."
fAct formats ((_, _, rp@(receiver, b2, Just _)), _, _, _) = error "Explicit pseudonyms not supported right now."
-- (fChan formats channel,fMsg formats m,Nothing,Nothing)
fAct formats (_, _, _, _) = error "zero knowledge not supported here\n"

-- this is what happens instead when using --vert for ChannelProtocol (MIGHT NEED TO CHANGE LATER, FOR NOW -Ch-> IS THE SAME AS SECURE CHANNEL TYPE!)
fACt formats ((sp@(sender, b1, Nothing), ChannelProtocol, rp@(receiver, b2, Nothing)), m, Nothing, Nothing) =
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
fACt formats ((sp@(_,_,_),ChannelProtocol,_),_,_,_) = error "Wtf? unaccounted channel protcol error encountered: -Ch-> cannot be used like this!"
fACt formats x = fAct formats x

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
                      ++ (printTypes typdec)
                      ++ (printTypes [(Function, ["sent","secCh"])]) -- only have this if App protocol!!! -- Should i make them protected keywords like "secret" is?
                      -- ++ (printTypes [(Set, ["opened","closed"])]) -- only have this if Ch protocol
                      ++ "\n"
                  )
                else ""
            )
              ++ "section inits:\n"
              ++ " initial_state init1 :=\n"
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