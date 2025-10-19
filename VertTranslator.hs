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
import Msg
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