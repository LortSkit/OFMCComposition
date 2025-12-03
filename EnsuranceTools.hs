module EnsuranceTools where

import AnBOnP
import Ast

isAppProtocol :: Actions -> Bool
isAppProtocol [] = False
isAppProtocol (a : as) =
  let ((_, channeltype, _), _, _, _) = a
   in case channeltype of
        ChannelProtocol -> True
        _ -> isAppProtocol as

isAppCompliant :: Actions -> (Bool, Int)
isAppCompliant actions = (length actions == 2, length actions)

isChCompliant :: Actions -> (Bool, Int)
isChCompliant actions = (length actions == 1, length actions)

getGoalType :: Goals -> GoalType
getGoalType goals =
  let numberOfGoals = length goals
      isGoalCompliant = numberOfGoals == 1
   in if not isGoalCompliant
        then error ("Protocol does not have the correct number of goals! Got " ++ show numberOfGoals ++ " goals, expected 1.")
        else case head goals of
          ChGoal channel msg ->
            let (_, channeltype, _) = channel
             in case channeltype of
                  FreshAuthentic -> Auth
                  FreshSecure -> Secc
                  Confidential -> error "Confidential goaltype is not supported! Please use either *-> or *->*."
          x -> error ("Protocol has the wrong goaltype " ++ show x ++ "!\nExpected ((AGENT1,False,Nothing),X,(AGENT2,False,Nothing)), where X = FreshSecure, FreshAuthentic")

throwIfVertErrors :: Protocol -> Bool
throwIfVertErrors protocol@(_, _, _, _, actions, goals) =
  let isApp = isAppProtocol actions
      (isCompliant, numActions) = if isApp then isAppCompliant actions else isChCompliant actions
      protocolType = if isApp then "App" else "Ch"
      expectedNumActions = if isApp then 2 else 1
      goaltype = getGoalType goals
      isImplemented = not ((not isApp) && goaltype == Auth)
   in if not isCompliant
        then error ("Protocol is not compliant with " ++ protocolType ++ " protocol: Protocol has " ++ show numActions ++ " actions, expected " ++ show expectedNumActions)
        else
          not isImplemented && error "Chauth has not been proven or implemented yet!"