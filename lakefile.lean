import Lake
open Lake DSL

package «coea_level_based» where
  -- CoEA Level-Based Phase Transition formalization

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CoEALevelBased» where
  roots := #[`RLocalGames, `WitnessGameDrift, `CRNRanking, `LintOptions, `CoEALevelBased, `SimultaneousPersistence,
             `UnifiedPaperValidation, `TimeVaryingLinearRuntime,
             `GameTheoryMinimax, `Duality.Common, `Duality.ExtendedFields,
             `Duality.FarkasBartl, `Duality.FarkasBasic, `Duality.FarkasSpecial,
             `Duality.LinearProgramming, `Duality.LinearProgrammingB,
             `FifoTrapObstruction, `WitnessVeto,
             `NonseparablePairSkeleton, `CoevolutionDeepBounds, `Hoeffding,
             `HoeffdingBridge, `LBTPreconditions, `TrapGameEA, `SimulationCoupling,
             `MeanRankingLemma, `GapClosureSolutions, `CheckTypes,
             `DriftTheorems.AdditiveDrift, `DriftTheorems.MultiplicativeDrift,
             `DriftTheorems.NegativeDrift, `LeCamLowerBound, `LBTCoupling]

lean_exe «coea_level_based» where
  root := `Main
