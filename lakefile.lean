import Lake
open Lake DSL

package jsp1006 where
  version := v!"0.1.0"
  leanOptions := #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, 3⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @
  "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target] lean_lib JSP1006Proof where
  roots := #[
    `CofactorCounting,
    `ComparisonBudget,
    `DyadicBadWindows,
    `DyadicDensity,
    `Elementary,
    `Erdos1201,
    `FarAmbient,
    `FarCofactors,
    `FarCutoffPayment,
    `FarEnergyTransfer,
    `FarExceptionalEnergy,
    `FarLargePrimeEnergy,
    `FarNoSmallEnergy,
    `FarPaidProduct,
    `FarRecombination,
    `FarRectangle,
    `FarSampleEnergy,
    `FarSampleSmall,
    `FarScheduledEnergy,
    `FarSetUtils,
    `FarTypicalEnergy,
    `LongWindowDeficit,
    `LongWindowUniform,
    `OriginalThreshold,
    `PerronThreeBand,
    `PrimeWindow,
    `RealFarEnergy,
    `RealFarSeparation,
    `RealTwoLengthComparison,
    `ThetaLogPower,
    `TruncationComparison
  ]

lean_lib ErdosProblems where
  srcDir := "third_party/plby/src/latest"
  globs := #[.submodules `ErdosProblems]

lean_lib PrimeNumberTheoremAnd where
  srcDir := "third_party/plby/src/latest"
  globs := #[.submodules `PrimeNumberTheoremAnd]

lean_lib UnitFractions where
  srcDir := "third_party/plby/src/latest"
  globs := #[.submodules `UnitFractions]

lean_lib Util where
  srcDir := "third_party/plby/src/latest"
  globs := #[.submodules `Util]

lean_lib BoundedGaps where
  srcDir := "third_party/formalpantheon/BoundedGaps"
  globs := #[.submodules `BoundedGaps]
