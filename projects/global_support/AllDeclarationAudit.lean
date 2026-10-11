import GlobalSupportRegression
import Lean

open Lean Elab Command

run_cmd do
  let ownModules : Array Name := #[`ResidueParityBridge, `DualCardinality, `DualFiberCounting, `ActualFiberBounds, `IntegerEvenCore, `ActualLargeClassBound, `ReducedColumnEnergy, `IntegerNormTwo, `CommonEndpoint, `NormTwoStar, `MatrixLargeClass, `OwnBlockEnergy, `FiniteClassBridge, `FiniteClassRows, `FixedSignCapacity, `SignClassTransfer, `ActualSignClassReduction, `ResidueImageAdapter, `EvenSmallClassBound, `FreeInvolutionCapacity, `MatrixClassAdapters, `IntegerCoreSupport, `GeneralSmallClassBound, `RationalResidueConnection, `OrthogonalPresentation, `GeneralCoreBound, `MaximumClass, `WrittenTheoremB, `RegressionChecks, `GeneralCoreRegression, `SupportRestriction, `SubmatrixImage, `GlobalSupportBound, `GlobalSupportRegression]
  let env ← getEnv
  liftIO <| IO.FS.writeFile
    "/workspace/scratch/ab284a076bfb/research/fresh_lean_verification_20261010/global_support_replay/imported_modules.txt"
    (String.intercalate "\n" (env.header.moduleNames.toList.map Name.toString) ++ "\n")
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut report : Array String := #["module\tdeclaration\taxioms"]
  for idx in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if ownModules.contains modName then
      let mut moduleCount : Nat := 0
      for n in env.header.moduleData[idx]!.constNames do
        let some ci := env.find? n | throwError "MISSING_DECLARATION {n}"
        if ci.isUnsafe then throwError "UNSAFE_LOCAL_DECLARATION {n}"
        if ci.isPartial then throwError "PARTIAL_LOCAL_DECLARATION {n}"
        match ci with
        | .axiomInfo _ => throwError "CUSTOM_AXIOM {n}"
        | _ => pure ()
        let axioms ← collectAxioms n
        for ax in axioms do
          if !allowed.contains ax then throwError "FORBIDDEN_AXIOM {n}: {ax}"
        report := report.push (modName.toString ++ "\t" ++ n.toString ++ "\t" ++
          String.intercalate " " (axioms.qsort Name.lt |>.toList.map Name.toString))
        count := count + 1
        moduleCount := moduleCount + 1
      logInfo m!"MODULE_DECLARATIONS {modName}: {moduleCount}"
  logInfo m!"ALL_LOCAL_DECLARATIONS {count}"
  liftIO <| IO.FS.writeFile
    "/workspace/scratch/ab284a076bfb/research/fresh_lean_verification_20261010/global_support_replay/all_local_declaration_axioms.tsv"
    (String.intercalate "\n" report.toList ++ "\n")
