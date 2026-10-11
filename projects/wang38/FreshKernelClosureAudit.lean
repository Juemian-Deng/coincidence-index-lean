import Wang38Full
import Lean

#print axioms Wang38.published_conjecture38I
#print axioms Wang38.published_conjecture38II
#print axioms Wang38.published_conjecture38

open Lean Elab Command
run_cmd do
  let ownModules : Array Name := #[`Wang38Targets, `InnerProduct, `SquareDimensionBound, `MatrixNumerator, `FrequencyInequality, `VectorFrequency, `MathlibBridge, `SwapArithmetic, `ExchangeLemma, `ResidueBlocks, `Wang38II, `PublishedStatement, `NormLift, `PrimeNeighbor, `Characteristic, `SelfDual, `LatticeBridge, `RankBridge, `SmallDimensions, `FrameOrientation, `FrameExtraction, `UniformConstruction, `BalancedReflection, `PrimeThree, `SourceNeighbor, `UnitSplitting, `ShortVectorBounds, `UnimodularGram, `CovolumeGram, `RootPairing, `RootComplement, `RootParityIndex, `RootDeterminant, `UnitOrNormFour, `IndexTwoStandard, `NormFourNeighbor, `RealUnitSplitting, `StandardTransport, `LowRankClassification, `RationalNeighborRealization, `Wang38Full, `FullAxiomAudit]
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut report : Array String := #["module\tdeclaration\taxioms"]
  for idx in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if ownModules.contains modName then
      let mut moduleCount : Nat := 0
      for n in env.header.moduleData[idx]!.constNames do
        let some ci := env.find? n | throwError "MISSING_DECLARATION {n}"
        if ci.isUnsafe then logInfo m!"LOCAL_RUNTIME_UNSAFE {n}"
        if ci.isPartial then logInfo m!"LOCAL_RUNTIME_PARTIAL {n}"
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
    "/workspace/scratch/ab284a076bfb/research/fresh_lean_verification_20261010/wang_both_replay/all_local_declaration_axioms_with_runtime_flags.tsv"
    (String.intercalate "\n" report.toList ++ "\n")

private partial def proofVisit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for dep in ci.getUsedConstantsAsSet.toArray do
      proofVisit env dep

run_cmd do
  let env ← getEnv
  let roots := #[`Wang38.published_conjecture38I,
    `Wang38.published_conjecture38II, `Wang38.published_conjecture38]
  let mut graph : Array String := #[]
  for root in roots do
    let deps := ((proofVisit env root).run {}).2
    logInfo m!"ENDPOINT_TRANSITIVE_CONSTANT_COUNT {root} {deps.size}"
    for n in deps.toArray.qsort Name.lt do
      let some ci := env.find? n | throwError "MISSING_PROOF_DEPENDENCY {n}"
      if ci.isUnsafe then throwError "UNSAFE_PROOF_DEPENDENCY {root}: {n}"
      if ci.isPartial then throwError "PARTIAL_PROOF_DEPENDENCY {root}: {n}"
      match ci with
      | .axiomInfo _ =>
        if n != `propext && n != `Classical.choice && n != `Quot.sound then
          throwError "CUSTOM_PROOF_AXIOM {root}: {n}"
        logInfo m!"ENDPOINT_RECURSIVE_AXIOM {root} {n}"
      | _ => pure ()
      graph := graph.push (root.toString ++ "\t" ++ n.toString ++ "\t" ++
        String.intercalate " " (ci.getUsedConstantsAsSet.toArray.qsort Name.lt |>.toList.map Name.toString))
    if deps.contains `Wang38.Frequency.sumN._unsafe_rec then
      throwError "SUMN_RUNTIME_AUXILIARY_USED_IN_PROOF {root}"
  liftIO <| IO.FS.writeFile "/workspace/scratch/ab284a076bfb/research/fresh_lean_verification_20261010/wang_both_replay/fresh_endpoint_kernel_dependency_graph.tsv"
    (String.intercalate "\n" graph.toList ++ "\n")
