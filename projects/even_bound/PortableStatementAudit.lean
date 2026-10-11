import WrittenTheoremB
import RegressionChecks
import Lean

open scoped BigOperators

namespace IndependentStatementAudit

-- Fully expanded evenness and index conclusion: no alias conceals another lattice.
theorem expanded_written_statement {n : ℕ} (R : Matrix (Fin n) (Fin n) ℚ)
    (horth : R ∈ Matrix.orthogonalGroup (Fin n) ℚ)
    (heven : ∀ x : Fin n → ℤ,
      (∃ y : Fin n → ℤ, R.mulVec (fun i => (x i : ℚ)) = fun i => (y i : ℚ)) →
      Even (∑ i, (x i)^2)) :
    n ≤ 2 * Nat.card ((Fin n → ℤ) ⧸ RationalResidueConnection.coincidenceSubgroup R) := by
  simpa only [AddSubgroup.index_eq_card] using WrittenTheoremB.writtenTheoremB R horth heven

-- Rationality alone supplies finiteness, not an additional public premise.
theorem actual_index_positive {n : ℕ} (R : Matrix (Fin n) (Fin n) ℚ) :
    0 < (RationalResidueConnection.coincidenceSubgroup R).index := by
  let : Finite ((Fin n → ℤ) ⧸ RationalResidueConnection.coincidenceSubgroup R) :=
    RationalResidueConnection.finite_coincidence_quotient R
  rw [AddSubgroup.index_eq_card]
  exact Nat.card_pos

-- The dimension-zero case has index one, evenness holds, and the public result applies.
theorem empty_actual_even :
    RationalResidueConnection.CoincidenceEven (0 : Matrix (Fin 0) (Fin 0) ℚ) := by
  intro x _
  simp

theorem empty_actual_index :
    (RationalResidueConnection.coincidenceSubgroup (0 : Matrix (Fin 0) (Fin 0) ℚ)).index = 1 := by
  have hz : RationalResidueConnection.coincidenceSubgroup
      (0 : Matrix (Fin 0) (Fin 0) ℚ) = ⊤ := by
    ext x
    simp only [AddSubgroup.mem_top, iff_true]
    exact ⟨0, by ext i; exact Fin.elim0 i⟩
  simp [hz]

theorem empty_public_application :
    0 ≤ 2 * (RationalResidueConnection.coincidenceSubgroup
      (0 : Matrix (Fin 0) (Fin 0) ℚ)).index := by
  apply WrittenTheoremB.writtenTheoremB
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i
    exact Fin.elim0 i
  · exact empty_actual_even

end IndependentStatementAudit

#check @WrittenTheoremB.writtenTheoremB
#print axioms WrittenTheoremB.integer_even_bound
#print axioms WrittenTheoremB.integer_even_index_bound
#print axioms WrittenTheoremB.writtenTheoremB
#print axioms IndependentStatementAudit.expanded_written_statement
#print axioms IndependentStatementAudit.actual_index_positive
#print axioms IndependentStatementAudit.empty_public_application
#print axioms EvenBoundRegression.fourRational_orthogonal
#print axioms EvenBoundRegression.fourRational_coincidence_even
#print axioms EvenBoundRegression.fourRational_bound
#print axioms EvenBoundRegression.nonminimal_denominator_bound
#print RationalResidueConnection.CoincidenceEven
#print RationalResidueConnection.coincidenceSubgroup

open Lean Elab Command

-- Analysis only: this command reads stored kernel declarations and emits a graph.
-- It does not construct or accept any proof used by the delivered theorem.
private partial def auditVisit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for dep in ci.getUsedConstantsAsSet.toArray do
      auditVisit env dep

run_cmd do
  let env ← getEnv
  let root := `WrittenTheoremB.writtenTheoremB
  let deps := ((auditVisit env root).run {}).2
  logInfo m!"TRANSITIVE_CONSTANT_COUNT {deps.size}"
  let mut graph : Array String := #[]
  for n in deps.toArray.qsort Name.lt do
    if let some ci := env.find? n then
      graph := graph.push (n.toString ++ "\t" ++ String.intercalate " "
        ((ci.getUsedConstantsAsSet.toArray.qsort Name.lt).toList.map Name.toString))
    else
      graph := graph.push (n.toString ++ "\t[MISSING]")
  liftIO <| IO.FS.writeFile
    "full_kernel_dependency_graph.tsv"
    (String.intercalate "\n" graph.toList ++ "\n")
  for n in deps.toArray.qsort Name.lt do
    if n.toString.startsWith "DualFiberCounting." then
      logInfo m!"COUNTING_DEPENDENCY {n}"
    if let some ci := env.find? n then
      match ci with
      | .axiomInfo _ => logInfo m!"RECURSIVE_AXIOM {n}"
      | _ => pure ()
      if ci.isUnsafe then logInfo m!"UNSAFE_DEPENDENCY {n}"
      if ci.isPartial then logInfo m!"PARTIAL_DEPENDENCY {n}"
  for n in [ `WrittenTheoremB.writtenTheoremB, `WrittenTheoremB.integer_even_index_bound,
      `WrittenTheoremB.integer_even_bound, `ActualLargeClassBound.bound_from_reduced_column,
      `EvenSmallClassBound.even_bound_of_small_classes,
      `ReducedColumnEnergy.actual_sign_class_reduced_column,
      `RationalResidueConnection.exists_orthogonal_integer_presentation] do
    let some ci := env.find? n | throwError "Missing declaration {n}"
    logInfo m!"DIRECT_DEPENDENCIES {n}: {ci.getUsedConstantsAsSet.toArray.qsort Name.lt}"
