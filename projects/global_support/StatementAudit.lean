import GlobalSupportRegression
import Lean

open scoped BigOperators

namespace IndependentGlobalStatementAudit
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Independently expanded literal row and column predicates and quotient-cardinality index. -/
theorem expanded_statement {n : ℕ} (R : Matrix (Fin n) (Fin n) ℚ)
    (horth : R ∈ Matrix.orthogonalGroup (Fin n) ℚ) :
    (Finset.univ.filter (fun i => ¬ ∃ z : Fin n → ℤ, ∀ j, R i j = (z j : ℚ))).card =
      (Finset.univ.filter (fun j => ¬ ∃ z : Fin n → ℤ, ∀ i, R i j = (z i : ℚ))).card ∧
    (Finset.univ.filter (fun j => ¬ ∃ z : Fin n → ℤ, ∀ i, R i j = (z i : ℚ))).card ≤
      2 * Nat.card ((Fin n → ℤ) ⧸ RationalResidueConnection.coincidenceSubgroup R) ∧
    (Finset.univ.filter (fun i => ¬ ∃ z : Fin n → ℤ, ∀ j, R i j = (z j : ℚ))).card ≤
      2 * Nat.card ((Fin n → ℤ) ⧸ RationalResidueConnection.coincidenceSubgroup R) := by
  classical
  simpa [GlobalSupportBound.nonintegralRows, GlobalSupportBound.nonintegralColumns,
    Matrix.transpose_apply, AddSubgroup.index_eq_card] using
    GlobalSupportBound.rational_global_support_bound R horth

theorem actual_subgroup_membership {n : ℕ} (R : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℤ) :
    x ∈ RationalResidueConnection.coincidenceSubgroup R ↔
      ∃ y : Fin n → ℤ, R.mulVec (fun i => (x i : ℚ)) = fun i => (y i : ℚ) := Iff.rfl

theorem actual_index_positive {n : ℕ} (R : Matrix (Fin n) (Fin n) ℚ) :
    0 < (RationalResidueConnection.coincidenceSubgroup R).index := by
  let : Finite ((Fin n → ℤ) ⧸ RationalResidueConnection.coincidenceSubgroup R) :=
    RationalResidueConnection.finite_coincidence_quotient R
  rw [AddSubgroup.index_eq_card]
  exact Nat.card_pos

theorem identity_index (n : ℕ) :
    (RationalResidueConnection.coincidenceSubgroup (1 : Matrix (Fin n) (Fin n) ℚ)).index = 1 := by
  have ht : RationalResidueConnection.coincidenceSubgroup
      (1 : Matrix (Fin n) (Fin n) ℚ) = ⊤ := by
    ext x
    simp only [AddSubgroup.mem_top, iff_true]
    exact ⟨x, by simp⟩
  simp [ht]

theorem empty_index :
    (RationalResidueConnection.coincidenceSubgroup (1 : Matrix (Fin 0) (Fin 0) ℚ)).index = 1 :=
  identity_index 0

/-- The integral tail itself witnesses that the mixed example is outside the even case. -/
theorem mixed_actual_kernel_not_even :
    ¬ RationalResidueConnection.CoincidenceEven GlobalSupportRegression.mixedRational := by
  intro he
  let x : Fin 4 → ℤ := ![0, 0, 1, 0]
  have hx : x ∈ RationalResidueConnection.coincidenceSubgroup GlobalSupportRegression.mixedRational := by
    refine ⟨x, ?_⟩
    ext i
    fin_cases i <;> norm_num [GlobalSupportRegression.mixedRational,
      GlobalSupportRegression.mixedNumerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, x]
  have h := he x hx
  norm_num [x, Fin.sum_univ_succ] at h

/-- Explicit application of the new public endpoint to this non-even, mixed matrix. -/
theorem mixed_non_even_public_application :
    ¬ RationalResidueConnection.CoincidenceEven GlobalSupportRegression.mixedRational ∧
    (GlobalSupportBound.nonintegralRows GlobalSupportRegression.mixedRational).card =
      (GlobalSupportBound.nonintegralColumns GlobalSupportRegression.mixedRational).card ∧
    (GlobalSupportBound.nonintegralColumns GlobalSupportRegression.mixedRational).card ≤
      2 * (RationalResidueConnection.coincidenceSubgroup GlobalSupportRegression.mixedRational).index ∧
    (GlobalSupportBound.nonintegralRows GlobalSupportRegression.mixedRational).card ≤
      2 * (RationalResidueConnection.coincidenceSubgroup GlobalSupportRegression.mixedRational).index :=
  ⟨mixed_actual_kernel_not_even,
    GlobalSupportBound.rational_global_support_bound _ GlobalSupportRegression.mixed_rational_orthogonal⟩

end
end IndependentGlobalStatementAudit

#check @GlobalSupportBound.rational_global_support_bound
#print GlobalSupportBound.nonintegralColumns
#print GlobalSupportBound.nonintegralRows
#print RationalResidueConnection.coincidenceSubgroup
#print axioms GlobalSupportBound.rational_global_support_bound
#print axioms IndependentGlobalStatementAudit.expanded_statement
#print axioms IndependentGlobalStatementAudit.actual_index_positive
#print axioms IndependentGlobalStatementAudit.identity_index
#print axioms IndependentGlobalStatementAudit.mixed_non_even_public_application
#print axioms GeneralCoreRegression.six_kernel_not_even

open Lean Elab Command

-- This reporting procedure only inspects accepted declarations. It contributes no proof.
private partial def auditVisit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for dep in ci.getUsedConstantsAsSet.toArray do
      auditVisit env dep

run_cmd do
  let env ← getEnv
  let root := `GlobalSupportBound.rational_global_support_bound
  let deps := ((auditVisit env root).run {}).2
  logInfo m!"TRANSITIVE_CONSTANT_COUNT {deps.size}"
  let mut graph : Array String := #[]
  for n in deps.toArray.qsort Name.lt do
    if let some ci := env.find? n then
      graph := graph.push (n.toString ++ "\t" ++ String.intercalate " "
        ((ci.getUsedConstantsAsSet.toArray.qsort Name.lt).toList.map Name.toString))
      match ci with
      | .axiomInfo _ => logInfo m!"RECURSIVE_AXIOM {n}"
      | _ => pure ()
      if ci.isUnsafe then throwError "UNSAFE_DEPENDENCY {n}"
      if ci.isPartial then throwError "PARTIAL_DEPENDENCY {n}"
    else
      throwError "MISSING_DEPENDENCY {n}"
  liftIO <| IO.FS.writeFile
    "/workspace/scratch/ab284a076bfb/research/fresh_lean_verification_20261010/global_support_replay/full_kernel_dependency_graph.tsv"
    (String.intercalate "\n" graph.toList ++ "\n")
  for n in [ `GlobalSupportBound.rational_global_support_bound,
      `GlobalSupportBound.integer_nonzero_columns_bound,
      `SupportRestriction.support_card_eq,
      `SubmatrixImage.card_residueImage_submatrix_le,
      `GeneralCoreBound.integer_core_bound,
      `GeneralSmallClassBound.bound_of_small_classes,
      `GeneralSmallClassBound.bound_of_fixed_column,
      `FreeInvolutionCapacity.card_le_two_mul_natCard,
      `ActualLargeClassBound.bound_from_reduced_column,
      `RationalResidueConnection.exists_orthogonal_integer_presentation] do
    let some ci := env.find? n | throwError "Missing declaration {n}"
    if !deps.contains n then throwError "REQUIRED_DEPENDENCY_UNUSED {n}"
    logInfo m!"DIRECT_DEPENDENCIES {n}: {ci.getUsedConstantsAsSet.toArray.qsort Name.lt}"
