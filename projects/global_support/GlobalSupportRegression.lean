import GlobalSupportBound
import GeneralCoreRegression

namespace GlobalSupportRegression
open scoped BigOperators
open SupportRestriction GlobalSupportBound ResidueParityBridge

/-- A rotation block with both positive and negative integral-coordinate tails. -/
def mixedNumerator : Matrix (Fin 4) (Fin 4) ℤ :=
  !![3, -4, 0, 0; 4, 3, 0, 0; 0, 0, 5, 0; 0, 0, 0, -5]

theorem mixed_rows : mixedNumerator * mixedNumerator.transpose =
    (5 : ℤ)^2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedNumerator, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixed_columns : mixedNumerator.transpose * mixedNumerator =
    (5 : ℤ)^2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedNumerator, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixed_support : nonzeroColumns mixedNumerator 5 = {0, 1} := by
  ext j
  fin_cases j <;>
    norm_num [nonzeroColumns, FixedSignCapacity.columnResidue, funext_iff,
      Fin.forall_fin_succ, mixedNumerator] <;> decide

theorem mixed_integer_bound : 2 ≤ 2 * Nat.card (ResidueImage mixedNumerator 5) := by
  have h := integer_nonzero_columns_bound mixedNumerator 5 (by decide) mixed_rows mixed_columns
  simpa [mixed_support] using h

def mixedRational : Matrix (Fin 4) (Fin 4) ℚ := fun i j => (mixedNumerator i j : ℚ) / 5

theorem mixed_rational_orthogonal : mixedRational ∈ Matrix.orthogonalGroup (Fin 4) ℚ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mixedRational, mixedNumerator, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixed_rational_columns : (nonintegralColumns mixedRational).card = 2 := by
  rw [nonintegralColumns_eq mixedNumerator 5 mixedRational (by decide)
    (by intro i j; dsimp [mixedRational]; ring), mixed_support]
  decide

theorem mixed_rational_global_bound :
    (nonintegralRows mixedRational).card = 2 ∧
    2 ≤ 2 * (RationalResidueConnection.coincidenceSubgroup mixedRational).index := by
  obtain ⟨he, hb, _⟩ := rational_global_support_bound mixedRational mixed_rational_orthogonal
  rw [mixed_rational_columns] at he hb
  exact ⟨he, hb⟩

/-- Entirely integral orthogonal matrices are included, with support zero. -/
theorem identity_support (n : ℕ) :
    nonintegralColumns (1 : Matrix (Fin n) (Fin n) ℚ) = ∅ := by
  classical
  ext j
  simp only [nonintegralColumns, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_not]
  refine ⟨fun i => if i = j then 1 else 0, ?_⟩
  intro i
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem identity_global_bound (n : ℕ) :
    (nonintegralRows (1 : Matrix (Fin n) (Fin n) ℚ)).card = 0 ∧
    0 ≤ 2 * (RationalResidueConnection.coincidenceSubgroup
      (1 : Matrix (Fin n) (Fin n) ℚ)).index := by
  have h := rational_global_support_bound (1 : Matrix (Fin n) (Fin n) ℚ)
    (Matrix.orthogonalGroup (Fin n) ℚ).one_mem
  constructor
  · simpa only [identity_support, Finset.card_empty] using h.1
  · exact Nat.zero_le _

/-- Empty dimension needs no separate nonemptiness premise. -/
theorem empty_global_bound :
    (nonintegralColumns (1 : Matrix (Fin 0) (Fin 0) ℚ)).card ≤
      2 * (RationalResidueConnection.coincidenceSubgroup
        (1 : Matrix (Fin 0) (Fin 0) ℚ)).index :=
  (rational_global_support_bound _ (Matrix.orthogonalGroup (Fin 0) ℚ).one_mem).2.1

end GlobalSupportRegression
