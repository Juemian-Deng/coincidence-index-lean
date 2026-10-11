import EvenSmallClassBound
import ActualLargeClassBound
import MaximumClass
import WrittenTheoremB
import Mathlib.Tactic.FinCases

namespace EvenBoundRegression
open scoped BigOperators
open ResidueParityBridge ActualFiberBounds

def fourMatrix : Matrix (Fin 4) (Fin 4) ℤ := fun i j => if i = j then -1 else 1

theorem fourMatrix_transpose : fourMatrix.transpose = fourMatrix := by
  ext i j
  simp [fourMatrix, eq_comm]

theorem fourMatrix_gram : fourMatrix.transpose * fourMatrix =
    (2 : ℤ)^2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem fourMatrix_kernel_even : KernelEven fourMatrix 2 := by
  intro x hx
  have h := hx 0
  rw [even_iff_two_dvd]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, fourMatrix] at h ⊢
  norm_num at h ⊢
  omega

theorem fourMatrix_bound : 4 ≤ 2 * Nat.card (ResidueImage fourMatrix 2) := by
  apply EvenSmallClassBound.even_bound_of_small_classes fourMatrix 2 (by decide)
  · simpa [fourMatrix_transpose] using fourMatrix_gram
  · exact fourMatrix_gram
  · exact fourMatrix_kernel_even
  · intro j
    exact (Finset.card_le_univ _).trans (by simp)

/-- The actual-bound statement also covers zero dimension without asserting
an odd coset exists in that case. -/
theorem empty_matrix_bound : 0 ≤ 2 * Nat.card
    (ResidueImage (0 : Matrix (Fin 0) (Fin 0) ℤ) 1) := by omega

/-- Empty character fibers are harmless, even for a scalar that cannot occur. -/
theorem empty_dual_fiber :
    Nat.card {f : ZMod 2 →+ ZMod 4 // f 0 = 1} = 0 := by
  have : IsEmpty {f : ZMod 2 →+ ZMod 4 // f 0 = 1} := ⟨by
    intro f
    have h := f.property
    rw [map_zero] at h
    exact (by decide : (0 : ZMod 4) ≠ 1) h⟩
  exact Nat.card_of_isEmpty

/-- Regression through the unconditional actual integer boundary theorem. -/
theorem fourMatrix_final_bound : 4 ≤ 2 * Nat.card (ResidueImage fourMatrix 2) := by
  apply WrittenTheoremB.integer_even_bound fourMatrix 2 (by decide)
  · simpa [fourMatrix_transpose] using fourMatrix_gram
  · exact fourMatrix_gram
  · exact fourMatrix_kernel_even

/-- The final theorem permits positive nonminimal denominators. -/
theorem doubled_fourMatrix_kernel_even : KernelEven ((2 : ℤ) • fourMatrix) 4 := by
  intro x hx
  apply fourMatrix_kernel_even x
  intro i
  have h := hx i
  change (4 : ℤ) ∣ ((2 : ℤ) • fourMatrix).mulVec x i at h
  rw [Matrix.smul_mulVec] at h
  change (4 : ℤ) ∣ 2 * fourMatrix.mulVec x i at h
  omega

theorem doubled_fourMatrix_gram : ((2 : ℤ) • fourMatrix).transpose * ((2 : ℤ) • fourMatrix) =
    (4 : ℤ)^2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [fourMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem nonminimal_denominator_bound :
    4 ≤ 2 * Nat.card (ResidueImage ((2 : ℤ) • fourMatrix) 4) := by
  apply WrittenTheoremB.integer_even_bound ((2 : ℤ) • fourMatrix) 4 (by decide)
  · simpa only [Matrix.transpose_smul, fourMatrix_transpose, Nat.cast_ofNat] using doubled_fourMatrix_gram
  · exact doubled_fourMatrix_gram
  · exact doubled_fourMatrix_kernel_even

def fourRational : Matrix (Fin 4) (Fin 4) ℚ := fun i j => (fourMatrix i j : ℚ) / 2

theorem fourRational_orthogonal : fourRational ∈ Matrix.orthogonalGroup (Fin 4) ℚ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourRational, fourMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem fourRational_coincidence_even : RationalResidueConnection.CoincidenceEven fourRational := by
  apply (RationalResidueConnection.coincidenceEven_iff_kernelEven
    fourRational fourMatrix 2 (by decide) ?_).mpr fourMatrix_kernel_even
  intro i j
  dsimp [fourRational]
  ring

theorem fourRational_bound :
    4 ≤ 2 * (RationalResidueConnection.coincidenceSubgroup fourRational).index :=
  WrittenTheoremB.writtenTheoremB fourRational fourRational_orthogonal fourRational_coincidence_even

end EvenBoundRegression
