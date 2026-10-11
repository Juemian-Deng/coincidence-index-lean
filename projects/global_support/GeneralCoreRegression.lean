import GeneralCoreBound
import RegressionChecks

namespace GeneralCoreRegression
open scoped BigOperators
open ResidueParityBridge FixedSignCapacity ActualFiberBounds
open EvenBoundRegression

/-- The order-two branch is used without any evenness input. -/
theorem four_columns_nonzero : ∀ j, columnLabel fourMatrix 2 j ≠ 0 := by
  intro j hz
  have h := congrArg (fun a : ResidueImage fourMatrix 2 => a.val j) hz
  simp only [columnLabel_apply, AddSubgroup.coe_zero, Pi.zero_apply, fourMatrix,
    ↓reduceIte] at h
  norm_num at h

theorem four_core_bound : 4 ≤ 2 * Nat.card (ResidueImage fourMatrix 2) := by
  apply GeneralCoreBound.integer_core_bound fourMatrix 2 (by decide)
  · simpa [fourMatrix_transpose] using fourMatrix_gram
  · exact fourMatrix_gram
  · exact four_columns_nonzero

theorem four_rational_nonintegral : GeneralCoreBound.NonintegralColumns fourRational := by
  intro j ⟨z, hz⟩
  have h := hz j
  simp only [fourRational, fourMatrix, ↓reduceIte, Int.cast_neg, Int.cast_one] at h
  have h' : (2 : ℚ) * (z j : ℚ) = -1 := by linarith
  have h'' : (2 : ℤ) * z j = -1 := by exact_mod_cast h'
  omega

theorem four_rational_core_bound :
    4 ≤ 2 * (RationalResidueConnection.coincidenceSubgroup fourRational).index :=
  GeneralCoreBound.rational_core_bound fourRational fourRational_orthogonal
    four_rational_nonintegral

/-- Sharp odd-index Householder numerator: the maximum class has six columns. -/
def sixMatrix : Matrix (Fin 6) (Fin 6) ℤ := fun i j => if i = j then 2 else -1

theorem six_transpose : sixMatrix.transpose = sixMatrix := by
  ext i j
  simp [sixMatrix, eq_comm]

theorem six_gram : sixMatrix.transpose * sixMatrix =
    (3 : ℤ)^2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem six_columns_nonzero : ∀ j, columnLabel sixMatrix 3 j ≠ 0 := by
  intro j hz
  have h := congrArg (fun a : ResidueImage sixMatrix 3 => a.val j) hz
  simp only [columnLabel_apply, AddSubgroup.coe_zero, Pi.zero_apply, sixMatrix,
    ↓reduceIte] at h
  exact (by decide : (2 : ZMod 3) ≠ 0) h

theorem six_core_bound : 6 ≤ 2 * Nat.card (ResidueImage sixMatrix 3) := by
  apply GeneralCoreBound.integer_core_bound sixMatrix 3 (by decide)
  · simpa [six_transpose] using six_gram
  · exact six_gram
  · exact six_columns_nonzero

/-- This core is outside the older even-kernel theorem's hypotheses. -/
theorem six_kernel_not_even : ¬ KernelEven sixMatrix 3 := by
  intro h
  let x : Fin 6 → ℤ := ![1, 1, 1, 0, 0, 0]
  have hker : ∀ i, (3 : ℤ) ∣ sixMatrix.mulVec x i := by
    intro i
    fin_cases i <;>
      norm_num [sixMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, x]
  have he := h x hker
  norm_num [x, Fin.sum_univ_succ] at he

/-- A free-small-class actual orthogonal numerator. -/
def rotationMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![3, -4; 4, 3]

theorem rotation_rows : rotationMatrix * rotationMatrix.transpose =
    (5 : ℤ)^2 • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rotation_cols : rotationMatrix.transpose * rotationMatrix =
    (5 : ℤ)^2 • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rotation_columns_nonfixed : ∀ j,
    columnLabel rotationMatrix 5 j ≠ -columnLabel rotationMatrix 5 j := by
  intro j hz
  have h := congrArg (fun a : ResidueImage rotationMatrix 5 => a.val j) hz
  simp only [columnLabel_apply, AddSubgroup.coe_neg, Pi.neg_apply] at h
  fin_cases j <;> norm_num [rotationMatrix] at h <;>
    exact (by decide : (3 : ZMod 5) ≠ -3) h

theorem rotation_core_bound : 2 ≤ 2 * Nat.card (ResidueImage rotationMatrix 5) := by
  apply GeneralSmallClassBound.bound_of_small_classes rotationMatrix 5 (by decide)
    rotation_rows rotation_cols
  · intro j hz
    apply rotation_columns_nonfixed j
    simp [hz]
  · intro j
    exact (Finset.card_le_univ _).trans (by simp)

/-- Empty dimension and denominator one remain legal. -/
theorem empty_core_bound : 0 ≤ 2 * Nat.card
    (ResidueImage (0 : Matrix (Fin 0) (Fin 0) ℤ) 1) := by
  apply GeneralCoreBound.integer_core_bound _ 1 (by decide)
  · ext i j; exact Fin.elim0 i
  · ext i j; exact Fin.elim0 i
  · intro j; exact Fin.elim0 j

end GeneralCoreRegression
