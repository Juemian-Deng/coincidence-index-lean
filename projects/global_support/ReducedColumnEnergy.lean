import ResidueParityBridge
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace ReducedColumnEnergy
open ResidueParityBridge
open scoped BigOperators

noncomputable section
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) [NeZero d]

/-- The order is that of the selected actual column in the concrete image. -/
def columnOrder (j : Fin n) : ℕ := addOrderOf (columnLabel P d j)

/-- The scale uses the actual selected-column order, not the ambient exponent. -/
def columnScale (j : Fin n) : ℤ := (d / columnOrder P d j : ℕ)

/-- Division is performed entrywise on the original, un-oriented column. -/
def reducedColumn (j : Fin n) : Fin n → ℤ := fun i => P i j / columnScale P d j

theorem column_order_pos (j : Fin n) : 0 < columnOrder P d j :=
  addOrderOf_pos _

theorem column_order_dvd_level (j : Fin n) : columnOrder P d j ∣ d :=
  addOrderOf_dvd_iff_nsmul_eq_zero.mpr (image_annihilated P d _)

theorem column_scale_pos (j : Fin n) : 0 < columnScale P d j := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hh := column_order_pos P d j
  have hdiv := column_order_dvd_level P d j
  unfold columnScale
  exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hd hdiv) hh)

theorem level_eq_scale_mul_order (j : Fin n) :
    (d : ℤ) = columnScale P d j * (columnOrder P d j : ℤ) := by
  unfold columnScale
  exact_mod_cast (Nat.div_mul_cancel (column_order_dvd_level P d j)).symm

/-- Order annihilation gives divisibility of every actual matrix entry. -/
theorem column_scale_dvd_entry (j i : Fin n) : columnScale P d j ∣ P i j := by
  have hz := addOrderOf_nsmul_eq_zero (columnLabel P d j)
  have hi := congrArg (fun v : ResidueImage P d => v.val i) hz
  change columnOrder P d j • (columnLabel P d j).val i = 0 at hi
  rw [columnLabel_apply] at hi
  have hzero : (((columnOrder P d j : ℤ) * P i j : ℤ) : ZMod d) = 0 := by
    simpa only [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul] using hi
  have hdvd : (d : ℤ) ∣ (columnOrder P d j : ℤ) * P i j :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  rw [level_eq_scale_mul_order P d j, mul_comm (columnScale P d j)] at hdvd
  exact Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast (column_order_pos P d j).ne') hdvd

theorem original_column_eq_scale_mul_reduced (j i : Fin n) :
    P i j = columnScale P d j * reducedColumn P d j i := by
  exact (Int.mul_ediv_cancel' (column_scale_dvd_entry P d j i)).symm

/-- Scaling down exact integer energy introduces no inequality or rounding. -/
theorem scaled_outside_energy (j : Fin n) (I : Finset (Fin n)) :
    (∑ i ∈ Finset.univ \ I, P i j ^ 2) =
      columnScale P d j ^ 2 * (∑ i ∈ Finset.univ \ I, reducedColumn P d j i ^ 2) := by
  simp_rw [original_column_eq_scale_mul_reduced P d j, mul_pow]
  rw [Finset.mul_sum]

/-- The signed diagonal identity is used only to prove that the actual scale
also divides the positive own value. No sign change of the image is needed. -/
theorem column_scale_dvd_own_value (j r : Fin n) (s τ σ : ℤ)
    (hvalue : τ * (σ * P r j) = s - (d : ℤ)) : columnScale P d j ∣ s := by
  have hdvd : columnScale P d j ∣ τ * (σ * P r j) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (column_scale_dvd_entry P d j r) σ) τ
  rw [hvalue] at hdvd
  have hlevel : columnScale P d j ∣ (d : ℤ) :=
    ⟨(columnOrder P d j : ℤ), level_eq_scale_mul_order P d j⟩
  simpa using dvd_add hdvd hlevel

/-- Exact scaling of a proved positive own value and outside-energy identity. -/
theorem reduce_own_energy (j : Fin n) (I : Finset (Fin n)) (s : ℤ)
    (hs : 0 < s) (hdiv : columnScale P d j ∣ s)
    (hbound : (I.card : ℤ) * s ≤ 2 * (d : ℤ))
    (henergy : (∑ i ∈ Finset.univ \ I, P i j ^ 2) =
      2 * (d : ℤ) * s - (I.card : ℤ) * s ^ 2) :
    0 < s / columnScale P d j ∧
    (I.card : ℤ) * (s / columnScale P d j) ≤ 2 * (columnOrder P d j : ℤ) ∧
    (∑ i ∈ Finset.univ \ I, reducedColumn P d j i ^ 2) =
      2 * (columnOrder P d j : ℤ) * (s / columnScale P d j) -
        (I.card : ℤ) * (s / columnScale P d j) ^ 2 := by
  have hδ := column_scale_pos P d j
  have hs' : s = columnScale P d j * (s / columnScale P d j) :=
    (Int.mul_ediv_cancel' hdiv).symm
  refine ⟨Int.ediv_pos_of_pos_of_dvd hs hδ.le hdiv, ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ hδ).mp
    calc
      columnScale P d j * ((I.card : ℤ) * (s / columnScale P d j)) =
          (I.card : ℤ) * s := by
        conv_rhs => rw [hs']
        ring
      _ ≤ 2 * (d : ℤ) := hbound
      _ = columnScale P d j * (2 * (columnOrder P d j : ℤ)) := by
        rw [level_eq_scale_mul_order P d j]; ring
  · apply mul_left_cancel₀ (pow_ne_zero 2 hδ.ne')
    calc
      columnScale P d j ^ 2 * (∑ i ∈ Finset.univ \ I, reducedColumn P d j i ^ 2) =
          ∑ i ∈ Finset.univ \ I, P i j ^ 2 := (scaled_outside_energy P d j I).symm
      _ = 2 * (d : ℤ) * s - (I.card : ℤ) * s ^ 2 := henergy
      _ = columnScale P d j ^ 2 * (2 * (columnOrder P d j : ℤ) * (s / columnScale P d j) -
          (I.card : ℤ) * (s / columnScale P d j) ^ 2) := by
        conv_lhs => rw [level_eq_scale_mul_order P d j, hs']
        ring

end
end ReducedColumnEnergy
