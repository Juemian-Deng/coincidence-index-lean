import ReducedColumnEnergy
import SignClassTransfer

set_option linter.unusedSectionVars false

namespace ReducedColumnEnergy
open ResidueParityBridge FixedSignCapacity SignClassTransfer IntegerNormTwo MatrixLargeClass
open scoped BigOperators

noncomputable section
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) [NeZero d]

/-- A genuine nonzero actual sign class supplies a reduced original column,
a matched row block of the same size, the sharp linear budget, and exact
outside energy. Divisibility, energy and normal form are all derived. -/
theorem actual_sign_class_reduced_column
    (ho : OrthogonalColumns P (d : ℤ))
    (J : Finset (Fin n)) (hfive : 5 ≤ J.card) (j : J)
    (hg : columnLabel P d j ≠ 0)
    (hc : ∀ k ∈ J, columnResidue P d k = columnResidue P d j ∨
      columnResidue P d k = -columnResidue P d j) :
    ∃ (I : Finset (Fin n)) (w : Fin n → ℤ) (δ a : ℤ),
      I.card = J.card ∧ 0 < δ ∧ 0 < a ∧
      δ = columnScale P d j ∧ w = reducedColumn P d j ∧
      (∀ i, P i j = δ * w i) ∧
      (I.card : ℤ) * a ≤ 2 * (addOrderOf (columnLabel P d j) : ℤ) ∧
      (∑ i ∈ Finset.univ \ I, w i ^ 2) =
        2 * (addOrderOf (columnLabel P d j) : ℤ) * a - (I.card : ℤ) * a ^ 2 := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hg' : columnResidue P d j ≠ 0 := by
    intro hz
    apply hg
    apply Subtype.ext
    ext i
    change (columnLabel P d j).val i = 0
    rw [columnLabel_apply]
    exact congrFun hz i
  obtain ⟨σ, τ, L, row, s, hσ, hτ, hr, hp, hs, _, hv, _, hbound, _⟩ :=
    finite_nonzero_sign_class_normal_form P d hd ho J hfive (columnResidue P d j) hg' hc
  let I : Finset (Fin n) := Finset.univ.image row
  have hI : I.card = J.card := by
    dsimp [I]
    rw [Finset.card_image_of_injective _ hr]
    simp
  have hvalue : τ (row j) * (σ j * P (row j) j) = s - (d : ℤ) := by
    simpa [hv, unitVector] using hp j (row j)
  have hdiv := column_scale_dvd_own_value P d j (row j) s (τ (row j)) (σ j) hvalue
  have hb : (I.card : ℤ) * s ≤ 2 * (d : ℤ) := by simpa only [hI] using hbound
  have he : (∑ i ∈ Finset.univ \ I, P i j ^ 2) =
      2 * (d : ℤ) * s - (I.card : ℤ) * s ^ 2 := by
    rw [hI]
    exact original_outside_block_energy P d s ho J σ τ L row hσ hτ hr hv hp j
  obtain ⟨ha, hbudget, henergy⟩ := reduce_own_energy P d j I s hs hdiv hb he
  exact ⟨I, reducedColumn P d j, columnScale P d j, s / columnScale P d j,
    hI, column_scale_pos P d j, ha, rfl, rfl,
    original_column_eq_scale_mul_reduced P d j, hbudget, henergy⟩

end
end ReducedColumnEnergy
