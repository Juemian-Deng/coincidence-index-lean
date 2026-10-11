import IntegerCoreSupport
import FreeInvolutionCapacity

/-! The two exhaustive small-class cases for an unrestricted orthogonal core. -/
namespace GeneralSmallClassBound
open scoped BigOperators
open ResidueParityBridge FixedSignCapacity ActualFiberBounds MatrixClassAdapters
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
noncomputable local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- An actual order-two column has four nonzero entries; all remaining rows
are nonzero characters in its annihilator, with actual class multiplicity four. -/
theorem bound_of_fixed_column (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hnonzero : ∀ j, columnLabel P d j ≠ 0)
    (hsmall : ∀ j, (signClass (columnLabel P d) j).card ≤ 4)
    (j : Fin n) (hfixed : columnLabel P d j = -columnLabel P d j) :
    n ≤ 2 * Nat.card (ResidueImage P d) := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hcore := IntegerCoreSupport.strict_core P d hd hcols hnonzero
  have hrowne := IntegerCoreSupport.rowEvaluation_ne_zero P d hd hrows hcore
  have hrowcap := row_evaluation_class_card_le P d 4 hd (by omega) hrows hsmall
  have hsupp := IntegerCoreSupport.fixed_column_support P d hd hcols hnonzero j hfixed
  have horder := IntegerCoreSupport.fixed_label_order P d j (hnonzero j) hfixed
  let q := Nat.card (AddMonoidHom.eval (columnLabel P d j) :
    (ResidueImage P d →+ ZMod d) →+ ZMod d).ker
  let : Finite (ResidueImage P d →+ ZMod d) :=
    Finite.of_injective (fun f : ResidueImage P d →+ ZMod d =>
      (f : ResidueImage P d → ZMod d)) DFunLike.coe_injective
  have hq : 0 < q := Nat.card_pos
  have hzero : (Finset.univ.filter (fun i => P i j = 0)).card ≤ 4 * (q - 1) := by
    have hb := zero_bin_card_le P d (fun i => P i j) j 1 4
      (by intro i; simp) hrowne hrowcap
    simpa only [abs_eq_zero] using hb
  have hpartition : (columnSupport P j).card +
      (Finset.univ.filter (fun i => P i j = 0)).card = n := by
    simpa only [columnSupport, not_not, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => P i j ≠ 0))
  have hcard : q * 2 = Nat.card (ResidueImage P d) := by
    simpa only [q, horder] using
      DualCardinality.card_eval_ker_mul_order d (columnLabel P d j) (image_annihilated P d)
  omega

/-- Complete unrestricted small-class branch. All hypotheses concern the actual
matrix. No parity character or small-class conclusion is a premise. -/
theorem bound_of_small_classes (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hnonzero : ∀ j, columnLabel P d j ≠ 0)
    (hsmall : ∀ j, (signClass (columnLabel P d) j).card ≤ 4) :
    n ≤ 2 * Nat.card (ResidueImage P d) := by
  classical
  let : NeZero d := ⟨by omega⟩
  by_cases hfixed : ∃ j, columnLabel P d j = -columnLabel P d j
  · obtain ⟨j, hj⟩ := hfixed
    exact bound_of_fixed_column P d hd hrows hcols hnonzero hsmall j hj
  · have hfree : ∀ j, columnLabel P d j ≠ -columnLabel P d j := by
      simpa only [not_exists] using hfixed
    simpa only [Fintype.card_fin] using
      FreeInvolutionCapacity.card_le_two_mul_natCard (columnLabel P d) hfree hsmall

end GeneralSmallClassBound
