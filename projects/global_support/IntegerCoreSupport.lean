import MatrixClassAdapters

/-! Core consequences of genuine integer orthogonality, without lattice parity. -/
namespace IntegerCoreSupport
open scoped BigOperators
open ResidueParityBridge FixedSignCapacity ActualFiberBounds MatrixClassAdapters
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

/-- Nonzero actual column labels are precisely nonzero coordinate residue columns. -/
theorem columnLabel_ne_zero_iff (j : Fin n) :
    columnLabel P d j ≠ 0 ↔ columnResidue P d j ≠ 0 := by
  constructor
  · intro hn hz
    apply hn
    apply Subtype.ext
    simpa only [columnLabel_val_eq_columnResidue, AddSubgroup.coe_zero] using hz
  · intro hn hz
    apply hn
    simpa only [columnLabel_val_eq_columnResidue, AddSubgroup.coe_zero] using
      congrArg Subtype.val hz

/-- A matrix without integral columns has all numerator entries strictly below d. -/
theorem strict_core (hd : 0 < d)
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hnonzero : ∀ j, columnLabel P d j ≠ 0) :
    ∀ i j, |P i j| < (d : ℤ) := by
  exact strict_core_of_nonzero_residue P d hd (column_norm_of_gram P d hcols)
    (fun j => (columnLabel_ne_zero_iff P d j).mp (hnonzero j))

/-- Strict core entries and row norm exclude zero row characters. -/
theorem rowEvaluation_ne_zero (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcore : ∀ i j, |P i j| < (d : ℤ)) :
    ∀ i, rowEvaluation P d i ≠ 0 := by
  intro i hz
  have hz' := (rowEvaluation_eq_zero_iff P d i).mp hz
  have hall : ∀ j, P i j = 0 := by
    intro j
    exact zero_of_dvd_of_abs_lt d (P i j) (by exact_mod_cast hd) (hcore i j)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hz' j))
  have hnorm := row_norm_of_gram P d hrows i
  simp only [hall, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at hnorm
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  nlinarith

/-- Fixed negation of a nonzero actual column means additive order exactly two. -/
theorem fixed_label_order (j : Fin n) (hne : columnLabel P d j ≠ 0)
    (hfixed : columnLabel P d j = -columnLabel P d j) :
    addOrderOf (columnLabel P d j) = 2 := by
  apply addOrderOf_eq_prime
  · simpa only [two_nsmul] using (eq_neg_iff_add_eq_zero.mp hfixed)
  · exact hne

/-- The support of an actual fixed column is exactly four, with strictness derived. -/
theorem fixed_column_support (hd : 0 < d)
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hnonzero : ∀ j, columnLabel P d j ≠ 0) (j : Fin n)
    (hfixed : columnLabel P d j = -columnLabel P d j) :
    (columnSupport P j).card = 4 := by
  apply fixed_column_support_card P d (by exact_mod_cast hd) j
    (column_norm_of_gram P d hcols j) (fun i => strict_core P d hd hcols hnonzero i j)
  apply column_fixed_divisibility P d j
  simpa only [columnLabel_val_eq_columnResidue, AddSubgroup.coe_neg] using
    congrArg Subtype.val hfixed

end IntegerCoreSupport
