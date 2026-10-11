import SupportRestriction
import SubmatrixImage

namespace GlobalSupportBound
open scoped BigOperators
open FixedSignCapacity ResidueParityBridge SupportRestriction
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

/-- Reindexing the actual rectangular core gives nonzero actual column labels. -/
theorem reindexed_core_nonzero {k : ℕ} (hd : 0 < d)
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (r : Fin k ≃ nonzeroRows P d) (c : Fin k ≃ nonzeroColumns P d) :
    ∀ j, columnLabel ((core P d).submatrix r c) d j ≠ 0 := by
  intro j hj
  apply (mem_nonzeroColumns P d (c j).val).mp (c j).property
  ext i
  by_cases hi : i ∈ nonzeroRows P d
  · obtain ⟨a, ha⟩ := r.surjective ⟨i, hi⟩
    have hz := congrArg (fun v => (v : ResidueImage ((core P d).submatrix r c) d).val a) hj
    simpa only [columnLabel_apply, AddSubgroup.coe_zero, Pi.zero_apply,
      Matrix.submatrix_apply, core, ha, columnResidue] using hz
  · simp only [columnResidue, entry_zero_of_row_not_mem P d hd hcols i (c j) hi (c j).property,
      Int.cast_zero, Pi.zero_apply]

/-- Arbitrary integer orthogonal matrices: only the genuinely nonzero residue
columns are counted. The core and its comparison with the full image are proved. -/
theorem integer_nonzero_columns_bound (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    (nonzeroColumns P d).card ≤ 2 * Nat.card (ResidueImage P d) := by
  let k := (nonzeroColumns P d).card
  let r : Fin k ≃ nonzeroRows P d :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using
      (support_card_eq P d hd hrows hcols))).symm
  let c : Fin k ≃ nonzeroColumns P d :=
    (Fintype.equivFinOfCardEq (by simp only [Fintype.card_coe, k])).symm
  let Q := (core P d).submatrix r c
  have hQr : Q * Q.transpose = (d : ℤ)^2 • (1 : Matrix (Fin k) (Fin k) ℤ) := by
    change (core P d).submatrix r c * (core P d).transpose.submatrix c r = _
    rw [Matrix.submatrix_mul_equiv, core_row_gram P d hd hrows]
    simp only [Matrix.submatrix_smul, Pi.smul_apply, Matrix.submatrix_one_equiv]
  have hQc : Q.transpose * Q = (d : ℤ)^2 • (1 : Matrix (Fin k) (Fin k) ℤ) := by
    change (core P d).transpose.submatrix c r * (core P d).submatrix r c = _
    rw [Matrix.submatrix_mul_equiv, core_column_gram P d hd hcols]
    simp only [Matrix.submatrix_smul, Pi.smul_apply, Matrix.submatrix_one_equiv]
  have hb : k ≤ 2 * Nat.card (ResidueImage Q d) :=
    GeneralCoreBound.integer_core_bound Q d hd hQr hQc
      (reindexed_core_nonzero P d hd hcols r c)
  have himage : Nat.card (ResidueImage Q d) ≤ Nat.card (ResidueImage P d) :=
    SubmatrixImage.card_residueImage_submatrix_le P d hd
      (fun i => (r i).val) (fun j => (c j).val)
  exact hb.trans (Nat.mul_le_mul_left 2 himage)

/-- The arbitrary-matrix row bound is obtained from the proved equality of counts. -/
theorem integer_nonzero_rows_bound (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    (nonzeroRows P d).card ≤ 2 * Nat.card (ResidueImage P d) := by
  rw [support_card_eq P d hd hrows hcols]
  exact integer_nonzero_columns_bound P d hd hrows hcols

/-- Literal nonintegrality, with no denominator or residue model in the definition. -/
def nonintegralColumns (R : Matrix (Fin n) (Fin n) ℚ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ¬ ∃ z : Fin n → ℤ, ∀ i, R i j = (z i : ℚ))

def nonintegralRows (R : Matrix (Fin n) (Fin n) ℚ) : Finset (Fin n) :=
  nonintegralColumns R.transpose

/-- The actual denominator presentation identifies precisely the nonintegral columns. -/
theorem nonintegralColumns_eq (R : Matrix (Fin n) (Fin n) ℚ) (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) :
    nonintegralColumns R = nonzeroColumns P d := by
  ext j
  simp only [nonintegralColumns, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_nonzeroColumns]
  apply not_congr
  constructor
  · rintro ⟨z, hz⟩
    ext i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    refine ⟨z i, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hP, hz]
  · intro hz
    have hdiv : ∀ i, (d : ℤ) ∣ P i j := by
      intro i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hz i)
    choose z hz using hdiv
    refine ⟨z, ?_⟩
    intro i
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    apply mul_left_cancel₀ hdq
    rw [← hP i j, hz i]
    push_cast
    rfl

/-- Full global support theorem for every rational orthogonal matrix. No core,
index preservation, parity, or nonintegrality hypothesis is supplied. -/
theorem rational_global_support_bound (R : Matrix (Fin n) (Fin n) ℚ)
    (horth : R ∈ Matrix.orthogonalGroup (Fin n) ℚ) :
    (nonintegralRows R).card = (nonintegralColumns R).card ∧
    (nonintegralColumns R).card ≤
      2 * (RationalResidueConnection.coincidenceSubgroup R).index ∧
    (nonintegralRows R).card ≤
      2 * (RationalResidueConnection.coincidenceSubgroup R).index := by
  obtain ⟨d, hd, P, hP, _, hcols, hrows, hkernel⟩ :=
    RationalResidueConnection.exists_orthogonal_integer_presentation R horth
  have hec := nonintegralColumns_eq P d R hd hP
  have her : nonintegralRows R = nonzeroRows P d :=
    nonintegralColumns_eq P.transpose d R.transpose hd (fun i j => hP j i)
  rw [hec, her, hkernel, ← card_image_eq_index]
  exact ⟨support_card_eq P d hd hrows hcols,
    integer_nonzero_columns_bound P d hd hrows hcols,
    integer_nonzero_rows_bound P d hd hrows hcols⟩

end
end GlobalSupportBound
