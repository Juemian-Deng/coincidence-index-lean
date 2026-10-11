import GeneralCoreBound

namespace SupportRestriction
open scoped BigOperators
open FixedSignCapacity ResidueParityBridge
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

def nonzeroColumns : Finset (Fin n) :=
  Finset.univ.filter (fun j => columnResidue P d j ≠ 0)

def nonzeroRows : Finset (Fin n) := nonzeroColumns P.transpose d

@[simp] theorem mem_nonzeroColumns (j : Fin n) :
    j ∈ nonzeroColumns P d ↔ columnResidue P d j ≠ 0 := by
  simp [nonzeroColumns]

@[simp] theorem mem_nonzeroRows (i : Fin n) :
    i ∈ nonzeroRows P d ↔ columnResidue P.transpose d i ≠ 0 := by
  simp [nonzeroRows]

theorem strict_entry_of_nonzero_column (hd : 0 < d)
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (j : Fin n) (hj : j ∈ nonzeroColumns P d) (i : Fin n) :
    |P i j| < (d : ℤ) := by
  let Q : Fin n → Unit → ℤ := fun i _ => P i j
  have hnorm : ∀ u, ∑ i, Q i u ^ 2 = (d : ℤ)^2 :=
    fun _ => column_norm_of_gram P d hcols j
  have hne : ∀ u, columnResidue Q d u ≠ 0 := by
    intro u
    exact (mem_nonzeroColumns P d j).mp hj
  exact strict_core_of_nonzero_residue Q d hd hnorm hne i ()

theorem entry_zero_of_row_not_mem (hd : 0 < d)
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (i j : Fin n) (hi : i ∉ nonzeroRows P d) (hj : j ∈ nonzeroColumns P d) :
    P i j = 0 := by
  have hz : columnResidue P.transpose d i = 0 := by simpa using hi
  have hzj : (P i j : ZMod d) = 0 := congrFun hz j
  exact zero_of_dvd_of_abs_lt d (P i j) (by exact_mod_cast hd)
    (strict_entry_of_nonzero_column P d hd hcols j hj i)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzj)

theorem entry_zero_of_column_not_mem (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (i j : Fin n) (hi : i ∈ nonzeroRows P d) (hj : j ∉ nonzeroColumns P d) :
    P i j = 0 := by
  exact entry_zero_of_row_not_mem P.transpose d hd (by simpa using hrows) j i
    (by simpa [nonzeroRows] using hj) hi

/-- The submatrix uses exactly the actual nonzero residue rows and columns. -/
def core : Matrix (nonzeroRows P d) (nonzeroColumns P d) ℤ :=
  fun i j => P i j

theorem sum_subtype_eq_of_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (S : Finset α) (f : α → M) (hzero : ∀ a, a ∉ S → f a = 0) :
    ∑ a : S, f a = ∑ a, f a := by
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ S) (by intro a _ ha; exact hzero a ha)

theorem core_column_gram (hd : 0 < d)
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    (core P d).transpose * core P d =
      (d : ℤ)^2 • (1 : Matrix (nonzeroColumns P d) (nonzeroColumns P d) ℤ) := by
  ext j k
  have hg := congrFun (congrFun hcols j.val) k.val
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] at hg ⊢
  rw [show (∑ i, core P d i j * core P d i k) = ∑ i, P i j * P i k from
    sum_subtype_eq_of_zero (nonzeroRows P d) (fun i => P i j * P i k)
      (by intro i hi; rw [entry_zero_of_row_not_mem P d hd hcols i j hi j.property, zero_mul])]
  simpa only [Subtype.val_inj] using hg

theorem core_row_gram (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    core P d * (core P d).transpose =
      (d : ℤ)^2 • (1 : Matrix (nonzeroRows P d) (nonzeroRows P d) ℤ) := by
  ext i k
  have hg := congrFun (congrFun hrows i.val) k.val
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] at hg ⊢
  rw [show (∑ j, core P d i j * core P d k j) = ∑ j, P i j * P k j from
    sum_subtype_eq_of_zero (nonzeroColumns P d) (fun j => P i j * P k j)
      (by intro j hj; rw [entry_zero_of_column_not_mem P d hd hrows i j i.property hj, zero_mul])]
  simpa only [Subtype.val_inj] using hg

/-- Frobenius energy proves equality of the actual nonintegral row and column counts. -/
theorem support_card_eq (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    (nonzeroRows P d).card = (nonzeroColumns P d).card := by
  have hr := row_norm_of_gram (core P d) (d : ℤ) (core_row_gram P d hd hrows)
  have hc := column_norm_of_gram (core P d) (d : ℤ) (core_column_gram P d hd hcols)
  have he : ((nonzeroRows P d).card : ℤ) * (d : ℤ)^2 =
      ((nonzeroColumns P d).card : ℤ) * (d : ℤ)^2 := by
    calc
      _ = ∑ i : nonzeroRows P d, ∑ j : nonzeroColumns P d, (core P d i j)^2 := by simp only [hr, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ = ∑ j : nonzeroColumns P d, ∑ i : nonzeroRows P d, (core P d i j)^2 := Finset.sum_comm
      _ = _ := by simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hd2 : (d : ℤ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd.ne')
  exact_mod_cast mul_right_cancel₀ hd2 he

end
end SupportRestriction
