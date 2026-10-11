import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Fixed-negation residue classes of an actual integer orthogonal core have
at most four columns. Only the diagonal Gram identities are needed. -/
set_option linter.unusedSectionVars false

namespace FixedSignCapacity
open scoped BigOperators

/-- A core entry divisible by the positive denominator is zero. -/
theorem zero_of_dvd_of_abs_lt (d x : ℤ) (hd : 0 < d)
    (hx : |x| < d) (hdiv : d ∣ x) : x = 0 := by
  obtain ⟨k, hk⟩ := hdiv
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
  have hklo : -1 < k := by nlinarith
  have hkhi : k < 1 := by nlinarith
  have : k = 0 := by omega
  simp [this] at hk
  exact hk

/-- Fixed negation forces a core entry to be zero or a signed half-denominator. -/
theorem fixed_entry_trichotomy (d x : ℤ) (hd : 0 < d)
    (hx : |x| < d) (hfixed : d ∣ 2 * x) :
    x = 0 ∨ 2 * x = d ∨ 2 * x = -d := by
  obtain ⟨k, hk⟩ := hfixed
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
  have hklo : -2 < k := by nlinarith
  have hkhi : k < 2 := by nlinarith
  have : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases this with h | h | h
  · right; right; nlinarith
  · left; nlinarith
  · right; left; nlinarith

/-- The squared magnitude of a nonzero fixed entry is exactly d²/4. -/
theorem fixed_entry_square (d x : ℤ) (hd : 0 < d)
    (hx : |x| < d) (hfixed : d ∣ 2 * x) (hne : x ≠ 0) :
    4 * x ^ 2 = d ^ 2 := by
  rcases fixed_entry_trichotomy d x hd hx hfixed with h | h | h
  · exact (hne h).elim
  · nlinarith [sq_nonneg (2*x-d)]
  · nlinarith [sq_nonneg (2*x+d)]

/-- Equality up to sign modulo d preserves zero coordinates in the core. -/
theorem same_residue_zero_iff (d x y : ℤ) (hd : 0 < d)
    (hx : |x| < d) (hy : |y| < d)
    (hres : d ∣ x - y ∨ d ∣ x + y) : x = 0 ↔ y = 0 := by
  constructor
  · intro h
    apply zero_of_dvd_of_abs_lt d y hd hy
    rcases hres with hr | hr
    · simpa [h] using (dvd_neg.mpr hr)
    · simpa [h] using hr
  · intro h
    apply zero_of_dvd_of_abs_lt d x hd hx
    rcases hres with hr | hr <;> simpa [h] using hr

/-- Fixed negation transports across equality up to sign of residues. -/
theorem fixed_of_same_residue (d x y : ℤ) (hy : d ∣ 2 * y)
    (hres : d ∣ x - y ∨ d ∣ x + y) : d ∣ 2 * x := by
  obtain ⟨b, hb⟩ := hy
  rcases hres with hr | hr
  · obtain ⟨a, ha⟩ := hr
    exact ⟨2 * a + b, by nlinarith⟩
  · obtain ⟨a, ha⟩ := hr
    exact ⟨2 * a - b, by nlinarith⟩

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Actual support of an integer column. -/
def columnSupport (P : α → β → ℤ) (j : β) : Finset α :=
  Finset.univ.filter (fun i => P i j ≠ 0)

@[simp] theorem mem_columnSupport (P : α → β → ℤ) (j : β) (i : α) :
    i ∈ columnSupport P j ↔ P i j ≠ 0 := by simp [columnSupport]

/-- Every fixed column of squared norm d² in the strict core has four entries. -/
theorem fixed_column_support_card (P : α → β → ℤ) (d : ℤ) (hd : 0 < d)
    (j : β) (hnorm : ∑ i, P i j ^ 2 = d ^ 2)
    (hcore : ∀ i, |P i j| < d) (hfixed : ∀ i, d ∣ 2 * P i j) :
    (columnSupport P j).card = 4 := by
  have hsum : (∑ i ∈ columnSupport P j, d ^ 2) = 4 * ∑ i, P i j ^ 2 := by
    rw [columnSupport, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : P i j = 0
    · simp [hi]
    · simpa [hi] using (fixed_entry_square d (P i j) hd (hcore i) (hfixed i) hi).symm
  have hc : ((columnSupport P j).card : ℤ) * d ^ 2 = 4 * d ^ 2 := by
    simpa [hnorm] using hsum
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hd)
  have : ((columnSupport P j).card : ℤ) = 4 := mul_right_cancel₀ hd2 hc
  exact_mod_cast this

/-- Congruent columns up to sign have the same actual support in the core. -/
theorem same_residue_column_support (P : α → β → ℤ) (d : ℤ) (hd : 0 < d)
    (j k : β) (hcore : ∀ i c, |P i c| < d)
    (hres : (∀ i, d ∣ P i j - P i k) ∨ (∀ i, d ∣ P i j + P i k)) :
    columnSupport P j = columnSupport P k := by
  ext i
  simp only [mem_columnSupport]
  apply not_congr
  apply same_residue_zero_iff d (P i j) (P i k) hd (hcore i j) (hcore i k)
  rcases hres with h | h
  · exact Or.inl (h i)
  · exact Or.inr (h i)

/-- A nonzero fixed class has capacity four, directly from one row's norm budget.
There is no input cardinality bound and no rank or dimension assumption. -/
theorem fixed_class_card_le_four (P : α → β → ℤ) (d : ℤ) (hd : 0 < d)
    (C : Finset β) (j₀ : β)
    (hcol : ∑ i, P i j₀ ^ 2 = d ^ 2)
    (hrow : ∀ i, ∑ j, P i j ^ 2 = d ^ 2)
    (hcore : ∀ i j, |P i j| < d)
    (hfixed : ∀ i, d ∣ 2 * P i j₀)
    (hclass : ∀ j ∈ C,
      (∀ i, d ∣ P i j - P i j₀) ∨ (∀ i, d ∣ P i j + P i j₀)) :
    C.card ≤ 4 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, P i j₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑ i, P i j₀ ^ 2 = 0 := by simp [h]
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    omega
  have hentries : ∀ j ∈ C, 4 * P i j ^ 2 = d ^ 2 := by
    intro j hj
    have hr : d ∣ P i j - P i j₀ ∨ d ∣ P i j + P i j₀ := by
      rcases hclass j hj with h | h
      · exact Or.inl (h i)
      · exact Or.inr (h i)
    apply fixed_entry_square d (P i j) hd (hcore i j)
    · exact fixed_of_same_residue d (P i j) (P i j₀) (hfixed i) hr
    · exact fun h => hi ((same_residue_zero_iff d _ _ hd
        (hcore i j) (hcore i j₀) hr).mp h)
  have hbudget : ∑ j ∈ C, P i j ^ 2 ≤ d ^ 2 := by
    calc (∑ j ∈ C, P i j ^ 2) ≤ ∑ j, P i j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (fun j _ _ => sq_nonneg (P i j))
    _ = d ^ 2 := hrow i
  have hsum : (C.card : ℤ) * d ^ 2 = 4 * ∑ j ∈ C, P i j ^ 2 := by
    rw [Finset.mul_sum]
    calc (C.card : ℤ) * d ^ 2 = ∑ j ∈ C, d ^ 2 := by simp
    _ = ∑ j ∈ C, 4 * P i j ^ 2 := Finset.sum_congr rfl (fun j hj => (hentries j hj).symm)
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have : (C.card : ℤ) ≤ 4 := by nlinarith
  exact_mod_cast this

/-- The actual column after entrywise reduction modulo the denominator. -/
def columnResidue (P : α → β → ℤ) (d : ℕ) (j : β) : α → ZMod d :=
  fun i => (P i j : ZMod d)

/-- A whole-column common-sign class, not independent coordinate signs. -/
def absoluteClass (P : α → β → ℤ) (d : ℕ) (j₀ : β) : Finset β :=
  Finset.univ.filter (fun j => columnResidue P d j = columnResidue P d j₀ ∨
    columnResidue P d j = -columnResidue P d j₀)

theorem column_fixed_divisibility (P : α → β → ℤ) (d : ℕ) (j : β)
    (hfixed : columnResidue P d j = -columnResidue P d j) :
    ∀ i, (d : ℤ) ∣ 2 * P i j := by
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hi := congrFun hfixed i
  change (P i j : ZMod d) = -(P i j : ZMod d) at hi
  push_cast
  rw [two_mul]
  exact eq_neg_iff_add_eq_zero.mp hi

theorem column_same_residue_divisibility (P : α → β → ℤ) (d : ℕ) (j k : β)
    (hres : columnResidue P d j = columnResidue P d k ∨
      columnResidue P d j = -columnResidue P d k) :
    (∀ i, (d : ℤ) ∣ P i j - P i k) ∨ (∀ i, (d : ℤ) ∣ P i j + P i k) := by
  rcases hres with h | h
  · left
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hi := congrFun h i
    change (P i j : ZMod d) = (P i k : ZMod d) at hi
    push_cast
    exact sub_eq_zero.mpr hi
  · right
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hi := congrFun h i
    change (P i j : ZMod d) = -(P i k : ZMod d) at hi
    push_cast
    exact eq_neg_iff_add_eq_zero.mp hi

/-- The actual common-sign residue class of a fixed core column is small. -/
theorem absoluteClass_card_le_four (P : α → β → ℤ) (d : ℕ) (hd : 0 < d)
    (j₀ : β) (hcol : ∑ i, P i j₀ ^ 2 = (d : ℤ) ^ 2)
    (hrow : ∀ i, ∑ j, P i j ^ 2 = (d : ℤ) ^ 2)
    (hcore : ∀ i j, |P i j| < (d : ℤ))
    (hfixed : columnResidue P d j₀ = -columnResidue P d j₀) :
    (absoluteClass P d j₀).card ≤ 4 := by
  apply fixed_class_card_le_four P d (by exact_mod_cast hd)
    (absoluteClass P d j₀) j₀ hcol hrow hcore
    (column_fixed_divisibility P d j₀ hfixed)
  intro j hj
  exact column_same_residue_divisibility P d j j₀ (Finset.mem_filter.mp hj).2

/-- A residue class with at least five members cannot be fixed by negation. -/
theorem large_class_not_fixed (P : α → β → ℤ) (d : ℕ) (hd : 0 < d)
    (j₀ : β) (hcol : ∑ i, P i j₀ ^ 2 = (d : ℤ) ^ 2)
    (hrow : ∀ i, ∑ j, P i j ^ 2 = (d : ℤ) ^ 2)
    (hcore : ∀ i j, |P i j| < (d : ℤ))
    (hlarge : 5 ≤ (absoluteClass P d j₀).card) :
    columnResidue P d j₀ ≠ -columnResidue P d j₀ := by
  intro hfixed
  have := absoluteClass_card_le_four P d hd j₀ hcol hrow hcore hfixed
  omega

/-- The diagonal of the actual row Gram identity gives each row norm. -/
theorem row_norm_of_gram [DecidableEq α]
    (P : Matrix α β ℤ) (d : ℤ)
    (hgram : P * P.transpose = d ^ 2 • (1 : Matrix α α ℤ)) (i : α) :
    ∑ j, P i j ^ 2 = d ^ 2 := by
  have h := congrFun (congrFun hgram i) i
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, pow_two] using h

/-- The diagonal of the actual column Gram identity gives each column norm. -/
theorem column_norm_of_gram [DecidableEq β]
    (P : Matrix α β ℤ) (d : ℤ)
    (hgram : P.transpose * P = d ^ 2 • (1 : Matrix β β ℤ)) (j : β) :
    ∑ i, P i j ^ 2 = d ^ 2 := by
  have h := congrFun (congrFun hgram j) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, pow_two] using h

/-- Direct matrix statement: no pre-proved support, dimension, or class cap input. -/
theorem gram_fixed_class_card_le_four [DecidableEq α] [DecidableEq β]
    (P : Matrix α β ℤ) (d : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ) ^ 2 • (1 : Matrix α α ℤ))
    (hcols : P.transpose * P = (d : ℤ) ^ 2 • (1 : Matrix β β ℤ))
    (hcore : ∀ i j, |P i j| < (d : ℤ)) (j₀ : β)
    (hfixed : columnResidue P d j₀ = -columnResidue P d j₀) :
    (absoluteClass P d j₀).card ≤ 4 := by
  exact absoluteClass_card_le_four P d hd j₀
    (column_norm_of_gram P d hcols j₀) (row_norm_of_gram P d hrows) hcore hfixed

/-- A fixed norm-d² core column can exist only for an even denominator. -/
theorem fixed_column_denominator_even (P : α → β → ℤ) (d : ℤ) (hd : 0 < d)
    (j : β) (hnorm : ∑ i, P i j ^ 2 = d ^ 2)
    (hcore : ∀ i, |P i j| < d) (hfixed : ∀ i, d ∣ 2 * P i j) : Even d := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, P i j ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑ i, P i j ^ 2 = 0 := by simp [h]
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    omega
  rcases fixed_entry_trichotomy d (P i j) hd (hcore i) (hfixed i) with h | h | h
  · exact (hi h).elim
  · exact ⟨P i j, by omega⟩
  · exact ⟨-P i j, by omega⟩

/-- The row version is the same statement applied to the transpose matrix. -/
theorem gram_fixed_row_class_card_le_four [DecidableEq α] [DecidableEq β]
    (P : Matrix α β ℤ) (d : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ) ^ 2 • (1 : Matrix α α ℤ))
    (hcols : P.transpose * P = (d : ℤ) ^ 2 • (1 : Matrix β β ℤ))
    (hcore : ∀ i j, |P i j| < (d : ℤ)) (i₀ : α)
    (hfixed : columnResidue P.transpose d i₀ = -columnResidue P.transpose d i₀) :
    (absoluteClass P.transpose d i₀).card ≤ 4 := by
  apply gram_fixed_class_card_le_four P.transpose d hd
  · simpa using hcols
  · simpa using hrows
  · exact fun j i => hcore i j
  · exact hfixed

/-- Column norms and nonzero residue columns force the strict core bound.
An entry of magnitude d would exhaust its column norm and isolate that column. -/
theorem strict_core_of_nonzero_residue (P : α → β → ℤ) (d : ℕ) (hd : 0 < d)
    (hcols : ∀ j, ∑ i, P i j ^ 2 = (d : ℤ) ^ 2)
    (hnonzero : ∀ j, columnResidue P d j ≠ 0) :
    ∀ i j, |P i j| < (d : ℤ) := by
  classical
  intro i j
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hbound : P i j ^ 2 ≤ (d : ℤ) ^ 2 := by
    calc P i j ^ 2 ≤ ∑ k, P k j ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (P k j)) (Finset.mem_univ i)
    _ = (d : ℤ) ^ 2 := hcols j
  have habs : |P i j| ≤ (d : ℤ) := by
    rw [abs_le]
    constructor <;> nlinarith
  by_contra hlt
  have habseq : |P i j| = (d : ℤ) := le_antisymm habs (by omega)
  have heq := (abs_eq (le_of_lt hd')).mp habseq
  have hsq : P i j ^ 2 = (d : ℤ) ^ 2 := by rcases heq with h | h <;> simp [h]
  have herase : ∑ k ∈ Finset.univ.erase i, P k j ^ 2 = 0 := by
    have he := Finset.sum_erase_add Finset.univ (fun k => P k j ^ 2) (Finset.mem_univ i)
    rw [hcols j, hsq] at he
    omega
  have hother : ∀ k, k ≠ i → P k j = 0 := by
    intro k hki
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.univ.erase i) => sq_nonneg (P k j))).mp herase
    have := hz k (by simp [hki])
    nlinarith
  apply hnonzero j
  funext k
  by_cases hk : k = i
  · subst k
    rcases heq with h | h <;> simp [columnResidue, h]
  · simp [columnResidue, hother k hk]

end FixedSignCapacity
