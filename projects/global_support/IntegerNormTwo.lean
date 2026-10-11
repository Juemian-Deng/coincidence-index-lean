import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Integral vectors of squared norm two

This file proves only the elementary integer root/support bridge. The index
set is any finite type. No orthogonal matrix or matrix bound is assumed.
-/

namespace IntegerNormTwo
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The finite set of nonzero coordinates. -/
def support (z : ι → ℤ) : Finset ι := Finset.univ.filter (fun i => z i ≠ 0)

/-- Squared Euclidean norm of an integer coordinate vector. -/
def normSq (z : ι → ℤ) : ℤ := ∑ i, z i ^ 2

/-- Integer coordinate inner product. -/
def dot (z w : ι → ℤ) : ℤ := ∑ i, z i * w i

/-- The coordinate unit vector at i. -/
def unitVector [DecidableEq ι] (i : ι) : ι → ℤ := fun k => if k = i then 1 else 0

@[simp] theorem mem_support (z : ι → ℤ) (i : ι) :
    i ∈ support z ↔ z i ≠ 0 := by simp [support]

/-- A single coordinate of a norm-two vector is zero or a signed unit. -/
theorem coordinate_eq_zero_or_unit (z : ι → ℤ) (hz : normSq z = 2) (i : ι) :
    z i = 0 ∨ z i = 1 ∨ z i = -1 := by
  have hsq : z i ^ 2 ≤ 2 := by
    calc z i ^ 2 ≤ ∑ j, z j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
    _ = 2 := hz
  have hlo : -1 ≤ z i := by
    by_contra h
    have : z i ≤ -2 := by omega
    nlinarith
  have hhi : z i ≤ 1 := by
    by_contra h
    have : 2 ≤ z i := by omega
    nlinarith
  omega

/-- Every nonzero coordinate of a norm-two vector is +1 or -1. -/
theorem coordinate_unit_of_mem (z : ι → ℤ) (hz : normSq z = 2)
    {i : ι} (hi : i ∈ support z) : z i = 1 ∨ z i = -1 := by
  have hne : z i ≠ 0 := (mem_support z i).mp hi
  rcases coordinate_eq_zero_or_unit z hz i with h | h | h
  · exact (hne h).elim
  · exact Or.inl h
  · exact Or.inr h

/-- Exactly two coordinates of a norm-two vector are nonzero. -/
theorem support_card_eq_two (z : ι → ℤ) (hz : normSq z = 2) :
    (support z).card = 2 := by
  have hsum : (∑ i ∈ support z, (1 : ℤ)) = normSq z := by
    rw [support, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rcases coordinate_eq_zero_or_unit z hz i with h | h | h <;> simp [h]
  have hc : ((support z).card : ℤ) = 2 := by simpa [hz] using hsum
  exact_mod_cast hc

variable [DecidableEq ι]

/-- The support is a pair of distinct coordinates. -/
theorem support_eq_pair (z : ι → ℤ) (hz : normSq z = 2) :
    ∃ i j, i ≠ j ∧ support z = {i, j} := by
  exact Finset.card_eq_two.mp (support_card_eq_two z hz)

/-- A norm-two vector is a signed sum of two distinct coordinate vectors. -/
theorem eq_signed_unit_vectors (z : ι → ℤ) (hz : normSq z = 2) :
    ∃ i j : ι, ∃ ε η : ℤ, i ≠ j ∧ (ε = 1 ∨ ε = -1) ∧
      (η = 1 ∨ η = -1) ∧
      z = fun k => ε * unitVector i k + η * unitVector j k := by
  obtain ⟨i, j, hij, hs⟩ := support_eq_pair z hz
  have hi : i ∈ support z := by simp [hs]
  have hj : j ∈ support z := by simp [hs]
  refine ⟨i, j, z i, z j, hij, coordinate_unit_of_mem z hz hi,
    coordinate_unit_of_mem z hz hj, ?_⟩
  funext k
  by_cases hki : k = i
  · subst k
    simp [unitVector, hij]
  by_cases hkj : k = j
  · subst k
    simp [unitVector, Ne.symm hij]
  have hk : k ∉ support z := by simp [hs, hki, hkj]
  have hkzero : z k = 0 := by simpa using hk
  simp [unitVector, hki, hkj, hkzero]

omit [DecidableEq ι] in
/-- The dot product can be restricted to the support of its first vector. -/
theorem dot_eq_sum_support (z w : ι → ℤ) :
    dot z w = ∑ i ∈ support z, z i * w i := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : z i = 0 := by simpa using hi
  simp [hz]

omit [DecidableEq ι] in
/-- Disjoint supports force zero inner product. -/
theorem dot_eq_zero_of_disjoint (z w : ι → ℤ)
    (hdisj : Disjoint (support z) (support w)) : dot z w = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hz : z i = 0
  · simp [hz]
  have hi : i ∈ support z := by simpa using hz
  have hw : i ∉ support w := Finset.disjoint_left.mp hdisj hi
  have hwzero : w i = 0 := by simpa using hw
  simp [hwzero]

/-- Inner product one forces supports to intersect. Norm hypotheses are not
needed for this elementary implication. -/
theorem supports_intersect_of_dot_one (z w : ι → ℤ) (hzw : dot z w = 1) :
    (support z ∩ support w).Nonempty := by
  by_contra h
  have hd : Disjoint (support z) (support w) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact h ⟨i, Finset.mem_inter.mpr ⟨hi, hj⟩⟩
  have := dot_eq_zero_of_disjoint z w hd
  omega

/-- Two norm-two vectors with inner product one cannot have equal supports. -/
theorem supports_ne_of_dot_one (z w : ι → ℤ)
    (hz : normSq z = 2) (hw : normSq w = 2) (hzw : dot z w = 1) :
    support z ≠ support w := by
  intro heq
  obtain ⟨i, j, hij, hs⟩ := support_eq_pair z hz
  have hzi : i ∈ support z := by simp [hs]
  have hzj : j ∈ support z := by simp [hs]
  have hwi : i ∈ support w := by rw [← heq]; exact hzi
  have hwj : j ∈ support w := by rw [← heq]; exact hzj
  have hdot : z i * w i + z j * w j = 1 := by
    simpa [dot_eq_sum_support z w, hs, hij] using hzw
  rcases coordinate_unit_of_mem z hz hzi with hi | hi <;>
    rcases coordinate_unit_of_mem z hz hzj with hj | hj <;>
    rcases coordinate_unit_of_mem w hw hwi with hi' | hi' <;>
    rcases coordinate_unit_of_mem w hw hwj with hj' | hj' <;>
    norm_num [hi, hj, hi', hj'] at hdot

/-- Joint interface for the two-element-set common-endpoint theorem. -/
theorem support_pair_properties_of_dot_one (z w : ι → ℤ)
    (hz : normSq z = 2) (hw : normSq w = 2) (hzw : dot z w = 1) :
    (support z).card = 2 ∧ (support w).card = 2 ∧
    support z ≠ support w ∧ (support z ∩ support w).Nonempty := by
  exact ⟨support_card_eq_two z hz, support_card_eq_two w hw,
    supports_ne_of_dot_one z w hz hw hzw, supports_intersect_of_dot_one z w hzw⟩

end IntegerNormTwo
