import ActualFiberBounds

/-!
# Capacity of occupied nonfixed sign classes

This counting lemma uses the actual labels, rather than a sign quotient. The
ambient group may have negation-fixed elements, but none of the given labels
is fixed. Every occupied sign class of size at most four therefore contributes
at most two rows per ambient group element on average.
-/

namespace FreeInvolutionCapacity
open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [AddCommGroup A] [Finite A]

/-- If every actual label is nonfixed under negation and every occupied sign
class has size at most four, the total number of labels is at most twice the
cardinality of the ambient finite group. No odd-order assumption is needed. -/
theorem card_le_two_mul_natCard (F : ι → A)
    (hfree : ∀ i, F i ≠ -F i)
    (hcap : ∀ i, (ActualFiberBounds.signClass F i).card ≤ 4) :
    Fintype.card ι ≤ 2 * Nat.card A := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let occ : A → ℕ := fun a => (Finset.univ.filter (fun i => F i = a)).card
  have htotal : Fintype.card ι = ∑ a, occ a := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset A))
      (f := F) (by simp)
    simpa only [Finset.card_univ] using h
  have hpoint : ∀ a, occ a + occ (-a) ≤ 4 := by
    intro a
    by_cases ha : a = -a
    · have hempty : Finset.univ.filter (fun i => F i = a) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hi : F i = a := (Finset.mem_filter.mp hi).2
        exact hfree i (by rw [hi]; exact ha)
      have hz : occ a = 0 := by simp only [occ, hempty, Finset.card_empty]
      rw [← ha, hz]
      norm_num
    · have hdis : Disjoint (Finset.univ.filter (fun i => F i = a))
          (Finset.univ.filter (fun i => F i = -a)) := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        exact ha ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
      change (Finset.univ.filter (fun i => F i = a)).card +
        (Finset.univ.filter (fun i => F i = -a)).card ≤ 4
      rw [← Finset.card_union_of_disjoint hdis]
      have hc := ActualFiberBounds.sign_target_card_le F 4 hcap a
      apply (Finset.card_le_card ?_).trans hc
      intro i hi
      simpa only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  have hneg : Function.Involutive (fun a : A => -a) := by intro a; simp
  have hperm : (∑ a, occ (-a)) = ∑ a, occ a := hneg.bijective.sum_comp occ
  rw [Finset.sum_add_distrib, hperm, ← htotal] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    at hsum ⊢
  omega

end FreeInvolutionCapacity
