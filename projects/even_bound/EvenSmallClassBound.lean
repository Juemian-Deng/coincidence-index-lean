import ActualFiberBounds
import ResidueImageAdapter

namespace EvenSmallClassBound
open scoped BigOperators
open ResidueParityBridge
open ActualFiberBounds

variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
noncomputable local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- The entire small-class branch, directly for the actual integer matrix.
The cap eight is precisely the branch condition; fixed caps, core bounds,
parity coset, and its half-cardinality are derived rather than assumed. -/
theorem even_bound_of_small_classes (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (heven : KernelEven P d)
    (hsmall : ∀ j, (signClass (columnLabel P d) j).card ≤ 8) :
    n ≤ 2 * Nat.card (ResidueImage P d) := by
  classical
  by_cases hn : 0 < n
  swap
  · omega
  let : NeZero d := ⟨by omega⟩
  let : Fintype (ResidueImage P d) := Fintype.ofFinite _
  let : Fintype (OddImage P d heven) := Fintype.ofFinite _
  let F := oddColumnLabel P d heven
  let occ : OddImage P d heven → ℕ := fun a =>
    (Finset.univ.filter (fun j => F j = a)).card
  have htotal : n = ∑ a, occ a := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (OddImage P d heven))) (f := F) (by simp)
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have hfixed : ∀ a, oddNeg P d heven a = a → occ a ≤ 4 := by
    intro a ha
    by_cases hex : (Finset.univ.filter (fun j => F j = a)).Nonempty
    · obtain ⟨j, hj⟩ := hex
      have hj : F j = a := (Finset.mem_filter.mp hj).2
      have hval : columnLabel P d j = a.val := congrArg Subtype.val hj
      have hfix : columnLabel P d j = -columnLabel P d j := by
        have h := congrArg Subtype.val ha
        change -a.val = a.val at h
        rw [hval]
        exact h.symm
      have hc := FixedSignCapacity.gram_even_fixed_image_class_card_le_four
        P d hd hrows hcols heven j hfix
      apply (Finset.card_le_card (t := Finset.univ.filter
        (fun k => columnLabel P d k = columnLabel P d j ∨
          columnLabel P d k = -columnLabel P d j)) ?_).trans hc
      intro k hk
      have hk : F k = a := (Finset.mem_filter.mp hk).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ((congrArg Subtype.val hk).trans hval.symm)
    · simp only [occ, Finset.not_nonempty_iff_eq_empty.mp hex, Finset.card_empty]
      omega
  have hpair : ∀ a, oddNeg P d heven a ≠ a → occ a + occ (oddNeg P d heven a) ≤ 8 := by
    intro a ha
    have hdis : Disjoint (Finset.univ.filter (fun j => F j = a))
        (Finset.univ.filter (fun j => F j = oddNeg P d heven a)) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      exact ha ((Finset.mem_filter.mp hk).2.symm.trans (Finset.mem_filter.mp hj).2)
    have hc := sign_target_card_le (columnLabel P d) 8 hsmall a.val
    rw [← Finset.card_union_of_disjoint hdis]
    apply (Finset.card_le_card ?_).trans hc
    intro j hj
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hj with hj | hj
    · exact Or.inl (congrArg Subtype.val hj)
    · exact Or.inr (congrArg Subtype.val hj)
  have hh : 2 * Fintype.card (OddImage P d heven) = Nat.card (ResidueImage P d) := by
    simpa only [Nat.card_eq_fintype_card] using twice_card_oddImage P d heven hn
  apply htotal.le.trans
  exact DualFiberCounting.parity_orbit_capacity (oddNeg P d heven)
    (oddNeg_involutive P d heven) occ _ hh hfixed hpair

end EvenSmallClassBound
