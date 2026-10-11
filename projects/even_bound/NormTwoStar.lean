import IntegerNormTwo
import CommonEndpoint

/-! Integration of the norm-two and common-endpoint bridges. These inputs are
an actual finite family of integer vectors with their actual dot products. -/

namespace NormTwoStar
open IntegerNormTwo
open scoped BigOperators

variable {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Four or more pairwise-inner-product-one integer norm-two roots have a
common nonzero coordinate whose sign agrees throughout the family. -/
theorem signed_common_endpoint_of_norm_two
    (I : Finset ι) (u : ι → α → ℤ) (hfour : 4 ≤ I.card)
    (hnorm : ∀ i ∈ I, normSq (u i) = 2)
    (hip : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → dot (u i) (u j) = 1) :
    ∃ r ε, (ε = 1 ∨ ε = -1) ∧
      ∀ i ∈ I, r ∈ support (u i) ∧ u i r = ε := by
  exact CommonEndpoint.signed_common_endpoint I u hfour
    (fun i hi => support_card_eq_two (u i) (hnorm i hi))
    (fun i hi x hx => coordinate_unit_of_mem (u i) (hnorm i hi) hx) hip

/-- The same family has a common endpoint and distinct other endpoints. -/
theorem star_decomposition_of_norm_two
    (I : Finset ι) (u : ι → α → ℤ) (hfour : 4 ≤ I.card)
    (hnorm : ∀ i ∈ I, normSq (u i) = 2)
    (hip : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → dot (u i) (u j) = 1) :
    ∃ r, ∃ leaf : I → α, Function.Injective leaf ∧
      ∀ i, r ≠ leaf i ∧ support (u i) = {r, leaf i} := by
  apply CommonEndpoint.indexed_star_decomposition I (fun i => support (u i)) hfour
  · intro i hi j hj heq
    by_contra hij
    exact supports_ne_of_dot_one (u i) (u j) (hnorm i hi) (hnorm j hj)
      (hip i hi j hj hij) heq
  · exact fun i hi => support_card_eq_two (u i) (hnorm i hi)
  · exact fun i hi j hj hij => supports_intersect_of_dot_one (u i) (u j)
      (hip i hi j hj hij)

/-- Signed star decomposition with one common sign and injective leaves. Each
leaf coefficient is a signed unit and the vector identity is coordinatewise. -/
theorem signed_star_decomposition_of_norm_two
    (I : Finset ι) (u : ι → α → ℤ) (hfour : 4 ≤ I.card)
    (hnorm : ∀ i ∈ I, normSq (u i) = 2)
    (hip : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → dot (u i) (u j) = 1) :
    ∃ r ε, ∃ leaf : I → α, ∃ η : I → ℤ,
      (ε = 1 ∨ ε = -1) ∧ Function.Injective leaf ∧
      ∀ i, r ≠ leaf i ∧ (η i = 1 ∨ η i = -1) ∧
        u i = fun x => ε * unitVector r x + η i * unitVector (leaf i) x := by
  obtain ⟨r, leaf, hleaf, hpair⟩ := star_decomposition_of_norm_two I u hfour hnorm hip
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hr : ∀ i : I, r ∈ support (u i) := by
    intro i
    rw [(hpair i).2]
    simp
  have hε : u i₀ r = 1 ∨ u i₀ r = -1 :=
    coordinate_unit_of_mem (u i₀) (hnorm i₀ hi₀) (hr ⟨i₀, hi₀⟩)
  have hsign : ∀ i : I, u i r = u i₀ r := by
    intro i
    by_cases hi : i.val = i₀
    · simp [hi]
    · exact CommonEndpoint.common_endpoint_signs_agree (u i) (u i₀)
        (support_card_eq_two (u i) (hnorm i i.property))
        (support_card_eq_two (u i₀) (hnorm i₀ hi₀))
        (supports_ne_of_dot_one (u i) (u i₀) (hnorm i i.property) (hnorm i₀ hi₀)
          (hip i i.property i₀ hi₀ hi))
        (hr i) (hr ⟨i₀, hi₀⟩)
        (coordinate_unit_of_mem (u i) (hnorm i i.property) (hr i))
        (hip i i.property i₀ hi₀ hi)
  refine ⟨r, u i₀ r, leaf, fun i => u i (leaf i), hε, hleaf, ?_⟩
  intro i
  have hli : leaf i ∈ support (u i) := by rw [(hpair i).2]; simp
  refine ⟨(hpair i).1, coordinate_unit_of_mem (u i) (hnorm i i.property) hli, ?_⟩
  funext x
  by_cases hxr : x = r
  · subst x
    simp [unitVector, (hpair i).1, hsign i]
  by_cases hxl : x = leaf i
  · subst x
    simp [unitVector, Ne.symm (hpair i).1]
  have hx : x ∉ support (u i) := by simp [(hpair i).2, hxr, hxl]
  have hz : u i x = 0 := by simpa using hx
  simp [unitVector, hxr, hxl, hz]

end NormTwoStar
