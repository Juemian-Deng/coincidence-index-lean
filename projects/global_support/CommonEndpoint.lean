import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The finite common-endpoint step only. No matrix theorem is assumed. -/
namespace CommonEndpoint
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- A two-element set is determined by any two distinct members. -/
theorem pair_eq_of_members {S : Finset α} (hS : S.card = 2)
    {a b : α} (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) : S = {a,b} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · simp [hS, hab]

/-- Meeting all three sides of a triangle forces a two-element set to be a side. -/
theorem triangle_classification {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {S : Finset α} (hS : S.card = 2)
    (hAB : (S ∩ {a,b}).Nonempty) (hAC : (S ∩ {a,c}).Nonempty)
    (hBC : (S ∩ {b,c}).Nonempty) :
    S = {a,b} ∨ S = {a,c} ∨ S = {b,c} := by
  by_cases ha : a ∈ S
  · rcases hBC with ⟨x, hx⟩
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx.2 with rfl | rfl
    · exact Or.inl (pair_eq_of_members hS hab ha hx.1)
    · exact Or.inr (Or.inl (pair_eq_of_members hS hac ha hx.1))
  · have hb : b ∈ S := by
      rcases hAB with ⟨x, hx⟩
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx.2 with rfl | rfl
      · exact (ha hx.1).elim
      · exact hx.1
    have hc : c ∈ S := by
      rcases hAC with ⟨x, hx⟩
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx.2 with rfl | rfl
      · exact (ha hx.1).elim
      · exact hx.1
    exact Or.inr (Or.inr (pair_eq_of_members hS hbc hb hc))

/-- A finite intersecting family of pairs with no common vertex has at most
three members. Distinctness is inherent in the Finset representation. -/
theorem no_common_endpoint_card_le_three (F : Finset (Finset α))
    (hpairs : ∀ S ∈ F, S.card = 2)
    (hmeet : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hno : ¬ ∃ a, ∀ S ∈ F, a ∈ S) : F.card ≤ 3 := by
  by_cases hF : F.Nonempty
  · obtain ⟨A, hA⟩ := hF
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hpairs A hA)
    have ha_missing : ∃ B ∈ F, a ∉ B := by
      by_contra! hn
      exact hno ⟨a, hn⟩
    obtain ⟨B, hB, haB⟩ := ha_missing
    have hbB : b ∈ B := by
      obtain ⟨x, hx⟩ := hmeet B hB {a,b} hA
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx.2 with rfl | rfl
      · exact (haB hx.1).elim
      · exact hx.1
    obtain ⟨c, hcB, hcb⟩ : ∃ c ∈ B, c ≠ b := by
      by_contra! hn
      have hsub : B ⊆ {b} := by
        intro x hx
        simpa using hn x hx
      have hcard := Finset.card_le_card hsub
      simp only [Finset.card_singleton, hpairs B hB] at hcard
      omega
    have hbc : b ≠ c := Ne.symm hcb
    have hBpair : B = {b,c} := pair_eq_of_members (hpairs B hB) hbc hbB hcB
    have hac : a ≠ c := by
      intro h
      exact haB (h.symm ▸ hcB)
    have hb_missing : ∃ C ∈ F, b ∉ C := by
      by_contra! hn
      exact hno ⟨b, hn⟩
    obtain ⟨C, hC, hbC⟩ := hb_missing
    have haC : a ∈ C := by
      obtain ⟨x, hx⟩ := hmeet C hC {a,b} hA
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx.2 with rfl | rfl
      · exact hx.1
      · exact (hbC hx.1).elim
    have hcC : c ∈ C := by
      obtain ⟨x, hx⟩ := hmeet C hC B hB
      rw [hBpair] at hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx.2 with rfl | rfl
      · exact (hbC hx.1).elim
      · exact hx.1
    have hCpair : C = {a,c} := pair_eq_of_members (hpairs C hC) hac haC hcC
    have hsub : F ⊆ {{a,b}, {a,c}, {b,c}} := by
      intro S hS
      have hAB := hmeet S hS {a,b} hA
      have hAC := hmeet S hS C hC
      have hBC := hmeet S hS B hB
      rw [hCpair] at hAC
      rw [hBpair] at hBC
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        triangle_classification hab hac hbc (hpairs S hS) hAB hAC hBC
    exact (Finset.card_le_card hsub).trans Finset.card_le_three
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [this]

/-- Four or more distinct pairwise-intersecting pairs have a common endpoint. -/
theorem common_endpoint_of_four (F : Finset (Finset α))
    (hfour : 4 ≤ F.card) (hpairs : ∀ S ∈ F, S.card = 2)
    (hmeet : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).Nonempty) :
    ∃ a, ∀ S ∈ F, a ∈ S := by
  by_contra hno
  have hmeet' : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty := by
    intro S hS T hT
    by_cases hST : S = T
    · subst T
      rw [Finset.inter_self]
      exact Finset.card_pos.mp (by rw [hpairs S hS]; omega)
    · exact hmeet S hS T hT hST
  have := no_common_endpoint_card_le_three F hpairs hmeet' hno
  omega

/-- Indexed form: an injective support map prevents repeated supports from
being counted as four different edges. -/
theorem indexed_common_endpoint {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset α) (hfour : 4 ≤ I.card)
    (hinj : Set.InjOn S I) (hpairs : ∀ i ∈ I, (S i).card = 2)
    (hmeet : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).Nonempty) :
    ∃ r, ∀ i ∈ I, r ∈ S i := by
  have hc : (I.image S).card = I.card := Finset.card_image_iff.mpr hinj
  obtain ⟨r, hr⟩ := common_endpoint_of_four (I.image S) (by omega)
    (by
      intro A hA
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      exact hpairs i hi)
    (by
      intro A hA B hB hAB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
      exact hmeet i hi j hj (fun hij => hAB (congrArg S hij)))
  exact ⟨r, fun i hi => hr (S i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩

/-- The common endpoint gives an actual star: every edge has one leaf,
all leaves differ from the center, and different edges have different leaves. -/
theorem indexed_star_decomposition {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset α) (hfour : 4 ≤ I.card)
    (hinj : Set.InjOn S I) (hpairs : ∀ i ∈ I, (S i).card = 2)
    (hmeet : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).Nonempty) :
    ∃ r, ∃ leaf : I → α, Function.Injective leaf ∧
      ∀ i, r ≠ leaf i ∧ S i = {r, leaf i} := by
  classical
  obtain ⟨r, hr⟩ := indexed_common_endpoint I S hfour hinj hpairs hmeet
  have hex : ∀ i : I, ∃ x, r ≠ x ∧ S i = {r,x} := by
    intro i
    obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp (hpairs i i.property)
    have hm := hr i i.property
    rw [hpair] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · subst a
      exact ⟨b, hab, hpair⟩
    · subst b
      exact ⟨a, hab.symm, hpair.trans (Finset.pair_comm a r)⟩
  choose leaf hleaf using hex
  refine ⟨r, leaf, ?_, hleaf⟩
  intro i j hij
  apply Subtype.ext
  apply hinj i.property j.property
  rw [(hleaf i).2, (hleaf j).2, hij]

/-- Distinct pairs containing r intersect at exactly r. -/
theorem pair_inter_eq_singleton {S T : Finset α}
    (hS : S.card = 2) (hT : T.card = 2) (hne : S ≠ T)
    {r : α} (hrS : r ∈ S) (hrT : r ∈ T) : S ∩ T = {r} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · intro hx
    by_contra hxr
    have hSr := pair_eq_of_members hS (Ne.symm hxr) hrS hx.1
    have hTr := pair_eq_of_members hT (Ne.symm hxr) hrT hx.2
    exact hne (hSr.trans hTr.symm)
  · rintro rfl
    exact ⟨hrS, hrT⟩

section Signed
variable [Fintype α]

/-- The actual nonzero-coordinate set of an integer vector. -/
def support (u : α → ℤ) : Finset α := Finset.univ.filter (fun x => u x ≠ 0)

omit [DecidableEq α] in
@[simp] theorem mem_support (u : α → ℤ) (x : α) : x ∈ support u ↔ u x ≠ 0 := by
  simp [support]

/-- Nonzero inner product forces the actual supports to meet. -/
theorem supports_meet_of_inner_one (u v : α → ℤ)
    (hip : ∑ x, u x * v x = 1) : (support u ∩ support v).Nonempty := by
  by_contra hn
  have hz : ∑ x, u x * v x = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hu : u x = 0
    · simp [hu]
    · have hv : v x = 0 := by
        by_contra hv
        exact hn ⟨x, Finset.mem_inter.mpr ⟨(mem_support u x).mpr hu,
          (mem_support v x).mpr hv⟩⟩
      simp [hv]
  omega

/-- On distinct two-coordinate supports sharing r, the whole inner product
is the product at r. -/
theorem inner_eq_common_product (u v : α → ℤ)
    (hu : (support u).card = 2) (hv : (support v).card = 2)
    (hne : support u ≠ support v) {r : α}
    (hru : r ∈ support u) (hrv : r ∈ support v) :
    ∑ x, u x * v x = u r * v r := by
  have hinter := pair_inter_eq_singleton hu hv hne hru hrv
  apply Finset.sum_eq_single r
  · intro x _ hxr
    by_cases hx : u x = 0
    · simp [hx]
    · have hxv : v x = 0 := by
        by_contra hxv
        have hm : x ∈ support u ∩ support v :=
          Finset.mem_inter.mpr ⟨(mem_support u x).mpr hx, (mem_support v x).mpr hxv⟩
        rw [hinter, Finset.mem_singleton] at hm
        exact hxr hm
      simp [hxv]
  · simp

/-- Positive unit inner product forces matching signs at the common endpoint.
The unit-entry hypothesis is explicit; integer norm-two classification is
not assumed under another name or supplied by this theorem. -/
theorem common_endpoint_signs_agree (u v : α → ℤ)
    (hu : (support u).card = 2) (hv : (support v).card = 2)
    (hne : support u ≠ support v) {r : α}
    (hru : r ∈ support u) (hrv : r ∈ support v)
    (hunit : u r = 1 ∨ u r = -1) (hip : ∑ x, u x * v x = 1) :
    u r = v r := by
  rw [inner_eq_common_product u v hu hv hne hru hrv] at hip
  rcases hunit with h | h <;> rw [h] at hip ⊢ <;> linarith

/-- A family of at least four distinct two-coordinate integer supports with
pairwise inner product one has a common coordinate and one shared sign there.
Unit entries are supplied explicitly, pending the integer norm-two bridge. -/
theorem signed_common_endpoint_of_distinct {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (u : ι → α → ℤ) (hfour : 4 ≤ I.card)
    (hinj : Set.InjOn (fun i => support (u i)) I)
    (hpairs : ∀ i ∈ I, (support (u i)).card = 2)
    (hunit : ∀ i ∈ I, ∀ x ∈ support (u i), u i x = 1 ∨ u i x = -1)
    (hip : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∑ x, u i x * u j x = 1) :
    ∃ r ε, (ε = 1 ∨ ε = -1) ∧ ∀ i ∈ I, r ∈ support (u i) ∧ u i r = ε := by
  obtain ⟨r, hr⟩ := indexed_common_endpoint I (fun i => support (u i)) hfour hinj
    hpairs (fun i hi j hj hij => supports_meet_of_inner_one (u i) (u j) (hip i hi j hj hij))
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  refine ⟨r, u i₀ r, hunit i₀ hi₀ r (hr i₀ hi₀), ?_⟩
  intro i hi
  refine ⟨hr i hi, ?_⟩
  by_cases hii : i = i₀
  · subst i
    rfl
  · exact common_endpoint_signs_agree (u i) (u i₀) (hpairs i hi) (hpairs i₀ hi₀)
      (fun heq => hii (hinj hi hi₀ heq)) (hr i hi) (hr i₀ hi₀)
      (hunit i hi r (hr i hi)) (hip i hi i₀ hi₀ hii)

/-- Two integer vectors with the same two-coordinate support and unit entries
cannot have inner product one: the possible dot products are -2, 0, and 2. -/
theorem inner_one_supports_ne (u v : α → ℤ)
    (hpairs : (support u).card = 2)
    (hu : ∀ x ∈ support u, u x = 1 ∨ u x = -1)
    (hv : ∀ x ∈ support v, v x = 1 ∨ v x = -1)
    (hip : ∑ x, u x * v x = 1) : support u ≠ support v := by
  intro heq
  obtain ⟨a, b, hab, habs⟩ := Finset.card_eq_two.mp hpairs
  have ha : a ∈ support u := by rw [habs]; simp
  have hb : b ∈ support u := by rw [habs]; simp
  have hva : a ∈ support v := heq ▸ ha
  have hvb : b ∈ support v := heq ▸ hb
  have hsum : ∑ x ∈ support u, u x * v x = ∑ x, u x * v x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    have hz : u x = 0 := by simpa using hx
    simp [hz]
  rw [habs] at hsum
  simp [hab] at hsum
  rw [hip] at hsum
  rcases hu a ha with hua | hua <;> rcases hu b hb with hub | hub <;>
    rcases hv a hva with hva | hva <;> rcases hv b hvb with hvb | hvb <;>
    norm_num [hua, hub, hva, hvb] at hsum

/-- Signed endpoint theorem without an assumed support-injectivity premise.
Distinctness and pairwise support intersections are derived from dot products.
The precise remaining structural premise is two nonzero unit coordinates. -/
theorem signed_common_endpoint {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (u : ι → α → ℤ) (hfour : 4 ≤ I.card)
    (hpairs : ∀ i ∈ I, (support (u i)).card = 2)
    (hunit : ∀ i ∈ I, ∀ x ∈ support (u i), u i x = 1 ∨ u i x = -1)
    (hip : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∑ x, u i x * u j x = 1) :
    ∃ r ε, (ε = 1 ∨ ε = -1) ∧ ∀ i ∈ I, r ∈ support (u i) ∧ u i r = ε := by
  apply signed_common_endpoint_of_distinct I u hfour ?_ hpairs hunit hip
  intro i hi j hj heq
  by_contra hij
  exact inner_one_supports_ne (u i) (u j) (hpairs i hi) (hunit i hi)
    (hunit j hj) (hip i hi j hj hij) heq

end Signed
end CommonEndpoint
