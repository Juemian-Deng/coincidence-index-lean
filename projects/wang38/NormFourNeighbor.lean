import RootPairing
import Mathlib.Tactic.FunProp
import Mathlib.GroupTheory.Index

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Wang38I.Classification
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normFourCore (L : Submodule ℤ E) (v : E) : Submodule ℤ E where
  carrier := {x | x ∈ L ∧ ∃ a : ℤ, inner ℝ ((1/2 : ℝ) • v) x = (a : ℝ)}
  zero_mem' := ⟨L.zero_mem, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, a, ha⟩ ⟨hy, b, hb⟩
    exact ⟨L.add_mem hx hy, a+b, by rw [inner_add_right, ha, hb, Int.cast_add]⟩
  smul_mem' := by
    rintro a x ⟨hx, b, hb⟩
    refine ⟨L.smul_mem a hx, a*b, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hb]
    push_cast
    rfl

def normFourNeighbor (L : Submodule ℤ E) (v : E) : Submodule ℤ E :=
  normFourCore L v ⊔ Submodule.span ℤ {((1/2 : ℝ) • v)}

lemma mem_normFourNeighbor (L : Submodule ℤ E) (v x : E) :
    x ∈ normFourNeighbor L v ↔ ∃ y ∈ normFourCore L v, ∃ a : ℤ,
      x = y + a • ((1/2 : ℝ) • v) := by
  simp only [normFourNeighbor, Submodule.mem_sup, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, hy, z, ⟨a, rfl⟩, rfl⟩
    exact ⟨y, hy, a, rfl⟩
  · rintro ⟨y, hy, a, rfl⟩
    exact ⟨y, hy, _, ⟨a, rfl⟩, rfl⟩

lemma half_normFour_unit (v : E) (hv : inner ℝ v v = 4) :
    inner ℝ ((1/2 : ℝ) • v) ((1/2 : ℝ) • v) = 1 := by
  rw [real_inner_smul_left, real_inner_smul_right, hv]
  norm_num

lemma half_mem_normFourNeighbor (L : Submodule ℤ E) (v : E) :
    (1/2 : ℝ) • v ∈ normFourNeighbor L v :=
  (show Submodule.span ℤ {((1/2 : ℝ) • v)} ≤ normFourNeighbor L v from le_sup_right)
    (Submodule.subset_span (Set.mem_singleton _))

lemma normFourCore_le (L : Submodule ℤ E) (v : E) : normFourCore L v ≤ L :=
  fun _ h => h.1

lemma twice_mem_normFourCore (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (v : E) (hvL : v ∈ L) {x : E} (hx : x ∈ L) :
    (2 : ℤ) • x ∈ normFourCore L v := by
  obtain ⟨a, ha⟩ := selfDual_inner_integral L hL hvL hx
  refine ⟨L.smul_mem 2 hx, a, ?_⟩
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, real_inner_smul_left, ha]
  push_cast
  ring

lemma normFour_has_odd_pairing (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (v : E) (hvL : v ∈ L) (hhalf : (1/2 : ℝ) • v ∉ L) :
    ∃ x ∈ L, ∃ k : ℤ, inner ℝ v x = (k : ℝ) ∧ k % 2 = 1 := by
  by_contra hnone
  apply hhalf
  rw [← hL]
  intro x hx
  obtain ⟨k, hk⟩ := selfDual_inner_integral L hL hvL hx
  have hknot : k % 2 ≠ 1 := fun he => hnone ⟨x, hx, k, hk, he⟩
  have hkeven : k % 2 = 0 := by omega
  obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero hkeven
  apply Submodule.mem_one.mpr
  refine ⟨a, ?_⟩
  change (a : ℝ) = inner ℝ ((1/2 : ℝ) • v) x
  rw [real_inner_smul_left, hk, ha]
  push_cast
  ring

lemma normFourNeighbor_integral (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (v : E) (hv : inner ℝ v v = 4) {x y : E}
    (hx : x ∈ normFourNeighbor L v) (hy : y ∈ normFourNeighbor L v) :
    ∃ a : ℤ, inner ℝ x y = (a : ℝ) := by
  obtain ⟨x, hxc, a, rfl⟩ := (mem_normFourNeighbor L v x).mp hx
  obtain ⟨y, hyc, b, rfl⟩ := (mem_normFourNeighbor L v y).mp hy
  obtain ⟨c, hc⟩ := selfDual_inner_integral L hL hxc.1 hyc.1
  obtain ⟨d, hd⟩ := hxc.2
  obtain ⟨e, he⟩ := hyc.2
  refine ⟨c + b*d + a*e + a*b, ?_⟩
  rw [inner_add_left, inner_add_right, inner_add_right]
  simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, real_inner_smul_right,
    hc, he, real_inner_comm ((1/2 : ℝ) • v) x, hd, hv]
  push_cast
  ring

lemma normFourNeighbor_selfDual (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (v : E) (hvL : v ∈ L) (hv : inner ℝ v v = 4)
    (hhalf : (1/2 : ℝ) • v ∉ L) :
    LinearMap.BilinForm.dualSubmodule (innerₗ E) (normFourNeighbor L v) =
      normFourNeighbor L v := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, j, hj, hjodd⟩ := normFour_has_odd_pairing L hL v hvL hhalf
    obtain ⟨d, hd⟩ : (2 : ℤ) ∣ 1-j := by omega
    have htwot : (2 : ℤ) • t ∈ normFourNeighbor L v :=
      (show normFourCore L v ≤ normFourNeighbor L v from le_sup_left)
        (twice_mem_normFourCore L hL v hvL ht)
    obtain ⟨m, hm⟩ := Submodule.mem_one.mp (hx _ htwot)
    have hm' : (m : ℝ) = 2 * inner ℝ x t := by
      change (m : ℝ) = inner ℝ x ((2 : ℤ) • t) at hm
      simpa only [ ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right,
        Int.cast_ofNat] using hm
    have hzL : x - m • ((1/2 : ℝ) • v) ∈ L := by
      rw [← hL]
      intro y hy
      obtain ⟨k, hk⟩ := selfDual_inner_integral L hL hvL hy
      have hycore : y - k • t ∈ normFourCore L v := by
        refine ⟨L.sub_mem hy (L.smul_mem k ht), k*d, ?_⟩
        rw [inner_sub_right, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right,
          real_inner_smul_left, real_inner_smul_left, hk, hj]
        have hd' : (1 : ℝ) - j = 2 * d := by exact_mod_cast hd
        push_cast
        linear_combination (k : ℝ) / 2 * hd'
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hx _ ((show normFourCore L v ≤ normFourNeighbor L v from le_sup_left) hycore))
      apply Submodule.mem_one.mpr
      refine ⟨a, ?_⟩
      change (a : ℝ) = inner ℝ (x - m • ((1/2 : ℝ) • v)) y
      change (a : ℝ) = inner ℝ x (y-k • t) at ha
      rw [inner_sub_left, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left,
        real_inner_smul_left, hk]
      rw [inner_sub_right, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right] at ha
      rw [ha, hm']
      ring
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hx _ (half_mem_normFourNeighbor L v))
    have hzcore : x - m • ((1/2 : ℝ) • v) ∈ normFourCore L v := by
      refine ⟨hzL, a-m, ?_⟩
      rw [inner_sub_right, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right,
        half_normFour_unit v hv, mul_one, real_inner_comm x ((1/2 : ℝ) • v)]
      change (a : ℝ) = inner ℝ x ((1/2 : ℝ) • v) at ha
      rw [← ha]
      push_cast
      rfl
    exact (mem_normFourNeighbor L v x).mpr ⟨_, hzcore, m, by abel⟩
  · intro x hx y hy
    obtain ⟨a, ha⟩ := normFourNeighbor_integral L hL v hv hx hy
    exact Submodule.mem_one.mpr ⟨a, ha.symm⟩

lemma normFour_intersection (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (v : E) (hv : inner ℝ v v = 4) :
    L ⊓ normFourNeighbor L v = normFourCore L v := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1, normFourNeighbor_integral L hL v hv
      (half_mem_normFourNeighbor L v) hx.2⟩
  · intro x hx
    exact ⟨hx.1, (show normFourCore L v ≤ normFourNeighbor L v from le_sup_left) hx⟩

lemma mem_normFourCore_iff (L : Submodule ℤ E) (v x : E)
    (hx : x ∈ L) (k : ℤ) (hk : inner ℝ v x = (k : ℝ)) :
    x ∈ normFourCore L v ↔ k % 2 = 0 := by
  constructor
  · rintro ⟨_, a, ha⟩
    rw [real_inner_smul_left, hk] at ha
    have he : (k : ℝ) = 2 * a := by linarith
    have he' : k = 2*a := by exact_mod_cast he
    omega
  · intro he
    obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero he
    refine ⟨hx, a, ?_⟩
    rw [real_inner_smul_left, hk, ha]
    push_cast
    ring

lemma normFourCore_index (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (v : E) (hvL : v ∈ L) (hhalf : (1/2 : ℝ) • v ∉ L) :
    (normFourCore L v).toAddSubgroup.relIndex L.toAddSubgroup = 2 := by
  rw [AddSubgroup.relIndex_eq_two_iff]
  obtain ⟨t, ht, j, hj, hjodd⟩ := normFour_has_odd_pairing L hL v hvL hhalf
  refine ⟨t, ht, ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := selfDual_inner_integral L hL hvL hx
  have hxt : inner ℝ v (x+t) = ((k+j : ℤ) : ℝ) := by
    rw [inner_add_right, hk, hj, Int.cast_add]
  change Xor (x+t ∈ normFourCore L v) (x ∈ normFourCore L v)
  rw [mem_normFourCore_iff L v (x+t) (L.add_mem hx ht) (k+j) hxt,
    mem_normFourCore_iff L v x hx k hk]
  simp only [Xor]
  omega

lemma normFour_mem_core (L : Submodule ℤ E) (v : E)
    (hvL : v ∈ L) (hv : inner ℝ v v = 4) : v ∈ normFourCore L v := by
  refine ⟨hvL, 2, ?_⟩
  rw [real_inner_smul_left, hv]
  norm_num

lemma normFourNeighbor_index (L : Submodule ℤ E) (v : E)
    (hvL : v ∈ L) (hv : inner ℝ v v = 4)
    (hhalf : (1/2 : ℝ) • v ∉ L) :
    (normFourCore L v).toAddSubgroup.relIndex (normFourNeighbor L v).toAddSubgroup = 2 := by
  rw [AddSubgroup.relIndex_eq_two_iff]
  refine ⟨(1/2 : ℝ) • v, half_mem_normFourNeighbor L v, ?_⟩
  intro x hx
  change Xor (x + (1/2 : ℝ) • v ∈ normFourCore L v) (x ∈ normFourCore L v)
  have hnotboth : ¬ (x + (1/2 : ℝ) • v ∈ normFourCore L v ∧ x ∈ normFourCore L v) := by
    rintro ⟨h1, h2⟩
    apply hhalf
    simpa using L.sub_mem h1.1 h2.1
  have hor : x + (1/2 : ℝ) • v ∈ normFourCore L v ∨ x ∈ normFourCore L v := by
    obtain ⟨y, hy, a, rfl⟩ := (mem_normFourNeighbor L v x).mp hx
    have hdecomp (b : ℤ) : (2*b : ℤ) • ((1/2 : ℝ) • v) = b • v := by
      simp only [← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_mul, Int.cast_ofNat]
      congr 1
      ring
    by_cases ha : a % 2 = 0
    · obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero ha
      right
      rw [hb, hdecomp]
      exact (normFourCore L v).add_mem hy ((normFourCore L v).smul_mem b (normFour_mem_core L v hvL hv))
    · have he : (a+1) % 2 = 0 := by omega
      obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero he
      left
      have heq : y + a • ((1/2 : ℝ) • v) + (1/2 : ℝ) • v =
          y + (a+1) • ((1/2 : ℝ) • v) := by rw [add_smul, one_smul]; abel
      rw [heq, hb, hdecomp]
      exact (normFourCore L v).add_mem hy ((normFourCore L v).smul_mem b (normFour_mem_core L v hvL hv))
  simp only [Xor]
  tauto

lemma twice_mem_original_of_normFourNeighbor (L : Submodule ℤ E) (v : E)
    (hvL : v ∈ L) {x : E} (hx : x ∈ normFourNeighbor L v) : (2 : ℝ) • x ∈ L := by
  obtain ⟨y, hy, a, rfl⟩ := (mem_normFourNeighbor L v x).mp hx
  have he : (2 : ℝ) • (y + a • ((1/2 : ℝ) • v)) = (2 : ℤ) • y + a • v := by
    simp only [smul_add, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_ofNat]
    congr 1
    congr 1
    ring
  rw [he]
  exact L.add_mem (L.smul_mem 2 hy.1) (L.smul_mem a hvL)

lemma normFourNeighbor_discreteTopology (L : Submodule ℤ E) [DiscreteTopology L]
    (v : E) (hvL : v ∈ L) : DiscreteTopology (normFourNeighbor L v) := by
  let f : normFourNeighbor L v → L := fun x =>
    ⟨(2 : ℝ) • x.val, twice_mem_original_of_normFourNeighbor L v hvL x.prop⟩
  have hf : Continuous f := by dsimp [f]; fun_prop
  apply DiscreteTopology.of_continuous_injective hf
  intro x y h
  have hh := congrArg (fun z : L => z.val) h
  change (2 : ℝ) • x.val = (2 : ℝ) • y.val at hh
  apply Subtype.ext
  exact (smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)) hh

lemma normFourNeighbor_isZLattice (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (v : E) (hvL : v ∈ L) :
    letI := normFourNeighbor_discreteTopology L v hvL
    IsZLattice ℝ (normFourNeighbor L v) := by
  let := normFourNeighbor_discreteTopology L v hvL
  constructor
  apply top_le_iff.mp
  rw [← (show Submodule.span ℝ (L : Set E) = ⊤ from IsZLattice.span_top)]
  apply Submodule.span_le.mpr
  intro x hx
  have hh : (2 : ℤ) • x ∈ normFourNeighbor L v :=
    (show normFourCore L v ≤ normFourNeighbor L v from le_sup_left)
      (twice_mem_normFourCore L hL v hvL hx)
  have hs := (Submodule.span ℝ (normFourNeighbor L v : Set E)).smul_mem
    (1/2 : ℝ) (Submodule.subset_span hh)
  rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul] at hs
  norm_num at hs
  exact hs

/-- Griess's norm-four neighbor construction, with literal inner-product
self-duality, geometric lattice structure, and both actual intersection indices. -/
theorem normFour_unit_or_neighbor (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (v : E) (hvL : v ∈ L) (hv : inner ℝ v v = 4) :
    (∃ u ∈ L, inner ℝ u u = 1) ∨
    ∃ K : Submodule ℤ E, ∃ hK : DiscreteTopology K,
      letI := hK
      IsZLattice ℝ K ∧
      LinearMap.BilinForm.dualSubmodule (innerₗ E) K = K ∧
      (1/2 : ℝ) • v ∈ K ∧ inner ℝ ((1/2 : ℝ) • v) ((1/2 : ℝ) • v) = 1 ∧
      (L ⊓ K).toAddSubgroup.relIndex L.toAddSubgroup = 2 ∧
      (L ⊓ K).toAddSubgroup.relIndex K.toAddSubgroup = 2 := by
  by_cases hh : (1/2 : ℝ) • v ∈ L
  · exact Or.inl ⟨_, hh, half_normFour_unit v hv⟩
  · right
    refine ⟨normFourNeighbor L v, normFourNeighbor_discreteTopology L v hvL,
      normFourNeighbor_isZLattice L hL v hvL, normFourNeighbor_selfDual L hL v hvL hv hh,
      half_mem_normFourNeighbor L v, half_normFour_unit v hv, ?_, ?_⟩
    · rw [normFour_intersection L hL v hv]
      exact normFourCore_index L hL v hvL hh
    · rw [normFour_intersection L hL v hv]
      exact normFourNeighbor_index L v hvL hv hh

#print axioms normFour_unit_or_neighbor
end Wang38I.Classification
