import CovolumeGram

/-! A norm-two root is primitive in a self-dual integral lattice: its
integer pairing map onto ℤ is surjective. This is the algebraic entry point
for the missing perpendicular-root determinant-two calculation. -/
namespace Wang38I.Classification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma selfDual_inner_integral (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    {x y : E} (hx : x ∈ L) (hy : y ∈ L) :
    ∃ k : ℤ, inner ℝ x y = (k : ℝ) := by
  have hx' : x ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by rwa [hL]
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hx' y hy)
  exact ⟨k, hk.symm⟩

/-- Half a norm-two root cannot belong to an integral self-dual lattice. -/
lemma half_root_not_mem (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (hu : inner ℝ u u = 2) : (1/2 : ℝ) • u ∉ L := by
  intro hhalf
  obtain ⟨k, hk⟩ := selfDual_inner_integral L hL hhalf hhalf
  have he : inner ℝ ((1/2 : ℝ) • u) ((1/2 : ℝ) • u) = (1/2 : ℝ) := by
    rw [real_inner_smul_left, real_inner_smul_right, hu]
    norm_num
  rw [he] at hk
  have hreal : (1 : ℝ) = 2 * (k : ℝ) := by linarith
  have hint : (1 : ℤ) = 2 * k := by exact_mod_cast hreal
  omega

/-- There is an odd integral pairing with every norm-two root. -/
theorem root_has_odd_pairing (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    ∃ x ∈ L, ∃ k : ℤ, inner ℝ u x = (k : ℝ) ∧ k % 2 = 1 := by
  by_contra hnone
  apply half_root_not_mem L hL u hu
  rw [← hL]
  intro x hx
  obtain ⟨k, hk⟩ := selfDual_inner_integral L hL huL hx
  have hknot : k % 2 ≠ 1 := by
    intro he
    exact hnone ⟨x, hx, k, hk, he⟩
  have hkeven : k % 2 = 0 := by omega
  obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero hkeven
  apply Submodule.mem_one.mpr
  refine ⟨a, ?_⟩
  change (a : ℝ) = inner ℝ ((1/2 : ℝ) • u) x
  rw [real_inner_smul_left, hk, ha]
  push_cast
  ring

/-- The root-pairing functional takes the value one on an actual lattice
vector. This is proved from self-duality and norm two, not assumed primitive. -/
theorem root_has_pairing_one (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    ∃ x ∈ L, inner ℝ u x = 1 := by
  obtain ⟨x, hx, k, hk, hodd⟩ := root_has_odd_pairing L hL u huL hu
  have hd : (2 : ℤ) ∣ 1 - k := by omega
  obtain ⟨a, ha⟩ := hd
  refine ⟨x + a • u, L.add_mem hx (L.smul_mem a huL), ?_⟩
  rw [inner_add_right, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hk, hu]
  have he : (1 : ℝ) - (k : ℝ) = 2 * (a : ℝ) := by exact_mod_cast ha
  linarith

/-- Surjectivity onto all integers, in a form suitable for constructing
the parity quotient and proving its exact index. -/
theorem root_pairing_surjective (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) (a : ℤ) :
    ∃ x ∈ L, inner ℝ u x = (a : ℝ) := by
  obtain ⟨x, hx, hux⟩ := root_has_pairing_one L hL u huL hu
  refine ⟨a • x, L.smul_mem a hx, ?_⟩
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hux, mul_one]

#print axioms root_has_pairing_one
#print axioms root_pairing_surjective
end Wang38I.Classification
