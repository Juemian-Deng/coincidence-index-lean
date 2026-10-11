import RootDeterminant

/-! Close the Griess short-vector route: rank one has a unit; ranks two
through eight contain a unit or a genuine squared-norm-four vector. -/
namespace Wang38I.Classification
open Module MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A norm-two root is impossible in a rank-one self-dual lattice. -/
theorem no_root_rank_one (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (hn : Module.finrank ℝ E = 1) (u : E) (huL : u ∈ L)
    (hu : inner ℝ u u = 2) : False := by
  have hd := rootPerp_finrank u hu
  rw [hn] at hd
  have hd0 : Module.finrank ℝ (rootPerp u) = 0 := by omega
  let : Subsingleton (rootPerp u) := Module.finrank_zero_iff.mp hd0
  obtain ⟨x, hx, hux⟩ := root_has_pairing_one L hL u huL hu
  have hz : rootProjection u hu x = 0 := Subsingleton.elim _ _
  have he := congrArg Subtype.val hz
  change x - (inner ℝ u x / 2) • u = 0 at he
  rw [hux, sub_eq_zero] at he
  exact half_root_not_mem L hL u hu (he ▸ hx)

theorem selfDual_rank_one_has_unit (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (hn : Module.finrank ℝ E = 1) : ∃ u ∈ L, inner ℝ u u = 1 := by
  obtain ⟨u, huL, hu | hu⟩ := selfDual_exists_unit_or_root L hL (by omega) (by omega)
  · exact ⟨u, huL, by simpa only [real_inner_self_eq_norm_sq] using hu⟩
  · exact (no_root_rank_one L hL hn u huL (by simpa only [real_inner_self_eq_norm_sq] using hu)).elim

/-- An actual second short vector is found in the actual root-perpendicular
lattice, with its determinant bound proved in RootDeterminant. -/
theorem selfDual_unit_or_orthogonal_roots (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (hn2 : 2 ≤ Module.finrank ℝ E) (hn8 : Module.finrank ℝ E ≤ 8) :
    (∃ u ∈ L, inner ℝ u u = 1) ∨
    ∃ u ∈ L, ∃ v ∈ L, inner ℝ u u = 2 ∧ inner ℝ v v = 2 ∧ inner ℝ u v = 0 := by
  obtain ⟨u, huL, huNorm | huNorm⟩ := selfDual_exists_unit_or_root L hL (by omega) hn8
  · exact Or.inl ⟨u, huL, by simpa only [real_inner_self_eq_norm_sq] using huNorm⟩
  have hu : inner ℝ u u = 2 := by simpa only [real_inner_self_eq_norm_sq] using huNorm
  let : IsZLattice ℝ (rootComplement L u) := rootComplement_isZLattice L hL u huL hu
  have hdim := rootPerp_finrank u hu
  have hpos : 0 < Module.finrank ℝ (rootPerp u) := by omega
  have hle7 : Module.finrank ℝ (rootPerp u) ≤ 7 := by omega
  have hvol : (ZLattice.covolume (rootComplement L u))^2 ≤ 2 :=
    (rootComplement_covolume_sq L hL u huL hu).le
  have hInt : ∀ x ∈ rootComplement L u, ∃ k : ℤ, ‖x‖^2 = (k : ℝ) := by
    intro x hx
    obtain ⟨k, hk⟩ := selfDual_inner_integral L hL hx hx
    exact ⟨k, by simpa [Submodule.norm_coe] using hk⟩
  obtain ⟨v, hvC, hvNorm | hvNorm⟩ :=
    exists_unit_or_root_covolume_sq_le_two (rootComplement L u) hpos hle7 hvol hInt
  · left
    exact ⟨v.val, hvC, by simpa only [real_inner_self_eq_norm_sq, Submodule.norm_coe] using hvNorm⟩
  · right
    exact ⟨u, huL, v.val, hvC, hu,
      by simpa only [real_inner_self_eq_norm_sq, Submodule.norm_coe] using hvNorm, v.prop⟩

/-- The complete short-vector prerequisite for the norm-four-neighbor step. -/
theorem selfDual_unit_or_normFour (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (hn2 : 2 ≤ Module.finrank ℝ E) (hn8 : Module.finrank ℝ E ≤ 8) :
    (∃ u ∈ L, inner ℝ u u = 1) ∨ ∃ v ∈ L, inner ℝ v v = 4 := by
  obtain hunit | ⟨u, huL, v, hvL, hu, hv, huv⟩ :=
    selfDual_unit_or_orthogonal_roots L hL hn2 hn8
  · exact Or.inl hunit
  · right
    refine ⟨u + v, L.add_mem huL hvL, ?_⟩
    have hvu : inner ℝ v u = 0 := (real_inner_comm _ _).trans huv
    rw [inner_add_left, inner_add_right, inner_add_right, hu, hv, huv, hvu]
    norm_num

#print axioms selfDual_rank_one_has_unit
#print axioms selfDual_unit_or_orthogonal_roots
#print axioms selfDual_unit_or_normFour
end Wang38I.Classification
