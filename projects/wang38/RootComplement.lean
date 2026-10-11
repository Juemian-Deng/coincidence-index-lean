import RootPairing
import Mathlib.Tactic.FunProp

/-! The actual root-perpendicular geometric lattice, with discreteness,
full span, and rank drop proved. Its covolume calculation remains separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Wang38I.Classification
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rootPerp (u : E) : Submodule ℝ E := LinearMap.ker (innerₗ E u)

def rootComplement (L : Submodule ℤ E) (u : E) : Submodule ℤ (rootPerp u) :=
  L.comap ((rootPerp u).subtype.restrictScalars ℤ)

@[simp] lemma mem_rootPerp (u x : E) : x ∈ rootPerp u ↔ inner ℝ u x = 0 := Iff.rfl
@[simp] lemma mem_rootComplement (L : Submodule ℤ E) (u : E) (x : rootPerp u) :
    x ∈ rootComplement L u ↔ x.val ∈ L := Iff.rfl

instance rootComplement_discreteTopology (L : Submodule ℤ E) [DiscreteTopology L] (u : E) :
    DiscreteTopology (rootComplement L u) := by
  let f : rootComplement L u → L := fun x => ⟨x.val.val, x.prop⟩
  have hf : Continuous f := by dsimp [f]; fun_prop
  apply DiscreteTopology.of_continuous_injective hf
  intro x y h
  have hh := congrArg (fun z : L => z.val) h
  change x.val.val = y.val.val at hh
  exact Subtype.ext (Subtype.ext hh)

def rootProjection (u : E) (hu : inner ℝ u u = 2) : E →ₗ[ℝ] rootPerp u where
  toFun x := ⟨x - (inner ℝ u x / 2) • u, by
    change inner ℝ u (x - (inner ℝ u x / 2) • u) = 0
    rw [inner_sub_right, real_inner_smul_right, hu]
    ring⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [inner_add_right, add_div, add_smul, Submodule.coe_add]
    abel
  map_smul' a x := by
    apply Subtype.ext
    simp only [real_inner_smul_right, RingHom.id_apply, Submodule.coe_smul, smul_sub, smul_smul,
      mul_div_assoc]

@[simp] lemma rootProjection_coe (u : E) (hu : inner ℝ u u = 2) (x : E) :
    (rootProjection u hu x).val = x - (inner ℝ u x / 2) • u := rfl

@[simp] lemma rootProjection_fixed (u : E) (hu : inner ℝ u u = 2) (x : rootPerp u) :
    rootProjection u hu x.val = x := by
  apply Subtype.ext
  have hx : inner ℝ u x.val = 0 := x.prop
  simp [hx]

lemma rootProjection_surjective (u : E) (hu : inner ℝ u u = 2) :
    Function.Surjective (rootProjection u hu) := by
  intro x
  exact ⟨x.val, rootProjection_fixed u hu x⟩

/-- Twice the orthogonal projection of a lattice vector stays in the
actual perpendicular lattice. -/
theorem twice_rootProjection_mem (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) {x : E} (hx : x ∈ L) :
    (2 : ℝ) • rootProjection u hu x ∈ rootComplement L u := by
  obtain ⟨k, hk⟩ := selfDual_inner_integral L hL huL hx
  change (2 : ℝ) • (x - (inner ℝ u x / 2) • u) ∈ L
  rw [hk, smul_sub, smul_smul]
  have he : (2 : ℝ) * ((k : ℝ)/2) = (k : ℝ) := by ring
  rw [he, Int.cast_smul_eq_zsmul]
  have hx2 : (2 : ℝ) • x = (2 : ℤ) • x := (Int.cast_smul_eq_zsmul ℝ 2 x)
  rw [hx2]
  exact L.sub_mem (L.smul_mem 2 hx) (L.smul_mem k huL)

/-- The perpendicular intersection is a full discrete lattice in the
actual codimension-one Euclidean subspace. -/
theorem rootComplement_isZLattice [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    IsZLattice ℝ (rootComplement L u) := by
  constructor
  have hs : Submodule.span ℝ (rootProjection u hu '' (L : Set E)) = ⊤ := by
    rw [Submodule.span_image, IsZLattice.span_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (rootProjection_surjective u hu)
  apply top_le_iff.mp
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  have htwice := Submodule.subset_span (R := ℝ) (twice_rootProjection_mem L hL u huL hu hx)
  have hh := (Submodule.span ℝ (rootComplement L u : Set (rootPerp u))).smul_mem (1/2 : ℝ) htwice
  simpa only [SetLike.mem_coe, smul_smul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_smul] using hh

set_option backward.isDefEq.respectTransparency false in
/-- The rationally defined perpendicular direction has geometric codimension one. -/
theorem rootPerp_finrank [FiniteDimensional ℝ E] (u : E) (hu : inner ℝ u u = 2) :
    Module.finrank ℝ (rootPerp u) + 1 = Module.finrank ℝ E := by
  have hr : (innerₗ E u).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro a
    refine ⟨(a/2) • u, ?_⟩
    change inner ℝ u ((a/2) • u) = a
    rw [real_inner_smul_right, hu]
    ring
  have he := (innerₗ E u).finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self] at he
  simpa only [rootPerp, Nat.add_comm] using he

/-- Its integer rank is exactly one less than the original geometric rank. -/
theorem rootComplement_finrank [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    Module.finrank ℤ (rootComplement L u) + 1 = Module.finrank ℝ E := by
  let : IsZLattice ℝ (rootComplement L u) := rootComplement_isZLattice L hL u huL hu
  rw [ZLattice.rank ℝ]
  exact rootPerp_finrank u hu

#print axioms rootComplement_isZLattice
#print axioms rootComplement_finrank
end Wang38I.Classification
