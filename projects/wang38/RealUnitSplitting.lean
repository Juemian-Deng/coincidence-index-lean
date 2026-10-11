import RootComplement
import Mathlib.LinearAlgebra.Basis.Prod

/-! Splitting off an actual norm-one vector in a real Euclidean integer lattice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Wang38I.Classification
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def realUnitProjection (u : E) (hu : inner ℝ u u = 1) : E →ₗ[ℝ] rootPerp u where
  toFun x := ⟨x - inner ℝ u x • u, by
    change inner ℝ u (x - inner ℝ u x • u) = 0
    rw [inner_sub_right, real_inner_smul_right, hu, mul_one, sub_self]⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [inner_add_right, add_smul, Submodule.coe_add]
    abel
  map_smul' a x := by
    apply Subtype.ext
    simp only [real_inner_smul_right, RingHom.id_apply, Submodule.coe_smul, smul_sub, smul_smul]

@[simp] lemma realUnitProjection_coe (u : E) (hu : inner ℝ u u = 1) (x : E) :
    (realUnitProjection u hu x).val = x - inner ℝ u x • u := rfl

@[simp] lemma realUnitProjection_fixed (u : E) (hu : inner ℝ u u = 1) (x : rootPerp u) :
    realUnitProjection u hu x.val = x := by
  apply Subtype.ext
  have hx : inner ℝ u x.val = 0 := x.prop
  simp [hx]

lemma realUnitProjection_surjective (u : E) (hu : inner ℝ u u = 1) :
    Function.Surjective (realUnitProjection u hu) := by
  intro x
  exact ⟨x.val, realUnitProjection_fixed u hu x⟩

lemma realUnitProjection_mem (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1) {x : E} (hx : x ∈ L) :
    realUnitProjection u hu x ∈ rootComplement L u := by
  obtain ⟨k, hk⟩ := selfDual_inner_integral L hL huL hx
  change x - inner ℝ u x • u ∈ L
  rw [hk, Int.cast_smul_eq_zsmul]
  exact L.sub_mem hx (L.smul_mem k huL)

theorem realUnit_decomposition (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1) {x : E} (hx : x ∈ L) :
    ∃ k : ℤ, ∃ y : rootComplement L u, x = (k : ℝ) • u + y.val.val := by
  obtain ⟨k, hk⟩ := selfDual_inner_integral L hL huL hx
  refine ⟨k, ⟨realUnitProjection u hu x, realUnitProjection_mem L hL u huL hu hx⟩, ?_⟩
  change x = (k : ℝ) • u + (x - inner ℝ u x • u)
  rw [hk]
  abel

theorem realUnitComplement_isZLattice [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1) :
    IsZLattice ℝ (rootComplement L u) := by
  constructor
  have hs : Submodule.span ℝ (realUnitProjection u hu '' (L : Set E)) = ⊤ := by
    rw [Submodule.span_image, IsZLattice.span_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (realUnitProjection_surjective u hu)
  apply top_le_iff.mp
  rw [← hs]
  apply Submodule.span_mono
  rintro y ⟨x, hx, rfl⟩
  exact realUnitProjection_mem L hL u huL hu hx

theorem realUnitComplement_selfDual (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1) :
    LinearMap.BilinForm.dualSubmodule (innerₗ (rootPerp u)) (rootComplement L u) =
      rootComplement L u := by
  ext z
  constructor
  · intro hz
    change z.val ∈ L
    rw [← hL]
    intro x hx
    obtain ⟨k, y, he⟩ := realUnit_decomposition L hL u huL hu hx
    have hy := hz y.val y.prop
    change inner ℝ z.val y.val.val ∈ (1 : Submodule ℤ ℝ) at hy
    have hzu : inner ℝ z.val u = 0 := (real_inner_comm _ _).trans z.prop
    change inner ℝ z.val x ∈ (1 : Submodule ℤ ℝ)
    rw [he]
    simpa [inner_add_right, real_inner_smul_right, hzu] using hy
  · intro hz y hy
    obtain ⟨k, hk⟩ := selfDual_inner_integral L hL hz hy
    exact Submodule.mem_one.mpr ⟨k, hk.symm⟩

theorem realUnitPerp_finrank [FiniteDimensional ℝ E] (u : E) (hu : inner ℝ u u = 1) :
    Module.finrank ℝ (rootPerp u) + 1 = Module.finrank ℝ E := by
  have hr : (innerₗ E u).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro a
    refine ⟨a • u, ?_⟩
    change inner ℝ u (a • u) = a
    rw [real_inner_smul_right, hu, mul_one]
  have he := (innerₗ E u).finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self] at he
  simpa only [rootPerp, Nat.add_comm] using he

/-- The integral complement has the geometric codimension-one rank. -/
theorem realUnitComplement_finrank [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1) :
    Module.finrank ℤ (rootComplement L u) + 1 = Module.finrank ℝ E := by
  let : IsZLattice ℝ (rootComplement L u) := realUnitComplement_isZLattice L hL u huL hu
  rw [ZLattice.rank ℝ]
  exact realUnitPerp_finrank u hu

def realUnitJoin (L : Submodule ℤ E) (u : E) (huL : u ∈ L) :
    (ℤ × rootComplement L u) →ₗ[ℤ] L where
  toFun t := ⟨t.1 • u + t.2.val.val, L.add_mem (L.smul_mem t.1 huL) t.2.prop⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' a x := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
      Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_add, smul_smul, smul_eq_mul]

def realUnitSplittingEquiv (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1) :
    (ℤ × rootComplement L u) ≃ₗ[ℤ] L :=
  LinearEquiv.ofBijective (realUnitJoin L u huL) (by
    constructor
    · rintro ⟨k, y⟩ ⟨l, z⟩ h
      have hh := congrArg Subtype.val h
      change k • u + y.val.val = l • u + z.val.val at hh
      have he := congrArg (fun x => inner ℝ u x) hh
      have hy : inner ℝ u y.val.val = 0 := y.val.prop
      have hz : inner ℝ u z.val.val = 0 := z.val.prop
      rw [← Int.cast_smul_eq_zsmul ℝ k u, ← Int.cast_smul_eq_zsmul ℝ l u] at he
      simp only [inner_add_right, real_inner_smul_right, hu, hy, hz, mul_one, add_zero] at he
      have hkl : k = l := Int.cast_injective he
      subst l
      exact Prod.ext rfl (Subtype.ext (Subtype.ext (add_left_cancel hh)))
    · intro x
      obtain ⟨k, y, hy⟩ := realUnit_decomposition L hL u huL hu x.prop
      refine ⟨(k, y), ?_⟩
      apply Subtype.ext
      simpa only [realUnitJoin, LinearMap.coe_mk, AddHom.coe_mk,
        Int.cast_smul_eq_zsmul] using hy.symm)

@[simp] lemma realUnitSplittingEquiv_apply (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1) (t : ℤ × rootComplement L u) :
    (realUnitSplittingEquiv L hL u huL hu t).val = t.1 • u + t.2.val.val := rfl

def realUnitExtendBasis {ι : Type*} (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1)
    (b : Basis ι ℤ (rootComplement L u)) : Basis (Unit ⊕ ι) ℤ L :=
  ((Basis.singleton Unit ℤ).prod b).map (realUnitSplittingEquiv L hL u huL hu)

@[simp] theorem realUnitExtendBasis_inl {ι : Type*} (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1)
    (b : Basis ι ℤ (rootComplement L u)) (i : Unit) :
    (realUnitExtendBasis L hL u huL hu b (Sum.inl i)).val = u := by
  simp [realUnitExtendBasis]

@[simp] theorem realUnitExtendBasis_inr {ι : Type*} (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1)
    (b : Basis ι ℤ (rootComplement L u)) (i : ι) :
    (realUnitExtendBasis L hL u huL hu b (Sum.inr i)).val = (b i).val.val := by
  simp [realUnitExtendBasis]

theorem realUnitExtendBasis_orthonormal {ι : Type*} (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1)
    (b : Basis ι ℤ (rootComplement L u))
    (hb : Orthonormal ℝ (fun i => (b i).val)) :
    Orthonormal ℝ (fun i => (realUnitExtendBasis L hL u huL hu b i).val) := by
  classical
  rw [orthonormal_iff_ite] at hb ⊢
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [realUnitExtendBasis_inl, hu, Subsingleton.elim i j, ite_true]
    | inr j =>
      have hj : inner ℝ u (b j).val.val = 0 := (b j).val.prop
      simp [hj]
  | inr i =>
    cases j with
    | inl j =>
      have hi : inner ℝ (b i).val.val u = 0 := (real_inner_comm _ _).trans (b i).val.prop
      simp [hi]
    | inr j => simpa using hb i j

/-- A literal Kronecker-delta pairing formulation for classification induction. -/
theorem realUnitExtendBasis_inner {ι : Type*} [DecidableEq ι] (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 1)
    (b : Basis ι ℤ (rootComplement L u))
    (hb : ∀ i j, inner ℝ (b i).val (b j).val = if i = j then 1 else 0)
    (i j : Unit ⊕ ι) :
    inner ℝ (realUnitExtendBasis L hL u huL hu b i).val
      (realUnitExtendBasis L hL u huL hu b j).val = if i = j then 1 else 0 := by
  exact orthonormal_iff_ite.mp
    (realUnitExtendBasis_orthonormal L hL u huL hu b (orthonormal_iff_ite.mpr hb)) i j

#print axioms realUnitComplement_isZLattice
#print axioms realUnitComplement_selfDual
#print axioms realUnitPerp_finrank
#print axioms realUnitComplement_finrank
#print axioms realUnitSplittingEquiv
#print axioms realUnitExtendBasis_orthonormal
#print axioms realUnitExtendBasis_inner
end Wang38I.Classification
