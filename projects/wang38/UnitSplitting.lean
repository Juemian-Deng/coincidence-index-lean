import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
The unit-vector splitting step for Griess's low-rank classification.
This works for arbitrary rational symmetric bilinear spaces, not just a
coordinate copy of the standard dot product. It constructs the actual
orthogonal-complement lattice and proves the properties needed for induction.
It does not assume that the complement is odd.
-/
namespace Wang38I.Classification
open LinearMap Module

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- Integral pairings, using the ordinary embedding ℤ → ℚ. -/
def IntegralOn (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, B x y = (z : ℚ)

lemma integralOn_of_selfDual (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule B L = L) : IntegralOn B L := by
  intro x hx y hy
  have hx' : x ∈ LinearMap.BilinForm.dualSubmodule B L := by rwa [hL]
  obtain ⟨z, hz⟩ := Submodule.mem_one.mp (hx' y hy)
  exact ⟨z, hz.symm⟩

/-- The rational hyperplane perpendicular to the vector u. -/
def unitPerp (B : LinearMap.BilinForm ℚ E) (u : E) : Submodule ℚ E :=
  LinearMap.ker (B u)

@[simp] lemma mem_unitPerp (B : LinearMap.BilinForm ℚ E) (u x : E) :
    x ∈ unitPerp B u ↔ B u x = 0 := Iff.rfl

/-- The actual intersection L ∩ u-perp, as an integer submodule of the
rational orthogonal-complement ambient space. -/
def unitComplement (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E) (u : E) :
    Submodule ℤ (unitPerp B u) :=
  L.comap ((unitPerp B u).subtype.restrictScalars ℤ)

@[simp] lemma mem_unitComplement (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    (u : E) (x : unitPerp B u) : x ∈ unitComplement B L u ↔ x.val ∈ L := Iff.rfl

/-- Rational orthogonal projection along a norm-one vector. -/
def unitProjection (B : LinearMap.BilinForm ℚ E) (u : E) (hu : B u u = 1) :
    E →ₗ[ℚ] unitPerp B u where
  toFun x := ⟨x - (B u x) • u, by simp [unitPerp, LinearMap.mem_ker, hu]⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [map_add, add_smul, Submodule.coe_add]
    abel
  map_smul' a x := by
    apply Subtype.ext
    simp only [map_smul, RingHom.id_apply, Submodule.coe_smul, smul_sub, smul_smul]
    rfl

@[simp] lemma unitProjection_coe (B : LinearMap.BilinForm ℚ E) (u : E) (hu : B u u = 1) (x : E) :
    (unitProjection B u hu x).val = x - (B u x) • u := rfl

@[simp] lemma unitProjection_fixed (B : LinearMap.BilinForm ℚ E) (u : E) (hu : B u u = 1)
    (x : unitPerp B u) : unitProjection B u hu x.val = x := by
  apply Subtype.ext
  simp only [unitProjection_coe, (mem_unitPerp B u x.val).mp x.prop, zero_smul, sub_zero]

lemma unitProjection_surjective (B : LinearMap.BilinForm ℚ E) (u : E) (hu : B u u = 1) :
    Function.Surjective (unitProjection B u hu) := by
  intro x
  exact ⟨x.val, unitProjection_fixed B u hu x⟩

/-- Integral pairings make orthogonal projection preserve the integer lattice. -/
lemma unitProjection_mem (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    (hL : IntegralOn B L) (u : E) (huL : u ∈ L) (hu : B u u = 1)
    {x : E} (hx : x ∈ L) :
    unitProjection B u hu x ∈ unitComplement B L u := by
  obtain ⟨k, hk⟩ := hL u huL x hx
  change x - B u x • u ∈ L
  rw [hk, Int.cast_smul_eq_zsmul]
  exact L.sub_mem hx (L.smul_mem k huL)

/-- Griess Lemma 3.3, with an actual integral coefficient and actual
orthogonal-complement element, rather than a presumed direct sum. -/
theorem unit_decomposition (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    (hL : IntegralOn B L) (u : E) (huL : u ∈ L) (hu : B u u = 1)
    {x : E} (hx : x ∈ L) :
    ∃ k : ℤ, ∃ y : unitComplement B L u,
      x = (k : ℚ) • u + y.val.val := by
  obtain ⟨k, hk⟩ := hL u huL x hx
  refine ⟨k, ⟨unitProjection B u hu x, unitProjection_mem B L hL u huL hu hx⟩, ?_⟩
  change x = (k : ℚ) • u + (x - B u x • u)
  rw [hk]
  abel

lemma unit_decomposition_unique (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    (u : E) (hu : B u u = 1) (k l : ℤ)
    (y z : unitComplement B L u)
    (h : (k : ℚ) • u + y.val.val = (l : ℚ) • u + z.val.val) :
    k = l ∧ y = z := by
  have hy : B u y.val.val = 0 := y.val.prop
  have hz : B u z.val.val = 0 := z.val.prop
  have he := congrArg (fun x => B u x) h
  simp only [map_add, map_smul, smul_eq_mul, hu, hy, hz, mul_one, add_zero] at he
  have hkl : k = l := Int.cast_injective he
  refine ⟨hkl, ?_⟩
  subst l
  have hyz := add_left_cancel h
  exact Subtype.ext (Subtype.ext hyz)

/-- Pairings split into a rank-one integral form and the complement form. -/
theorem unit_pairing_split (B : LinearMap.BilinForm ℚ E) (hB : B.IsSymm)
    (L : Submodule ℤ E) (u : E) (hu : B u u = 1)
    (k l : ℤ) (y z : unitComplement B L u) :
    B ((k : ℚ) • u + y.val.val) ((l : ℚ) • u + z.val.val) =
      (k : ℚ) * (l : ℚ) + B y.val.val z.val.val := by
  have hy : B u y.val.val = 0 := y.val.prop
  have hz : B u z.val.val = 0 := z.val.prop
  have hy' : B y.val.val u = 0 := (hB.eq _ _).trans hy
  simp [hu, hy', hz]

/-- The complement is exactly the image of integral orthogonal projection. -/
theorem unitComplement_eq_map (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    (hL : IntegralOn B L) (u : E) (huL : u ∈ L) (hu : B u u = 1) :
    unitComplement B L u = L.map ((unitProjection B u hu).restrictScalars ℤ) := by
  ext x
  constructor
  · intro hx
    exact ⟨x.val, hx, unitProjection_fixed B u hu x⟩
  · rintro ⟨x, hx, rfl⟩
    exact unitProjection_mem B L hL u huL hu hx

/-- Finite generation and full rational span survive the unit split. -/
theorem unitComplement_isLattice (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    [Submodule.IsLattice ℚ L] (hL : IntegralOn B L)
    (u : E) (huL : u ∈ L) (hu : B u u = 1) :
    Submodule.IsLattice ℚ (unitComplement B L u) := by
  constructor
  · rw [unitComplement_eq_map B L hL u huL hu]
    exact Submodule.IsLattice.fg.map _
  · rw [unitComplement_eq_map B L hL u huL hu, Submodule.map_coe]
    change Submodule.span ℚ (unitProjection B u hu '' (L : Set E)) = ⊤
    rw [Submodule.span_image, Submodule.IsLattice.span_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (unitProjection_surjective B u hu)

/-- Unimodularity is preserved: the actual complement lattice equals its
integral dual for the restricted bilinear form. -/
theorem unitComplement_selfDual (B : LinearMap.BilinForm ℚ E) (hB : B.IsSymm)
    (L : Submodule ℤ E) (hL : LinearMap.BilinForm.dualSubmodule B L = L)
    (u : E) (huL : u ∈ L) (hu : B u u = 1) :
    LinearMap.BilinForm.dualSubmodule (B.restrict (unitPerp B u)) (unitComplement B L u) =
      unitComplement B L u := by
  have hInt := integralOn_of_selfDual B L hL
  ext z
  constructor
  · intro hz
    change z.val ∈ L
    rw [← hL]
    intro x hx
    obtain ⟨k, y, he⟩ := unit_decomposition B L hInt u huL hu hx
    have hy := hz y.val y.prop
    change B z.val y.val.val ∈ (1 : Submodule ℤ ℚ) at hy
    have hzu : B z.val u = 0 := (hB.eq _ _).trans z.prop
    rw [he]
    simpa [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hzu] using hy
  · intro hz y hy
    obtain ⟨k, hk⟩ := hInt z.val hz y.val hy
    exact Submodule.mem_one.mpr ⟨k, hk.symm⟩

/-- The concrete integral gluing map for the orthogonal decomposition. -/
def unitJoin (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    (u : E) (huL : u ∈ L) :
    (ℤ × unitComplement B L u) →ₗ[ℤ] L where
  toFun t := ⟨t.1 • u + t.2.val.val, L.add_mem (L.smul_mem t.1 huL) t.2.prop⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' a x := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
      Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_add, smul_smul, smul_eq_mul]

/-- An actual ℤ-linear equivalence, not just an informal direct-sum label. -/
noncomputable def unitSplittingEquiv (B : LinearMap.BilinForm ℚ E)
    (L : Submodule ℤ E) (hL : IntegralOn B L)
    (u : E) (huL : u ∈ L) (hu : B u u = 1) :
    (ℤ × unitComplement B L u) ≃ₗ[ℤ] L :=
  LinearEquiv.ofBijective (unitJoin B L u huL) (by
    constructor
    · rintro ⟨k, y⟩ ⟨l, z⟩ h
      have hh := congrArg Subtype.val h
      have he : (k : ℚ) • u + y.val.val = (l : ℚ) • u + z.val.val := by
        simpa only [unitJoin, LinearMap.coe_mk, AddHom.coe_mk,
          Int.cast_smul_eq_zsmul] using hh
      obtain ⟨hk, hy⟩ := unit_decomposition_unique B L u hu k l y z he
      exact Prod.ext hk hy
    · intro x
      obtain ⟨k, y, hy⟩ := unit_decomposition B L hL u huL hu x.prop
      refine ⟨(k, y), ?_⟩
      apply Subtype.ext
      simpa only [unitJoin, LinearMap.coe_mk, AddHom.coe_mk,
        Int.cast_smul_eq_zsmul] using hy.symm)

@[simp] lemma unitSplittingEquiv_apply (B : LinearMap.BilinForm ℚ E)
    (L : Submodule ℤ E) (hL : IntegralOn B L)
    (u : E) (huL : u ∈ L) (hu : B u u = 1)
    (t : ℤ × unitComplement B L u) :
    (unitSplittingEquiv B L hL u huL hu t).val = t.1 • u + t.2.val.val := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The rational ambient rank drops by exactly one. -/
theorem unitPerp_finrank [FiniteDimensional ℚ E]
    (B : LinearMap.BilinForm ℚ E) (u : E) (hu : B u u = 1) :
    Module.finrank ℚ (unitPerp B u) + 1 = Module.finrank ℚ E := by
  have hr : (B u).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro a
    exact ⟨a • u, by simp [hu]⟩
  have he := (B u).finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self] at he
  simpa only [unitPerp, Nat.add_comm] using he

/-- The actual integral complement lattice has precisely the required
rank for the lower-dimensional classification induction. -/
theorem unitComplement_finrank [FiniteDimensional ℚ E]
    (B : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E) [Submodule.IsLattice ℚ L]
    (hL : IntegralOn B L) (u : E) (huL : u ∈ L) (hu : B u u = 1) :
    Module.finrank ℤ (unitComplement B L u) + 1 = Module.finrank ℚ E := by
  let : Submodule.IsLattice ℚ (unitComplement B L u) :=
    unitComplement_isLattice B L hL u huL hu
  have he : Module.finrank ℤ (unitComplement B L u) = Module.finrank ℚ (unitPerp B u) := by
    exact congrArg Cardinal.toNat (Submodule.IsLattice.rank' ℚ (unitComplement B L u))
  rw [he]
  exact unitPerp_finrank B u hu

/-- Positive definiteness passes to the actual restricted space. -/
theorem unitComplement_positive (B : LinearMap.BilinForm ℚ E)
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) (u : E) :
    ∀ x : unitPerp B u, x ≠ 0 → 0 < (B.restrict (unitPerp B u)) x x := by
  intro x hx
  apply hB x.val
  exact fun h => hx (Subtype.ext h)

#print axioms unit_decomposition
#print axioms unit_decomposition_unique
#print axioms unit_pairing_split
#print axioms unitComplement_isLattice
#print axioms unitComplement_selfDual
#print axioms unitComplement_finrank
#print axioms unitSplittingEquiv
end Wang38I.Classification
