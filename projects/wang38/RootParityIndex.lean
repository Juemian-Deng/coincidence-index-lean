import RootComplement
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-! The root-even-pairing sublattice has exact index two and covolume two.
These are actual group indices and geometric covolumes. -/
noncomputable section
namespace Wang38I.Classification
open Module MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def rootPairingMap (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) : L →ₗ[ℤ] ℤ :=
  LinearMap.BilinForm.dualSubmoduleToDual (innerₗ E) L ⟨u, by rwa [hL]⟩

lemma rootPairingMap_cast (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (x : L) :
    (rootPairingMap L hL u huL x : ℝ) = inner ℝ u x.val := by
  exact LinearMap.BilinForm.dualSubmoduleParing_spec (innerₗ E) _ x

lemma rootPairingMap_surjective (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    Function.Surjective (rootPairingMap L hL u huL) := by
  intro a
  obtain ⟨x, hx, he⟩ := root_pairing_surjective L hL u huL hu a
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Int.cast_injective (α := ℝ)
  rw [rootPairingMap_cast, he]

def rootParityMap (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) : L →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap.comp (rootPairingMap L hL u huL)

def rootParityKernel (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) : Submodule ℤ L :=
  LinearMap.ker (rootParityMap L hL u huL)

def rootParityLattice (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) : Submodule ℤ E :=
  (rootParityKernel L hL u huL).map L.subtype

lemma rootParityLattice_le (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) : rootParityLattice L hL u huL ≤ L := by
  rintro x ⟨y, hy, rfl⟩
  exact y.prop

lemma mem_rootParityLattice (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (x : L) :
    x.val ∈ rootParityLattice L hL u huL ↔ rootParityMap L hL u huL x = 0 := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := Subtype.ext he
    subst y
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

instance rootParityLattice_discreteTopology (L : Submodule ℤ E) [DiscreteTopology L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) : DiscreteTopology (rootParityLattice L hL u huL) := by
  let f : rootParityLattice L hL u huL → L :=
    fun x => ⟨x.val, rootParityLattice_le L hL u huL x.prop⟩
  have hf : Continuous f := by dsimp [f]; fun_prop
  apply DiscreteTopology.of_continuous_injective hf
  intro x y h
  have hh := congrArg (fun z : L => z.val) h
  exact Subtype.ext hh

lemma twice_mem_rootParityLattice (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) {x : E} (hx : x ∈ L) :
    (2 : ℝ) • x ∈ rootParityLattice L hL u huL := by
  have he : (2 : ℝ) • x = ((2 : ℤ) • (⟨x, hx⟩ : L)).val := by
    simp only [two_smul, Submodule.coe_add]
  rw [he, mem_rootParityLattice, map_smul]
  simp only [zsmul_eq_mul, Int.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

theorem rootParityLattice_isZLattice [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) : IsZLattice ℝ (rootParityLattice L hL u huL) := by
  constructor
  apply top_le_iff.mp
  rw [← IsZLattice.span_top (K := ℝ) (L := L)]
  apply Submodule.span_le.mpr
  intro x hx
  have hh := Submodule.subset_span (R := ℝ) (twice_mem_rootParityLattice L hL u huL hx)
  have he := (Submodule.span ℝ (rootParityLattice L hL u huL : Set E)).smul_mem (1/2 : ℝ) hh
  simpa only [SetLike.mem_coe, smul_smul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_smul] using he

lemma rootParityMap_surjective (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    Function.Surjective (rootParityMap L hL u huL) :=
  ZMod.intCast_surjective.comp (rootPairingMap_surjective L hL u huL hu)

/-- The parity kernel has exact index two, proved via the actual quotient. -/
theorem rootParityKernel_index_two (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    (rootParityKernel L hL u huL).toAddSubgroup.index = 2 := by
  rw [AddSubgroup.index_eq_card]
  have he := (rootParityMap L hL u huL).quotKerEquivOfSurjective
    (rootParityMap_surjective L hL u huL hu)
  change Nat.card (L ⧸ LinearMap.ker (rootParityMap L hL u huL)) = 2
  rw [Nat.card_congr he.toEquiv]
  simp

/-- The embedded parity sublattice has the same exact relative index. -/
theorem rootParityLattice_relIndex_two (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    (rootParityLattice L hL u huL).toAddSubgroup.relIndex L.toAddSubgroup = 2 := by
  have he : (rootParityLattice L hL u huL).toAddSubgroup.addSubgroupOf L.toAddSubgroup =
      (rootParityKernel L hL u huL).toAddSubgroup := by
    ext x
    exact mem_rootParityLattice L hL u huL x
  change ((rootParityLattice L hL u huL).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index = 2
  rw [he]
  exact rootParityKernel_index_two L hL u huL hu

/-- The geometric covolume of the root-parity sublattice is exactly two. -/
theorem rootParityLattice_covolume [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    ZLattice.covolume (rootParityLattice L hL u huL) = 2 := by
  let : IsZLattice ℝ (rootParityLattice L hL u huL) := rootParityLattice_isZLattice L hL u huL
  have he := ZLattice.covolume_div_covolume_eq_relIndex'
    (rootParityLattice L hL u huL) L (rootParityLattice_le L hL u huL)
  rw [selfDual_covolume_one L hL, rootParityLattice_relIndex_two L hL u huL hu] at he
  simpa using he

#print axioms rootParityKernel_index_two
#print axioms rootParityLattice_relIndex_two
#print axioms rootParityLattice_covolume
end Wang38I.Classification
