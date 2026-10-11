import UnitSplitting
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Self-duality forces an actual integer Gram determinant to be a unit.
This proves the algebraic part of the covolume-one bridge; no determinant
condition is supplied as an assumption. -/
open scoped BigOperators
namespace Wang38I.Classification
open Module

variable {E : Type*} [AddCommGroup E] [Module ℚ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma extended_basis_integer_span (L : Submodule ℤ E) [Submodule.IsLattice ℚ L]
    (b : Basis ι ℤ L) : Submodule.span ℤ (Set.range (b.extendOfIsLattice ℚ)) = L := by
  have he : (b.extendOfIsLattice ℚ : ι → E) = L.subtype ∘ b := by
    funext i
    exact Basis.extendOfIsLattice_apply ℚ b i
  rw [he, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
    Submodule.range_subtype]

/-- Every dual basis vector really lies in the original self-dual lattice. -/
theorem dual_basis_mem_selfDual (B : LinearMap.BilinForm ℚ E) (hB : B.Nondegenerate)
    (L : Submodule ℤ E) [Submodule.IsLattice ℚ L]
    (hL : LinearMap.BilinForm.dualSubmodule B L = L) (b : Basis ι ℤ L) (i : ι) :
    B.dualBasis hB (b.extendOfIsLattice ℚ) i ∈ L := by
  have he := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) B hB (b.extendOfIsLattice ℚ)
  have hh : LinearMap.BilinForm.dualSubmodule B
      (Submodule.span ℤ (Set.range (b.extendOfIsLattice ℚ))) = L := by
    rw [extended_basis_integer_span L b, hL]
  have hs : Submodule.span ℤ (Set.range (B.dualBasis hB (b.extendOfIsLattice ℚ))) = L :=
    he.symm.trans hh
  have hm : B.dualBasis hB (b.extendOfIsLattice ℚ) i ∈
      Submodule.span ℤ (Set.range (B.dualBasis hB (b.extendOfIsLattice ℚ))) :=
    Submodule.subset_span ⟨i, rfl⟩
  rwa [hs] at hm

/-- An integer Gram matrix in an actual lattice basis has determinant ±1
when the lattice is self-dual. -/
theorem integer_gram_det_isUnit (B : LinearMap.BilinForm ℚ E) (hB : B.Nondegenerate)
    (L : Submodule ℤ E) [Submodule.IsLattice ℚ L]
    (hL : LinearMap.BilinForm.dualSubmodule B L = L) (b : Basis ι ℤ L)
    (G : Matrix ι ι ℤ) (hG : ∀ i j, (G i j : ℚ) = B (b i).val (b j).val) :
    IsUnit G.det := by
  let bQ := b.extendOfIsLattice ℚ
  let d : ι → L := fun i => ⟨B.dualBasis hB bQ i, dual_basis_mem_selfDual B hB L hL b i⟩
  let C : Matrix ι ι ℤ := fun i j => b.repr (d i) j
  have hrepr : ∀ i, (∑ k, ((C i k : ℤ) : ℚ) • (b k).val) = (d i).val := by
    intro i
    have hh := congrArg Subtype.val (b.sum_repr (d i))
    simpa only [C, Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul] using hh
  have hCG : C * G = 1 := by
    ext i j
    apply Int.cast_injective (α := ℚ)
    simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Matrix.one_apply, Int.cast_ite,
      Int.cast_one, Int.cast_zero, hG]
    have hdual := LinearMap.BilinForm.apply_dualBasis_left hB bQ i j
    have hdual' : B (d i).val (b j).val = if j = i then 1 else 0 := by
      simpa only [d, bQ, Basis.extendOfIsLattice_apply] using hdual
    rw [← hrepr i] at hdual'
    simpa [map_sum, LinearMap.sum_apply, LinearMap.smul_apply, eq_comm] using hdual' 
  have hd : C.det * G.det = 1 := by
    rw [← Matrix.det_mul, hCG, Matrix.det_one]
  exact IsUnit.of_mul_eq_one_right C.det hd

/-- The integral Gram matrix itself is obtained from self-duality, so no
hidden integrality hypothesis is needed in the combined result. -/
theorem selfDual_integer_gram (B : LinearMap.BilinForm ℚ E) (hB : B.Nondegenerate)
    (L : Submodule ℤ E) [Submodule.IsLattice ℚ L]
    (hL : LinearMap.BilinForm.dualSubmodule B L = L) (b : Basis ι ℤ L) :
    ∃ G : Matrix ι ι ℤ, (∀ i j, (G i j : ℚ) = B (b i).val (b j).val) ∧
      (G.det = 1 ∨ G.det = -1) := by
  have hi := integralOn_of_selfDual B L hL
  have hg : ∀ i j, ∃ g : ℤ, (g : ℚ) = B (b i).val (b j).val := by
    intro i j
    obtain ⟨g, hg⟩ := hi (b i).val (b i).prop (b j).val (b j).prop
    exact ⟨g, hg.symm⟩
  choose G hG using hg
  exact ⟨G, hG, Int.isUnit_iff.mp (integer_gram_det_isUnit B hB L hL b G hG)⟩

#print axioms integer_gram_det_isUnit
#print axioms selfDual_integer_gram
end Wang38I.Classification
