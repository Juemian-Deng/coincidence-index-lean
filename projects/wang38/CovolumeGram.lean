import ShortVectorBounds
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-! Close the actual real-lattice self-duality → covolume-one → unit/root
chain. No covolume value or Gram determinant is assumed in the final theorem. -/
open scoped BigOperators
open MeasureTheory Module
namespace Wang38I.Classification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared geometric covolume is the determinant of the actual Gram matrix. -/
theorem covolume_sq_eq_gram_det (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    (ZLattice.covolume L)^2 = (Matrix.gram ℝ (fun i => (b i).val)).det := by
  classical
  let e : Fin (Module.finrank ℝ E) ≃ ι := Fintype.equivOfCardEq (by
    simpa using Module.finrank_eq_card_basis (b.ofZLatticeBasis ℝ))
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex e
  have hf : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    simp [measureReal_def, o.volume_parallelepiped]
  have hc := ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis
  rw [hf, mul_one] at hc
  rw [hc, sq_abs, Basis.det_apply, Matrix.gram_eq_conjTranspose_mul o,
    Matrix.det_mul, Matrix.det_conjTranspose]
  have hmat : o.toBasis.toMatrix (Subtype.val ∘ b) =
      Matrix.of (fun i j => (o.repr (b j).val).ofLp i) := by
    ext i j
    rfl
  rw [hmat]
  simp [pow_two]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma real_inner_nondegenerate : (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    have hh := hx x
    change inner ℝ x x = 0 at hh
    exact inner_self_eq_zero.mp hh
  · intro x hx
    have hh := hx x
    change inner ℝ x x = 0 at hh
    exact inner_self_eq_zero.mp hh

omit [MeasurableSpace E] [BorelSpace E] in
/-- Self-duality gives an integer inverse to the real Gram matrix, so its
integer determinant is a unit. The basis vectors are the actual lattice basis. -/
theorem selfDual_real_integer_gram (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (b : Basis ι ℤ L) :
    ∃ G : Matrix ι ι ℤ, (∀ i j, (G i j : ℝ) = inner ℝ (b i).val (b j).val) ∧
      IsUnit G.det := by
  let B : LinearMap.BilinForm ℝ E := innerₗ E
  let bR := b.ofZLatticeBasis ℝ
  have hB : B.Nondegenerate := real_inner_nondegenerate
  have hspan : Submodule.span ℤ (Set.range bR) = L := b.ofZLatticeBasis_span ℝ
  have hmem : ∀ i, B.dualBasis hB bR i ∈ L := by
    intro i
    have he := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) B hB bR
    have hh : LinearMap.BilinForm.dualSubmodule B (Submodule.span ℤ (Set.range bR)) = L := by
      rw [hspan]; exact hL
    have hs := he.symm.trans hh
    have hm : B.dualBasis hB bR i ∈ Submodule.span ℤ (Set.range (B.dualBasis hB bR)) :=
      Submodule.subset_span ⟨i, rfl⟩
    rwa [hs] at hm
  have hg : ∀ i j, ∃ g : ℤ, (g : ℝ) = B (b i).val (b j).val := by
    intro i j
    have hi : (b i).val ∈ LinearMap.BilinForm.dualSubmodule B L := by
      simpa only [B, hL] using (b i).prop
    exact Submodule.mem_one.mp (hi (b j).val (b j).prop)
  choose g hg using hg
  let G : Matrix ι ι ℤ := Matrix.of g
  have hG : ∀ i j, (G i j : ℝ) = B (b i).val (b j).val := hg
  let d : ι → L := fun i => ⟨B.dualBasis hB bR i, hmem i⟩
  let C : Matrix ι ι ℤ := fun i j => b.repr (d i) j
  have hrepr : ∀ i, (∑ k, ((C i k : ℤ) : ℝ) • (b k).val) = (d i).val := by
    intro i
    have hh := congrArg Subtype.val (b.sum_repr (d i))
    simpa only [C, Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul] using hh
  have hCG : C * G = 1 := by
    ext i j
    apply Int.cast_injective (α := ℝ)
    simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Matrix.one_apply, Int.cast_ite,
      Int.cast_one, Int.cast_zero, hG]
    have hdual := LinearMap.BilinForm.apply_dualBasis_left hB bR i j
    have hdual' : B (d i).val (b j).val = if j = i then 1 else 0 := by
      simpa only [d, bR, Basis.ofZLatticeBasis_apply] using hdual
    rw [← hrepr i] at hdual'
    simpa [map_sum, LinearMap.sum_apply, LinearMap.smul_apply, eq_comm] using hdual'
  refine ⟨G, hG, ?_⟩
  have hd : C.det * G.det = 1 := by rw [← Matrix.det_mul, hCG, Matrix.det_one]
  exact IsUnit.of_mul_eq_one_right C.det hd

/-- Self-duality, not a supplied determinant or volume assumption, forces
geometric covolume one for an actual real Euclidean lattice. -/
theorem selfDual_covolume_one (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L) :
    ZLattice.covolume L = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  obtain ⟨G, hG, hunit⟩ := selfDual_real_integer_gram L hL b
  have hgram : Matrix.gram ℝ (fun i => (b i).val) = G.map (Int.castRingHom ℝ) := by
    ext i j
    simpa [Matrix.gram, real_inner_comm] using (hG i j).symm
  have hs := covolume_sq_eq_gram_det L b
  rw [hgram] at hs
  have hdet : (G.map (Int.castRingHom ℝ)).det = (G.det : ℝ) := by
    exact ((Int.castRingHom ℝ).map_det G).symm
  rw [hdet] at hs
  have hcpos := ZLattice.covolume_pos L volume
  rcases Int.isUnit_iff.mp hunit with h | h
  · rw [h] at hs
    norm_num only [Int.cast_one, Int.cast_neg] at hs
    nlinarith
  · rw [h] at hs
    norm_num only [Int.cast_one, Int.cast_neg] at hs
    nlinarith [sq_nonneg (ZLattice.covolume L)]

/-- A complete self-dual-lattice-to-short-vector theorem in ranks ≤8.
This theorem has no unproved covolume or shortest-vector hypothesis. -/
theorem selfDual_exists_unit_or_root (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (hnpos : 0 < Module.finrank ℝ E) (hn8 : Module.finrank ℝ E ≤ 8) :
    ∃ x : E, x ∈ L ∧ (‖x‖^2 = 1 ∨ ‖x‖^2 = 2) := by
  apply exists_unit_or_root_covolume_one L hnpos hn8 (selfDual_covolume_one L hL)
  intro x hx
  have hx' : x ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by rwa [hL]
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hx' x hx)
  change (k : ℝ) = inner ℝ x x at hk
  exact ⟨k, by simpa only [real_inner_self_eq_norm_sq] using hk.symm⟩

#print axioms covolume_sq_eq_gram_det
#print axioms selfDual_covolume_one
#print axioms selfDual_exists_unit_or_root
end Wang38I.Classification
