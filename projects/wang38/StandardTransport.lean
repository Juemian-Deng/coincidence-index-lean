import IndexTwoStandard

noncomputable section
open scoped BigOperators
namespace Wang38I.Classification
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def isometryLatticeMap (e : E ≃ₗᵢ[ℝ] F) (L : Submodule ℤ E) : Submodule ℤ F :=
  L.map (e.toLinearEquiv.toLinearMap.restrictScalars ℤ)

@[simp] theorem mem_isometryLatticeMap (e : E ≃ₗᵢ[ℝ] F) (L : Submodule ℤ E) (x : F) :
    x ∈ isometryLatticeMap e L ↔ e.symm x ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩

 theorem isometryLatticeMap_selfDual (e : E ≃ₗᵢ[ℝ] F) (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L) :
    LinearMap.BilinForm.dualSubmodule (innerₗ _) (isometryLatticeMap e L) =
      isometryLatticeMap e L := by
  ext x
  rw [mem_isometryLatticeMap]
  conv_rhs => rw [← hL]
  constructor
  · intro hx y hy
    have h := hx (e y) ((mem_isometryLatticeMap e L (e y)).mpr (by simpa using hy))
    change inner ℝ x (e y) ∈ (1 : Submodule ℤ ℝ) at h
    change inner ℝ (e.symm x) y ∈ (1 : Submodule ℤ ℝ)
    rwa [← e.inner_map_map (e.symm x) y, e.apply_symm_apply]
  · intro hx y hy
    have h := hx (e.symm y) ((mem_isometryLatticeMap e L _).mp hy)
    change inner ℝ (e.symm x) (e.symm y) ∈ (1 : Submodule ℤ ℝ) at h
    change inner ℝ x y ∈ (1 : Submodule ℤ ℝ)
    simpa only [← e.inner_map_map (e.symm x) (e.symm y), e.apply_symm_apply] using h

 theorem isometryLatticeMap_inf (e : E ≃ₗᵢ[ℝ] F) (L Z : Submodule ℤ E) :
    isometryLatticeMap e (L ⊓ Z) = isometryLatticeMap e L ⊓ isometryLatticeMap e Z := by
  ext x
  simp

 theorem isometryLatticeMap_relIndex (e : E ≃ₗᵢ[ℝ] F) (L Z : Submodule ℤ E) :
    (isometryLatticeMap e L).toAddSubgroup.relIndex
      (isometryLatticeMap e Z).toAddSubgroup = L.toAddSubgroup.relIndex Z.toAddSubgroup := by
  exact AddSubgroup.relIndex_map_map_of_injective
    (f := e.toLinearEquiv.toAddEquiv.toAddMonoidHom) L.toAddSubgroup Z.toAddSubgroup e.injective

 theorem orthonormal_span_map {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) :
    isometryLatticeMap b.repr (Submodule.span ℤ (Set.range b)) = standardIntegerLattice n := by
  simp only [isometryLatticeMap, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe]
  simp [OrthonormalBasis.repr_self, EuclideanSpace.basisFun_apply]

/-- Coordinate transport through an actual linear isometry preserves both
relative intersection indices and literal self-duality. -/
theorem indexTwo_isometry_alternative {n : ℕ} (hn : 0 < n) (hn8 : n ≤ 8)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (L K : Submodule ℤ E)
    (hK : isometryLatticeMap e K = standardIntegerLattice n)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    (hiL : (L ⊓ K).toAddSubgroup.relIndex L.toAddSubgroup = 2)
    (hiK : (L ⊓ K).toAddSubgroup.relIndex K.toAddSubgroup = 2) :
    (∃ v ∈ L, inner ℝ v v = 1) ∨
      (n = 8 ∧ ∀ x ∈ L, ∃ m : ℤ, inner ℝ x x = 2*m) := by
  have hiL' : (isometryLatticeMap e L ⊓ standardIntegerLattice n).toAddSubgroup.relIndex
      (isometryLatticeMap e L).toAddSubgroup = 2 := by
    rw [← hK, ← isometryLatticeMap_inf, isometryLatticeMap_relIndex]
    exact hiL
  have hiK' : (isometryLatticeMap e L ⊓ standardIntegerLattice n).toAddSubgroup.relIndex
      (standardIntegerLattice n).toAddSubgroup = 2 := by
    rw [← hK, ← isometryLatticeMap_inf, isometryLatticeMap_relIndex]
    exact hiK
  rcases indexTwo_standard_alternative hn hn8 (isometryLatticeMap e L)
    (isometryLatticeMap_selfDual e L hL) hiL' hiK' with h | ⟨hn, heven⟩
  · obtain ⟨v, hv, hnorm⟩ := h
    exact Or.inl ⟨e.symm v, (mem_isometryLatticeMap e L v).mp hv,
      by simpa only [e.symm.inner_map_map] using hnorm⟩
  · right
    refine ⟨hn, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := heven (e x)
      ((mem_isometryLatticeMap e L (e x)).mpr (by simpa using hx))
    exact ⟨m, by simpa only [e.inner_map_map] using hm⟩

/-- A genuine isometric coordinate realization constructed from an
orthonormal integer basis of the actual full lattice. -/
theorem indexTwo_orthonormalIntegerBasis_alternative
    [FiniteDimensional ℝ E] {n : ℕ} (hn : 0 < n) (hn8 : n ≤ 8)
    (L K : Submodule ℤ E) [DiscreteTopology K] [IsZLattice ℝ K]
    (b : Module.Basis (Fin n) ℤ K)
    (hb : ∀ i j, inner ℝ (b i).val (b j).val = if i = j then 1 else 0)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    (hiL : (L ⊓ K).toAddSubgroup.relIndex L.toAddSubgroup = 2)
    (hiK : (L ⊓ K).toAddSubgroup.relIndex K.toAddSubgroup = 2) :
    (∃ v ∈ L, inner ℝ v v = 1) ∨
      (n = 8 ∧ ∀ x ∈ L, ∃ m : ℤ, inner ℝ x x = 2*m) := by
  let bR := b.ofZLatticeBasis ℝ
  have ho : Orthonormal ℝ bR := by
    rw [orthonormal_iff_ite]
    simpa only [bR, Module.Basis.ofZLatticeBasis_apply] using hb
  let o := bR.toOrthonormalBasis ho
  have hspan : Submodule.span ℤ (Set.range o) = K := by
    rw [show (o : Fin n → E) = bR from Module.Basis.coe_toOrthonormalBasis bR ho]
    exact b.ofZLatticeBasis_span ℝ
  apply indexTwo_isometry_alternative hn hn8 o.repr L K _ hL hiL hiK
  rw [← hspan]
  exact orthonormal_span_map o

/-- Squared-norm formulation of the actual-lattice transport theorem. -/
theorem indexTwo_orthonormalIntegerBasis_norm_sq_alternative
    [FiniteDimensional ℝ E] {n : ℕ} (hn : 0 < n) (hn8 : n ≤ 8)
    (L K : Submodule ℤ E) [DiscreteTopology K] [IsZLattice ℝ K]
    (b : Module.Basis (Fin n) ℤ K)
    (hb : ∀ i j, inner ℝ (b i).val (b j).val = if i = j then 1 else 0)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    (hiL : (L ⊓ K).toAddSubgroup.relIndex L.toAddSubgroup = 2)
    (hiK : (L ⊓ K).toAddSubgroup.relIndex K.toAddSubgroup = 2) :
    (∃ v ∈ L, ‖v‖^2 = 1) ∨
      (n = 8 ∧ ∀ x ∈ L, ∃ m : ℤ, ‖x‖^2 = 2*m) := by
  simpa only [real_inner_self_eq_norm_sq] using
    indexTwo_orthonormalIntegerBasis_alternative hn hn8 L K b hb hL hiL hiK

#print axioms isometryLatticeMap_selfDual
#print axioms isometryLatticeMap_relIndex
#print axioms orthonormal_span_map
#print axioms indexTwo_isometry_alternative
#print axioms indexTwo_orthonormalIntegerBasis_alternative
#print axioms indexTwo_orthonormalIntegerBasis_norm_sq_alternative
end Wang38I.Classification
