import RootParityIndex

/-! The root-perpendicular determinant-two calculation from actual parity
index, orthogonal integral decomposition, and geometric Gram/covolume identities. -/
noncomputable section
namespace Wang38I.Classification
open Module MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma root_mem_rootParityLattice (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    u ∈ rootParityLattice L hL u huL := by
  apply (mem_rootParityLattice L hL u huL ⟨u, huL⟩).mpr
  have he : rootPairingMap L hL u huL ⟨u, huL⟩ = 2 := by
    apply Int.cast_injective (α := ℝ)
    rw [rootPairingMap_cast, hu]
    norm_num
  change ((rootPairingMap L hL u huL ⟨u, huL⟩ : ℤ) : ZMod 2) = 0
  rw [he]
  decide

lemma complement_mem_rootParityLattice (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (y : rootComplement L u) :
    y.val.val ∈ rootParityLattice L hL u huL := by
  have he : rootPairingMap L hL u huL ⟨y.val.val, y.prop⟩ = 0 := by
    apply Int.cast_injective (α := ℝ)
    rw [rootPairingMap_cast]
    simpa only [Int.cast_zero] using (show inner ℝ u y.val.val = 0 from y.val.prop)
  apply (mem_rootParityLattice L hL u huL ⟨y.val.val, y.prop⟩).mpr
  change ((rootPairingMap L hL u huL ⟨y.val.val, y.prop⟩ : ℤ) : ZMod 2) = 0
  rw [he]
  rfl

def rootParityJoin (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    (ℤ × rootComplement L u) →ₗ[ℤ] rootParityLattice L hL u huL where
  toFun t := ⟨t.1 • u + t.2.val.val,
    (rootParityLattice L hL u huL).add_mem
      ((rootParityLattice L hL u huL).smul_mem t.1 (root_mem_rootParityLattice L hL u huL hu))
      (complement_mem_rootParityLattice L hL u huL t.2)⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' a x := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
      Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_add, smul_smul, smul_eq_mul]

lemma rootParity_decomposition (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2)
    (x : rootParityLattice L hL u huL) :
    ∃ k : ℤ, ∃ y : rootComplement L u, x.val = k • u + y.val.val := by
  let xL : L := ⟨x.val, rootParityLattice_le L hL u huL x.prop⟩
  have he := (mem_rootParityLattice L hL u huL xL).mp x.prop
  have hd : (2 : ℤ) ∣ rootPairingMap L hL u huL xL := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp he
  obtain ⟨k, hk⟩ := hd
  have hp : inner ℝ u x.val = 2 * (k : ℝ) := by
    have hh := rootPairingMap_cast L hL u huL xL
    rw [hk] at hh
    push_cast at hh
    exact hh.symm
  have hproj : (rootProjection u hu x.val).val = x.val - k • u := by
    rw [rootProjection_coe, hp]
    have hdiv : (2 * (k : ℝ)) / 2 = (k : ℝ) := by ring
    rw [hdiv, Int.cast_smul_eq_zsmul]
  have hprojL : rootProjection u hu x.val ∈ rootComplement L u := by
    change (rootProjection u hu x.val).val ∈ L
    rw [hproj]
    exact L.sub_mem xL.prop (L.smul_mem k huL)
  refine ⟨k, ⟨rootProjection u hu x.val, hprojL⟩, ?_⟩
  change x.val = k • u + (rootProjection u hu x.val).val
  rw [hproj]
  abel

/-- Literal integral orthogonal direct-sum equivalence for the parity lattice. -/
def rootParitySplitting (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    (ℤ × rootComplement L u) ≃ₗ[ℤ] rootParityLattice L hL u huL :=
  LinearEquiv.ofBijective (rootParityJoin L hL u huL hu) (by
    constructor
    · rintro ⟨k, y⟩ ⟨l, z⟩ h
      have he := congrArg (fun t : rootParityLattice L hL u huL => inner ℝ u t.val) h
      change inner ℝ u (k • u + y.val.val) = inner ℝ u (l • u + z.val.val) at he
      have hy : inner ℝ u y.val.val = 0 := y.val.prop
      have hz : inner ℝ u z.val.val = 0 := z.val.prop
      simp only [inner_add_right, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right,
        hu, hy, hz, add_zero] at he
      have hkl : k = l := by
        apply Int.cast_injective (α := ℝ)
        linarith
      subst l
      have hv := congrArg (fun t : rootParityLattice L hL u huL => t.val) h
      change k • u + y.val.val = k • u + z.val.val at hv
      exact Prod.ext rfl (Subtype.ext (Subtype.ext (add_left_cancel hv)))
    · intro x
      obtain ⟨k, y, hy⟩ := rootParity_decomposition L hL u huL hu x
      exact ⟨(k, y), Subtype.ext hy.symm⟩)

@[simp] lemma rootParitySplitting_apply (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) (t : ℤ × rootComplement L u) :
    (rootParitySplitting L hL u huL hu t).val = t.1 • u + t.2.val.val := rfl

/-- Exact geometric determinant-two identity for the actual perpendicular
lattice, proved from the index-two parity lattice. -/
theorem rootComplement_covolume_sq [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (u : E) (huL : u ∈ L) (hu : inner ℝ u u = 2) :
    (ZLattice.covolume (rootComplement L u))^2 = 2 := by
  classical
  let : IsZLattice ℝ (rootComplement L u) := rootComplement_isZLattice L hL u huL hu
  let : IsZLattice ℝ (rootParityLattice L hL u huL) := rootParityLattice_isZLattice L hL u huL
  let b := Module.Free.chooseBasis ℤ (rootComplement L u)
  let bS := ((Basis.singleton Unit ℤ).prod b).map (rootParitySplitting L hL u huL hu)
  have hleft : ∀ a : Unit, (bS (Sum.inl a)).val = u := by
    intro a
    simp [bS, Basis.prod_apply]
  have hright : ∀ i, (bS (Sum.inr i)).val = (b i).val.val := by
    intro i
    simp [bS, Basis.prod_apply]
  have hgram : Matrix.gram ℝ (fun i => (bS i).val) =
      Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => (2 : ℝ))) 0 0
        (Matrix.gram ℝ (fun i => (b i).val)) := by
    ext i j
    rcases i with a | i <;> rcases j with c | j
    · simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, hleft]
      exact hu
    · simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, hleft, hright]
      exact (b j).val.prop
    · simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, hleft, hright]
      rw [real_inner_comm]
      exact (b i).val.prop
    · simp [Matrix.gram_apply, hright]
  have hS := covolume_sq_eq_gram_det (rootParityLattice L hL u huL) bS
  have hC := covolume_sq_eq_gram_det (rootComplement L u) b
  rw [hgram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique] at hS
  rw [rootParityLattice_covolume L hL u huL hu, ← hC] at hS
  change (2 : ℝ)^2 = 2 * (ZLattice.covolume (rootComplement L u))^2 at hS
  nlinarith

#print axioms rootParitySplitting
#print axioms rootComplement_covolume_sq
end Wang38I.Classification
