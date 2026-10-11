import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Concrete residue image and descended coordinate parity

The matrix is an actual finite square integer matrix. No rational orthogonality
or lattice geometry is assumed. The evenness input states explicitly that the
integer vectors sent to zero modulo d have even coordinate sum.
-/

namespace ResidueParityBridge
open scoped BigOperators

variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

/-- The actual integer matrix followed by reduction modulo d. -/
def residueMap : (Fin n → ℤ) →+ (Fin n → ZMod d) where
  toFun x i := (P.mulVec x i : ZMod d)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [Matrix.mulVec_add]

/-- The actual image as an additive subgroup, with its inherited group law. -/
abbrev ResidueImage := (residueMap P d).range

/-- Integer coordinate vectors mapped into the actual image. -/
def imageMap : (Fin n → ℤ) →+ ResidueImage P d := (residueMap P d).rangeRestrict

/-- The divisibility kernel of the integer matrix. -/
abbrev residueKernel := (residueMap P d).ker

theorem mem_residueKernel_iff (x : Fin n → ℤ) :
    x ∈ residueKernel P d ↔ ∀ i, (d : ℤ) ∣ P.mulVec x i := by
  change (fun i => (P.mulVec x i : ZMod d)) = 0 ↔ _
  rw [funext_iff]
  simp only [Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The first isomorphism theorem for this concrete residue matrix map. -/
noncomputable def quotientEquivImage :
    ((Fin n → ℤ) ⧸ residueKernel P d) ≃+ ResidueImage P d :=
  QuotientAddGroup.quotientKerEquivRange (residueMap P d)

theorem quotientEquivImage_mk (x : Fin n → ℤ) :
    quotientEquivImage P d (QuotientAddGroup.mk x) = imageMap P d x := rfl

theorem card_image_eq_index : Nat.card (ResidueImage P d) = (residueKernel P d).index :=
  (AddSubgroup.index_ker (residueMap P d)).symm

instance finite_image [NeZero d] : Finite (ResidueImage P d) := inferInstance

instance finite_quotient [NeZero d] : Finite ((Fin n → ℤ) ⧸ residueKernel P d) :=
  Finite.of_equiv (ResidueImage P d) (quotientEquivImage P d).symm.toEquiv

theorem image_annihilated (v : ResidueImage P d) : d • v = 0 := by
  apply Subtype.ext
  ext i
  simp [nsmul_eq_mul]

/-- The label of coordinate j is the image of the integer unit vector e_j. -/
def columnLabel (j : Fin n) : ResidueImage P d := imageMap P d (Pi.single j 1)

/-- Coordinate labels really are the residue columns of P. -/
theorem columnLabel_apply (i j : Fin n) :
    (columnLabel P d j).val i = (P i j : ZMod d) := by
  change (P.mulVec (Pi.single j 1) i : ZMod d) = _
  simp

theorem imageMap_eq_sum_labels (x : Fin n → ℤ) :
    imageMap P d x = ∑ j, x j • columnLabel P d j := by
  apply Subtype.ext
  ext i
  change ((P.mulVec x i : ℤ) : ZMod d) = _
  simp [columnLabel_apply, Matrix.mulVec, dotProduct,
    Finset.sum_apply, zsmul_eq_mul, mul_comm]

/-- Every element is an integer linear combination of the actual columns. -/
theorem exists_sum_labels (v : ResidueImage P d) :
    ∃ x : Fin n → ℤ, v = ∑ j, x j • columnLabel P d j := by
  obtain ⟨x, hx⟩ := (residueMap P d).rangeRestrict_surjective v
  exact ⟨x, hx.symm.trans (imageMap_eq_sum_labels P d x)⟩

/-- An explicit generating statement for the coordinate labels. -/
theorem labels_generate : AddSubgroup.closure (Set.range (columnLabel P d)) = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨x, rfl⟩ := exists_sum_labels P d v
  exact AddSubgroup.sum_mem _ (fun j _ =>
    AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self j)) (x j))

/-- The parity of the integer coordinate sum, before quotienting. -/
def coordinateParity : (Fin n → ℤ) →+ ZMod 2 where
  toFun x := ((∑ i, x i : ℤ) : ZMod 2)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

/-- Evenness is an assertion about the actual divisibility kernel. -/
def KernelEven : Prop :=
  ∀ x : Fin n → ℤ, (∀ i, (d : ℤ) ∣ P.mulVec x i) → Even (∑ i, x i)

theorem kernel_le_parity (heven : KernelEven P d) :
    (imageMap P d).ker ≤ coordinateParity.ker := by
  intro x hx
  apply ZMod.intCast_eq_zero_iff_even.mpr
  apply heven
  apply (mem_residueKernel_iff P d x).mp
  simpa only [imageMap, AddMonoidHom.ker_rangeRestrict] using hx

/-- Parity descended from the explicit integer sum map, using kernel evenness. -/
noncomputable def parityCharacter (heven : KernelEven P d) : ResidueImage P d →+ ZMod 2 :=
  (imageMap P d).liftOfSurjective (residueMap P d).rangeRestrict_surjective
    ⟨coordinateParity, kernel_le_parity P d heven⟩

theorem parityCharacter_imageMap (heven : KernelEven P d) (x : Fin n → ℤ) :
    parityCharacter P d heven (imageMap P d x) = ((∑ i, x i : ℤ) : ZMod 2) := by
  simp [parityCharacter, AddMonoidHom.liftOfSurjective, coordinateParity]

theorem parityCharacter_columnLabel (heven : KernelEven P d) (j : Fin n) :
    parityCharacter P d heven (columnLabel P d j) = 1 := by
  rw [columnLabel, parityCharacter_imageMap]
  simp

/-- Positive dimension forces the descended parity to be nontrivial. -/
theorem parityCharacter_ne_zero (heven : KernelEven P d) (hn : 0 < n) :
    parityCharacter P d heven ≠ 0 := by
  intro h
  have hh := parityCharacter_columnLabel P d heven ⟨0, hn⟩
  rw [h] at hh
  exact zero_ne_one hh

/-- More strongly, the actual descended parity character is onto C₂. -/
theorem parityCharacter_surjective (heven : KernelEven P d) (hn : 0 < n) :
    Function.Surjective (parityCharacter P d heven) := by
  intro z
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨a • columnLabel P d ⟨0, hn⟩, ?_⟩
  rw [map_zsmul, parityCharacter_columnLabel, zsmul_eq_mul, mul_one]

/-- The odd coset, constructed inside the actual matrix image. -/
abbrev OddImage (heven : KernelEven P d) :=
  {v : ResidueImage P d // parityCharacter P d heven v = 1}

theorem parity_kernel_index (heven : KernelEven P d) (hn : 0 < n) :
    (parityCharacter P d heven).ker.index = 2 := by
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top_of_surjective _ (parityCharacter_surjective P d heven hn)]
  simp

/-- Exact half-cardinality, avoiding any rounded natural-number division. -/
theorem twice_card_oddImage (heven : KernelEven P d) (hn : 0 < n) :
    2 * Nat.card (OddImage P d heven) = Nat.card (ResidueImage P d) := by
  have hc : Nat.card (OddImage P d heven) = Nat.card (parityCharacter P d heven).ker :=
    Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective
      (parityCharacter_surjective P d heven hn) 1)
  rw [hc, Nat.mul_comm]
  have h := (parityCharacter P d heven).ker.card_mul_index
  rwa [parity_kernel_index P d heven hn] at h

theorem card_oddImage_eq_half (heven : KernelEven P d) (hn : 0 < n) :
    Nat.card (OddImage P d heven) = Nat.card (ResidueImage P d) / 2 := by
  rw [← twice_card_oddImage P d heven hn, Nat.mul_div_right]
  decide

theorem twice_card_oddImage_eq_index (heven : KernelEven P d) (hn : 0 < n) :
    2 * Nat.card (OddImage P d heven) = (residueKernel P d).index := by
  rw [twice_card_oddImage P d heven hn, card_image_eq_index]

/-- Interface for the pre-existing finite-type parity-orbit capacity lemma. -/
theorem twice_fintype_card_oddImage (heven : KernelEven P d) (hn : 0 < n)
    [Fintype (OddImage P d heven)] :
    2 * Fintype.card (OddImage P d heven) = (residueKernel P d).index := by
  rw [← Nat.card_eq_fintype_card]
  exact twice_card_oddImage_eq_index P d heven hn

/-- Negation preserves the odd coset, including elements fixed by negation. -/
def oddNeg (heven : KernelEven P d) (v : OddImage P d heven) : OddImage P d heven :=
  ⟨-v.val, by rw [map_neg, v.property]; decide⟩

theorem oddNeg_involutive (heven : KernelEven P d) :
    Function.Involutive (oddNeg P d heven) := by
  intro v
  apply Subtype.ext
  exact neg_neg v.val

/-- Every coordinate has a concrete label in this odd coset. -/
noncomputable def oddColumnLabel (heven : KernelEven P d) (j : Fin n) : OddImage P d heven :=
  ⟨columnLabel P d j, parityCharacter_columnLabel P d heven j⟩

theorem columnLabel_ne_zero (heven : KernelEven P d) (j : Fin n) :
    columnLabel P d j ≠ 0 := by
  intro hz
  have h := parityCharacter_columnLabel P d heven j
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- Label equality is precisely equality of the actual residue columns. -/
theorem columnLabel_eq_iff (j k : Fin n) :
    columnLabel P d j = columnLabel P d k ↔
      ∀ i, (P i j : ZMod d) = (P i k : ZMod d) := by
  constructor
  · intro h i
    simpa only [columnLabel_apply] using congrArg (fun v : ResidueImage P d => v.val i) h
  · intro h
    apply Subtype.ext
    exact funext (fun i => by simpa only [columnLabel_apply] using h i)

/-- Negative-label equality is precisely negated equality of actual residue columns. -/
theorem columnLabel_eq_neg_iff (j k : Fin n) :
    columnLabel P d j = -columnLabel P d k ↔
      ∀ i, (P i j : ZMod d) = -(P i k : ZMod d) := by
  constructor
  · intro h i
    simpa only [AddSubgroup.coe_neg, Pi.neg_apply, columnLabel_apply] using
      congrArg (fun v : ResidueImage P d => v.val i) h
  · intro h
    apply Subtype.ext
    exact funext (fun i => by simpa only [AddSubgroup.coe_neg, Pi.neg_apply,
      columnLabel_apply] using h i)

/-- Actual coordinate evaluation restricted to the actual image. -/
def rowEvaluation (i : Fin n) : ResidueImage P d →+ ZMod d :=
  (Pi.evalAddMonoidHom (fun _ : Fin n => ZMod d) i).comp (residueMap P d).range.subtype

theorem rowEvaluation_columnLabel (i j : Fin n) :
    rowEvaluation P d i (columnLabel P d j) = (P i j : ZMod d) := columnLabel_apply P d i j

/-- Homomorphisms out of the image are determined by the actual columns. -/
theorem hom_ext_on_columns {A : Type*} [AddCommGroup A]
    (f g : ResidueImage P d →+ A)
    (h : ∀ j, f (columnLabel P d j) = g (columnLabel P d j)) : f = g := by
  ext v
  obtain ⟨x, rfl⟩ := exists_sum_labels P d v
  simp only [map_sum, map_zsmul, h]

/-- Two evaluation functionals are equal exactly when the residue rows agree. -/
theorem rowEvaluation_eq_iff (i k : Fin n) :
    rowEvaluation P d i = rowEvaluation P d k ↔
      ∀ j, (P i j : ZMod d) = (P k j : ZMod d) := by
  constructor
  · intro h j
    simpa only [rowEvaluation_columnLabel] using
      congrArg (fun f : ResidueImage P d →+ ZMod d => f (columnLabel P d j)) h
  · intro h
    exact hom_ext_on_columns P d _ _ (fun j => by simpa only [rowEvaluation_columnLabel] using h j)

/-- Negated evaluation functionals detect precisely negated residue rows. -/
theorem rowEvaluation_eq_neg_iff (i k : Fin n) :
    rowEvaluation P d i = -rowEvaluation P d k ↔
      ∀ j, (P i j : ZMod d) = -(P k j : ZMod d) := by
  constructor
  · intro h j
    simpa only [AddMonoidHom.neg_apply, rowEvaluation_columnLabel] using
      congrArg (fun f : ResidueImage P d →+ ZMod d => f (columnLabel P d j)) h
  · intro h
    exact hom_ext_on_columns P d _ _ (fun j => by
      simpa only [AddMonoidHom.neg_apply, rowEvaluation_columnLabel] using h j)

/-- An evaluation functional vanishes exactly when its actual residue row is zero. -/
theorem rowEvaluation_eq_zero_iff (i : Fin n) :
    rowEvaluation P d i = 0 ↔ ∀ j, (P i j : ZMod d) = 0 := by
  constructor
  · intro h j
    simpa only [AddMonoidHom.zero_apply, rowEvaluation_columnLabel] using
      congrArg (fun f : ResidueImage P d →+ ZMod d => f (columnLabel P d j)) h
  · intro h
    exact hom_ext_on_columns P d _ _ (fun j => by
      simpa only [AddMonoidHom.zero_apply, rowEvaluation_columnLabel] using h j)

/-- Squared norm and coordinate sum have identical parity over the integers. -/
theorem norm_sum_parity (x : Fin n → ℤ) :
    ((∑ i, (x i)^2 : ℤ) : ZMod 2) = ((∑ i, x i : ℤ) : ZMod 2) := by
  apply sub_eq_zero.mp
  rw [← Int.cast_sub, ZMod.intCast_eq_zero_iff_even]
  apply even_iff_two_dvd.mpr
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  simpa only [pow_two, mul_sub, mul_one] using (Int.even_mul_pred_self (x i)).two_dvd

/-- Thus the usual even squared-norm condition implies the explicit parity input. -/
theorem kernelEven_of_even_norm
    (h : ∀ x : Fin n → ℤ, (∀ i, (d : ℤ) ∣ P.mulVec x i) → Even (∑ i, (x i)^2)) :
    KernelEven P d := by
  intro x hx
  apply ZMod.intCast_eq_zero_iff_even.mp
  rw [← norm_sum_parity]
  exact ZMod.intCast_eq_zero_iff_even.mpr (h x hx)

end ResidueParityBridge
