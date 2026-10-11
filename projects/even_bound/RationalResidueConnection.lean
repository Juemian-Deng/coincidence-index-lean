import ResidueParityBridge
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rational matrices, integer numerators, and their actual residue kernels

A positive common denominator is enough; no least-denominator assertion is
made. The coincidence subgroup is defined by the actual rational matrix action.
-/

namespace RationalResidueConnection
open scoped BigOperators

variable {n : ℕ}

/-- A positive common denominator, without any minimality requirement. -/
def commonDenominator (R : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  ∏ ij : Fin n × Fin n, (R ij.1 ij.2).den

theorem commonDenominator_pos (R : Matrix (Fin n) (Fin n) ℚ) :
    0 < commonDenominator R := by
  apply Finset.prod_pos
  intro ij _
  exact (R ij.1 ij.2).den_pos

theorem entry_den_dvd (R : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (R i j).den ∣ commonDenominator R :=
  Finset.dvd_prod_of_mem (fun ij : Fin n × Fin n => (R ij.1 ij.2).den)
    (Finset.mem_univ (i, j))

/-- Integer numerators for the explicit product denominator. -/
def integerNumerator (R : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (R i j).num * (commonDenominator R / (R i j).den : ℕ)

theorem integerNumerator_cast (R : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (integerNumerator R i j : ℚ) = (commonDenominator R : ℚ) * R i j := by
  have hd : ((R i j).den : ℚ) * (commonDenominator R / (R i j).den : ℕ) =
      (commonDenominator R : ℚ) := by
    exact_mod_cast Nat.mul_div_cancel' (entry_den_dvd R i j)
  simp only [integerNumerator, Int.cast_mul, Int.cast_natCast]
  rw [← Rat.den_mul_eq_num]
  calc
    ((R i j).den : ℚ) * R i j * (commonDenominator R / (R i j).den : ℕ) =
        (((R i j).den : ℚ) * (commonDenominator R / (R i j).den : ℕ)) * R i j := by ring
    _ = _ := by rw [hd]

theorem integerNumerator_div (R : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    R i j = (integerNumerator R i j : ℚ) / (commonDenominator R : ℚ) := by
  have hd : (commonDenominator R : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_pos R).ne'
  apply (eq_div_iff hd).mpr
  rw [integerNumerator_cast, mul_comm]

/-- Every finite rational square matrix has an explicit positive presentation. -/
theorem exists_integer_presentation (R : Matrix (Fin n) (Fin n) ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ P : Matrix (Fin n) (Fin n) ℤ,
      ∀ i j, R i j = (P i j : ℚ) / (d : ℚ) :=
  ⟨commonDenominator R, commonDenominator_pos R, integerNumerator R,
    integerNumerator_div R⟩

/-- The subgroup of integer vectors whose actual rational image is integral. -/
def coincidenceSubgroup (R : Matrix (Fin n) (Fin n) ℚ) : AddSubgroup (Fin n → ℤ) where
  carrier := {x | ∃ y : Fin n → ℤ, R.mulVec (fun i => (x i : ℚ)) = fun i => (y i : ℚ)}
  zero_mem' := by exact ⟨0, by ext i; simp [Matrix.mulVec, dotProduct]⟩
  add_mem' := by
    rintro x z ⟨y, hy⟩ ⟨w, hw⟩
    refine ⟨y + w, ?_⟩
    simp only [Pi.add_apply, Int.cast_add]
    change R.mulVec ((fun i => (x i : ℚ)) + (fun i => (z i : ℚ))) =
      (fun i => (y i : ℚ)) + (fun i => (w i : ℚ))
    rw [Matrix.mulVec_add, hy, hw]
  neg_mem' := by
    rintro x ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    simp only [Pi.neg_apply, Int.cast_neg]
    change R.mulVec (-(fun i => (x i : ℚ))) = -(fun i => (y i : ℚ))
    rw [Matrix.mulVec_neg, hy]

theorem mem_coincidenceSubgroup_iff (R : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℤ) :
    x ∈ coincidenceSubgroup R ↔
      ∃ y : Fin n → ℤ, R.mulVec (fun i => (x i : ℚ)) = fun i => (y i : ℚ) := Iff.rfl

variable (R : Matrix (Fin n) (Fin n) ℚ) (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

/-- Scaling commutes with the actual matrix-vector product. -/
theorem numerator_mulVec_cast
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) (x : Fin n → ℤ) (i : Fin n) :
    (P.mulVec x i : ℚ) = (d : ℚ) * R.mulVec (fun j => (x j : ℚ)) i := by
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hP]
  ring

/-- Integrality of Rx is exactly divisibility of Px by the common denominator. -/
theorem mem_coincidence_iff_dvd (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) (x : Fin n → ℤ) :
    x ∈ coincidenceSubgroup R ↔ ∀ i, (d : ℤ) ∣ P.mulVec x i := by
  constructor
  · rintro ⟨y, hy⟩ i
    refine ⟨y i, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [numerator_mulVec_cast R P d hP, hy]
  · intro hx
    choose y hy using hx
    refine ⟨y, ?_⟩
    funext i
    have h := numerator_mulVec_cast R P d hP x i
    rw [hy i] at h
    push_cast at h
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    exact (mul_left_cancel₀ hdq h).symm

/-- The rational coincidence subgroup equals the existing concrete residue kernel. -/
theorem coincidenceSubgroup_eq_residueKernel (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) :
    coincidenceSubgroup R = ResidueParityBridge.residueKernel P d := by
  ext x
  rw [mem_coincidence_iff_dvd R P d hd hP, ResidueParityBridge.mem_residueKernel_iff]

/-- Column orthogonality gives the integer Gram entries, including off-diagonal zeroes. -/
theorem column_gram_entries
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j)
    (horth : R.transpose * R = 1) (i j : Fin n) :
    ∑ k, P k i * P k j = if i = j then (d : ℤ)^2 else 0 := by
  have hr : ∑ k, R k i * R k j = if i = j then (1 : ℚ) else 0 := by
    have h := congrFun (congrFun horth i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  apply Int.cast_injective (α := ℚ)
  push_cast
  calc
    ∑ k, (P k i : ℚ) * (P k j : ℚ) = (d : ℚ)^2 * ∑ k, R k i * R k j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hP, hP]
      ring
    _ = _ := by rw [hr]; split_ifs <;> simp

/-- The numerator matrix satisfies its actual column Gram identity. -/
theorem column_gram
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j)
    (horth : R.transpose * R = 1) :
    P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply] using column_gram_entries R P d hP horth i j

/-- Row orthogonality gives the integer row Gram entries. -/
theorem row_gram_entries
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j)
    (horth : R * R.transpose = 1) (i j : Fin n) :
    ∑ k, P i k * P j k = if i = j then (d : ℤ)^2 else 0 := by
  exact column_gram_entries R.transpose P.transpose d (fun i j => hP j i) horth i j

/-- The numerator matrix satisfies its actual row Gram identity. -/
theorem row_gram
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j)
    (horth : R * R.transpose = 1) :
    P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  exact column_gram R.transpose P.transpose d (fun i j => hP j i) horth

/-- Every column has integer squared norm d². -/
theorem column_normSq
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j)
    (horth : R.transpose * R = 1) (j : Fin n) :
    ∑ i, (P i j)^2 = (d : ℤ)^2 := by
  simpa [pow_two] using column_gram_entries R P d hP horth j j

/-- Every row has integer squared norm d². -/
theorem row_normSq
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j)
    (horth : R * R.transpose = 1) (i : Fin n) :
    ∑ j, (P i j)^2 = (d : ℤ)^2 := by
  simpa [pow_two] using row_gram_entries R P d hP horth i i

/-- The actual coincidence index equals the cardinality of the actual residue image. -/
theorem card_residueImage_eq_coincidence_index (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) :
    Nat.card (ResidueParityBridge.ResidueImage P d) = (coincidenceSubgroup R).index := by
  rw [coincidenceSubgroup_eq_residueKernel R P d hd hP]
  exact ResidueParityBridge.card_image_eq_index P d

/-- Squared-norm evenness of the actual rational coincidence subgroup. -/
def CoincidenceEven : Prop :=
  ∀ x : Fin n → ℤ, x ∈ coincidenceSubgroup R → Even (∑ i, (x i)^2)

/-- Genuine coincidence-lattice evenness supplies the existing residue parity input. -/
theorem kernelEven_of_coincidenceEven (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j)
    (heven : CoincidenceEven R) : ResidueParityBridge.KernelEven P d := by
  apply ResidueParityBridge.kernelEven_of_even_norm P d
  intro x hx
  exact heven x ((mem_coincidence_iff_dvd R P d hd hP x).mpr hx)

/-- The norm and coordinate-sum notions of evenness are equivalent. -/
theorem coincidenceEven_iff_kernelEven (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) :
    CoincidenceEven R ↔ ResidueParityBridge.KernelEven P d := by
  constructor
  · exact kernelEven_of_coincidenceEven R P d hd hP
  · intro heven x hx
    apply ZMod.intCast_eq_zero_iff_even.mp
    rw [ResidueParityBridge.norm_sum_parity]
    apply ZMod.intCast_eq_zero_iff_even.mpr
    exact heven x ((mem_coincidence_iff_dvd R P d hd hP x).mp hx)

/-- The actual coincidence quotient is additively isomorphic to the residue image. -/
noncomputable def coincidenceQuotientEquivImage (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) :
    ((Fin n → ℤ) ⧸ coincidenceSubgroup R) ≃+ ResidueParityBridge.ResidueImage P d :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (coincidenceSubgroup_eq_residueKernel R P d hd hP)).trans
    (ResidueParityBridge.quotientEquivImage P d)

/-- This isomorphism sends each integer vector to its actual residue image. -/
theorem coincidenceQuotientEquivImage_mk (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) (x : Fin n → ℤ) :
    coincidenceQuotientEquivImage R P d hd hP (QuotientAddGroup.mk x) =
      ResidueParityBridge.imageMap P d x := by
  simp [coincidenceQuotientEquivImage, QuotientAddGroup.quotientAddEquivOfEq_mk,
    ResidueParityBridge.quotientEquivImage_mk]

/-- In particular a rational matrix always has a finite coincidence quotient. -/
theorem finite_coincidence_quotient : Finite ((Fin n → ℤ) ⧸ coincidenceSubgroup R) := by
  let d := commonDenominator R
  have hd : 0 < d := commonDenominator_pos R
  let : NeZero d := ⟨hd.ne'⟩
  exact Finite.of_equiv (ResidueParityBridge.ResidueImage (integerNumerator R) d)
    (coincidenceQuotientEquivImage R (integerNumerator R) d hd
      (integerNumerator_cast R)).symm.toEquiv

/-- Coordinate labels in the coincidence quotient really are the residue columns. -/
theorem coincidenceQuotientEquivImage_coordinate (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) (j : Fin n) :
    coincidenceQuotientEquivImage R P d hd hP (QuotientAddGroup.mk (Pi.single j 1)) =
      ResidueParityBridge.columnLabel P d j :=
  coincidenceQuotientEquivImage_mk R P d hd hP (Pi.single j 1)

/-- A displayed fraction presentation is interchangeable with the scaled-entry form. -/
theorem presentation_iff_scaled (hd : 0 < d) :
    (∀ i j, R i j = (P i j : ℚ) / (d : ℚ)) ↔
      (∀ i j, (P i j : ℚ) = (d : ℚ) * R i j) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  constructor
  · intro h i j
    have hh := (eq_div_iff hdq).mp (h i j)
    simpa only [mul_comm] using hh.symm
  · intro h i j
    apply (eq_div_iff hdq).mpr
    simpa only [mul_comm] using (h i j).symm

end RationalResidueConnection
