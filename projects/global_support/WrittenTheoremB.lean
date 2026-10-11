import EvenSmallClassBound
import ActualLargeClassBound
import MaximumClass
import ActualSignClassReduction
import OrthogonalPresentation

/-!
# The even coincidence-lattice dimension bound

Both exported conclusions concern the actual matrix and its actual residue
image/coincidence lattice. The integer theorem allows any positive denominator.
All sign capacities, normal forms, reduced energy, dual cardinalities, and
parity characters are obtained from previously proved concrete constructions.
-/

namespace WrittenTheoremB
open scoped BigOperators
open ResidueParityBridge ActualFiberBounds FixedSignCapacity MatrixClassAdapters

variable {n : ℕ}

/-- Integer formulation with no normal-form, cardinality, or capacity premises.
The evenness hypothesis refers exactly to integer vectors whose image under P
is divisible coordinatewise by d. -/
theorem integer_even_bound (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (heven : KernelEven P d) : n ≤ 2 * Nat.card (ResidueImage P d) := by
  classical
  by_cases hsmall : ∀ j, (signClass (columnLabel P d) j).card ≤ 8
  · exact EvenSmallClassBound.even_bound_of_small_classes P d hd hrows hcols heven hsmall
  let : NeZero d := ⟨by omega⟩
  obtain ⟨j₀, hlarge, hmax⟩ := MaximumClass.exists_large_maximum P d hsmall
  let J := absoluteClass P d j₀
  have hlarge' : 9 ≤ J.card := by
    simpa only [column_class_eq] using hlarge
  have hj₀ : j₀ ∈ J := by simp [J, absoluteClass]
  let j : J := ⟨j₀, hj₀⟩
  have hc : ∀ k ∈ J, columnResidue P d k = columnResidue P d j ∨
      columnResidue P d k = -columnResidue P d j := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  obtain ⟨I, w, δ, a, hcard, _, ha, _, _, hcol, hcap, henergy⟩ :=
    ReducedColumnEnergy.actual_sign_class_reduced_column P d
      (SignClassTransfer.orthogonalColumns_of_gram P d hcols) J (by omega) j
      (columnLabel_ne_zero P d heven j) hc
  apply ActualLargeClassBound.bound_from_reduced_column P d j I w δ a
    (by omega) ha hcol hcap henergy
  · exact IntegerEvenCore.rowEvaluation_ne_zero P d hd hrows heven
  · intro i
    rw [hcard]
    apply row_evaluation_class_card_le P d J.card hd (by omega) hrows
    intro k
    simpa only [column_class_eq] using hmax k

/-- Equivalent index formulation for the actual integer divisibility kernel. -/
theorem integer_even_index_bound (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (heven : KernelEven P d) : n ≤ 2 * (residueKernel P d).index := by
  rw [← card_image_eq_index]
  exact integer_even_bound P d hd hrows hcols heven

/-- The written theorem for an actual rational orthogonal matrix and its
actual coincidence subgroup: even squared norms force n ≤ 2 times the index.
No choice of denominator, image model, or lattice index is a premise. -/
theorem writtenTheoremB (R : Matrix (Fin n) (Fin n) ℚ)
    (horth : R ∈ Matrix.orthogonalGroup (Fin n) ℚ)
    (heven : RationalResidueConnection.CoincidenceEven R) :
    n ≤ 2 * (RationalResidueConnection.coincidenceSubgroup R).index := by
  obtain ⟨d, hd, P, hP, _, hcols, hrows, hkernel⟩ :=
    RationalResidueConnection.exists_orthogonal_integer_presentation R horth
  rw [hkernel]
  apply integer_even_index_bound P d hd hrows hcols
  exact RationalResidueConnection.kernelEven_of_coincidenceEven R P d hd hP heven

end WrittenTheoremB
