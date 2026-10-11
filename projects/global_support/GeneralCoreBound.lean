import GeneralSmallClassBound
import ActualLargeClassBound
import ActualSignClassReduction
import OrthogonalPresentation

/-! Unrestricted coincidence-index bounds for the actual nonintegral core. -/
namespace GeneralCoreBound
open scoped BigOperators
open ResidueParityBridge ActualFiberBounds FixedSignCapacity MatrixClassAdapters
variable {n : ℕ}

/-- A failed cap-four branch has an occupied maximum of size at least five. -/
theorem exists_large_maximum (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)
    (hnot : ¬ ∀ j, (signClass (columnLabel P d) j).card ≤ 4) :
    ∃ j, 5 ≤ (signClass (columnLabel P d) j).card ∧
      ∀ k, (signClass (columnLabel P d) k).card ≤ (signClass (columnLabel P d) j).card := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
    (fun i => (signClass (columnLabel P d) i).card) ⟨j, Finset.mem_univ j⟩
  refine ⟨k, ?_, fun i => hk i (Finset.mem_univ i)⟩
  have h := hk j (Finset.mem_univ j)
  omega

/-- Actual integer orthogonal core, at any positive denominator: dimension is
at most twice the actual residue-image cardinality. No evenness is assumed. -/
theorem integer_core_bound (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hnonzero : ∀ j, columnLabel P d j ≠ 0) :
    n ≤ 2 * Nat.card (ResidueImage P d) := by
  classical
  by_cases hsmall : ∀ j, (signClass (columnLabel P d) j).card ≤ 4
  · exact GeneralSmallClassBound.bound_of_small_classes P d hd hrows hcols hnonzero hsmall
  let : NeZero d := ⟨by omega⟩
  obtain ⟨j₀, hlarge, hmax⟩ := exists_large_maximum P d hsmall
  let J := absoluteClass P d j₀
  have hlarge' : 5 ≤ J.card := by
    simpa only [column_class_eq] using hlarge
  have hj₀ : j₀ ∈ J := by simp [J, absoluteClass]
  let j : J := ⟨j₀, hj₀⟩
  have hc : ∀ k ∈ J, columnResidue P d k = columnResidue P d j ∨
      columnResidue P d k = -columnResidue P d j := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  obtain ⟨I, w, δ, a, hcard, _, ha, _, _, hcol, hcap, henergy⟩ :=
    ReducedColumnEnergy.actual_sign_class_reduced_column P d
      (SignClassTransfer.orthogonalColumns_of_gram P d hcols) J hlarge' j
      (hnonzero j) hc
  apply ActualLargeClassBound.bound_from_reduced_column P d j I w δ a
    (by omega) ha hcol hcap henergy
  · exact IntegerCoreSupport.rowEvaluation_ne_zero P d hd hrows
      (IntegerCoreSupport.strict_core P d hd hcols hnonzero)
  · intro i
    rw [hcard]
    apply row_evaluation_class_card_le P d J.card hd (by omega) hrows
    intro k
    simpa only [column_class_eq] using hmax k

/-- The same theorem stated with the actual divisibility-kernel index. -/
theorem integer_core_index_bound (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) (hd : 0 < d)
    (hrows : P * P.transpose = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcols : P.transpose * P = (d : ℤ)^2 • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hnonzero : ∀ j, columnLabel P d j ≠ 0) :
    n ≤ 2 * (residueKernel P d).index := by
  rw [← card_image_eq_index]
  exact integer_core_bound P d hd hrows hcols hnonzero

/-- Literal nonintegrality of every column of a rational matrix. -/
def NonintegralColumns (R : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ j, ¬ ∃ z : Fin n → ℤ, ∀ i, R i j = (z i : ℚ)

/-- Nonintegral rational columns give nonzero actual labels at any denominator. -/
theorem nonzero_columns_of_nonintegral (R : Matrix (Fin n) (Fin n) ℚ)
    (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) (hd : 0 < d)
    (hP : ∀ i j, (P i j : ℚ) = (d : ℚ) * R i j)
    (hcore : NonintegralColumns R) : ∀ j, columnLabel P d j ≠ 0 := by
  intro j hz
  have hres : columnResidue P d j = 0 := by
    simpa only [columnLabel_val_eq_columnResidue, AddSubgroup.coe_zero] using
      congrArg Subtype.val hz
  have hdiv : ∀ i, (d : ℤ) ∣ P i j := by
    intro i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hres i)
  choose z hz using hdiv
  apply hcore j
  refine ⟨z, ?_⟩
  intro i
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  apply mul_left_cancel₀ hd'
  rw [← hP i j, hz i]
  push_cast
  rfl

/-- Actual rational orthogonal nonintegral core: its dimension is at most twice
its actual coincidence-subgroup index. The denominator is constructed, not assumed. -/
theorem rational_core_bound (R : Matrix (Fin n) (Fin n) ℚ)
    (horth : R ∈ Matrix.orthogonalGroup (Fin n) ℚ)
    (hcore : NonintegralColumns R) :
    n ≤ 2 * (RationalResidueConnection.coincidenceSubgroup R).index := by
  obtain ⟨d, hd, P, hP, _, hcols, hrows, hkernel⟩ :=
    RationalResidueConnection.exists_orthogonal_integer_presentation R horth
  rw [hkernel]
  exact integer_core_index_bound P d hd hrows hcols
    (nonzero_columns_of_nonintegral R P d hd hP hcore)

end GeneralCoreBound
