import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-! Dimension-specific Minkowski volume estimates for the low-rank lattice
classification. Bounds are proved inside Lean, not imported decimal tables. -/
open MeasureTheory MeasureTheory.Measure Module Metric
open scoped Nat
namespace Wang38I.Classification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A rational covolume cap: 10/7 exceeds √2, and suffices in dimensions ≤7.
Dimension 8 only needs the unimodular cap 1. -/
noncomputable def shortVectorCovolumeCap (n : ℕ) : ℝ := if n = 8 then 1 else 10/7

lemma sqrt_two_lt_cap : Real.sqrt 2 < (10 : ℝ)/7 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- The open ball of squared radius 3 beats Minkowski's volume threshold
at every required dimension, with an explicit rational bound on covolume. -/
theorem ball_sqrt_three_volume (n : ℕ) (hn : Module.finrank ℝ E = n)
    (hnpos : 0 < n) (hn8 : n ≤ 8) :
    ENNReal.ofReal (shortVectorCovolumeCap n * 2^n) <
      volume (Metric.ball (0 : E) (Real.sqrt 3)) := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hr : (5 : ℝ)/3 ≤ Real.sqrt 3 := by
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hp := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have heven (k : ℕ) : (Real.sqrt 3) ^ (2*k) = (3 : ℝ)^k := by
    rw [pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hodd (k : ℕ) : (Real.sqrt 3) ^ (2*k+1) = (3 : ℝ)^k * Real.sqrt 3 := by
    rw [pow_succ, heven]
  interval_cases n
  · rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by omega), hn,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg 3) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [shortVectorCovolumeCap])).mpr
    rw [hodd 0]
    norm_num [shortVectorCovolumeCap, Nat.doubleFactorial] at *
    calc
      _ < ((3 : ℝ)^0 * (5/3)) * (3^0 * 2^1 / 1) := by norm_num
      _ ≤ _ := by gcongr <;> norm_num; assumption
  · rw [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by omega), hn,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg 3) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [shortVectorCovolumeCap])).mpr
    rw [heven 1]
    norm_num [shortVectorCovolumeCap, Nat.doubleFactorial] at *
    calc
      _ < (3 : ℝ)^1 * (3^1 / 1) := by norm_num
      _ ≤ _ := by gcongr <;> norm_num; assumption
  · rw [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by omega), hn,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg 3) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [shortVectorCovolumeCap])).mpr
    rw [hodd 1]
    norm_num [shortVectorCovolumeCap, Nat.doubleFactorial] at *
    calc
      _ < ((3 : ℝ)^1 * (5/3)) * (3^1 * 2^2 / 3) := by norm_num
      _ ≤ _ := by gcongr <;> norm_num; assumption
  · rw [InnerProductSpace.volume_ball_of_dim_even (k := 2) (by omega), hn,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg 3) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [shortVectorCovolumeCap])).mpr
    rw [heven 2]
    norm_num [shortVectorCovolumeCap, Nat.doubleFactorial] at *
    calc
      _ < (3 : ℝ)^2 * (3^2 / 2) := by norm_num
      _ ≤ _ := by gcongr; norm_num
  · rw [InnerProductSpace.volume_ball_of_dim_odd (k := 2) (by omega), hn,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg 3) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [shortVectorCovolumeCap])).mpr
    rw [hodd 2]
    norm_num [shortVectorCovolumeCap, Nat.doubleFactorial] at *
    calc
      _ < ((3 : ℝ)^2 * (5/3)) * (3^2 * 2^3 / 15) := by norm_num
      _ ≤ _ := by gcongr <;> norm_num
  · rw [InnerProductSpace.volume_ball_of_dim_even (k := 3) (by omega), hn,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg 3) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [shortVectorCovolumeCap])).mpr
    rw [heven 3]
    norm_num [shortVectorCovolumeCap, Nat.doubleFactorial] at *
    calc
      _ < (3 : ℝ)^3 * (3^3 / 6) := by norm_num
      _ ≤ _ := by gcongr; norm_num
  · rw [InnerProductSpace.volume_ball_of_dim_odd (k := 3) (by omega), hn,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg 3) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [shortVectorCovolumeCap])).mpr
    rw [hodd 3]
    norm_num [shortVectorCovolumeCap, Nat.doubleFactorial] at *
    calc
      _ < ((3 : ℝ)^3 * (5/3)) * (3^3 * 2^4 / 105) := by norm_num
      _ ≤ _ := by gcongr <;> norm_num
  · rw [InnerProductSpace.volume_ball_of_dim_even (k := 4) (by omega), hn,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg 3) _)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [shortVectorCovolumeCap])).mpr
    rw [heven 4]
    norm_num [shortVectorCovolumeCap, Nat.doubleFactorial] at *
    calc
      _ < (3 : ℝ)^4 * (3^4 / 24) := by norm_num
      _ ≤ _ := by gcongr; norm_num

lemma shortVectorCovolumeCap_nonneg (n : ℕ) : 0 ≤ shortVectorCovolumeCap n := by
  unfold shortVectorCovolumeCap
  split_ifs <;> norm_num

/-- The dimension-dependent bound is applied to an actual Mathlib lattice
and its actual covolume. No shortest-vector existence is assumed. -/
theorem exists_norm_sq_lt_three_of_covolume
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hnpos : 0 < Module.finrank ℝ E) (hn8 : Module.finrank ℝ E ≤ 8)
    (hc : ZLattice.covolume L ≤ shortVectorCovolumeCap (Module.finrank ℝ E)) :
    ∃ x : E, x ∈ L ∧ x ≠ 0 ∧ ‖x‖^2 < 3 := by
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hF : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
  have hFfinite : volume F ≠ ⊤ := by
    exact ne_of_lt (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).measure_lt_top
  have hcov : volume F = ENNReal.ofReal (ZLattice.covolume L) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
    exact (ENNReal.ofReal_toReal hFfinite).symm
  have hvol : volume F * 2 ^ Module.finrank ℝ E <
      volume (Metric.ball (0 : E) (Real.sqrt 3)) := by
    apply lt_of_le_of_lt _ (ball_sqrt_three_volume (Module.finrank ℝ E) rfl hnpos hn8)
    rw [hcov, ENNReal.ofReal_mul (shortVectorCovolumeCap_nonneg _),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    gcongr
  have hsym : ∀ x ∈ Metric.ball (0 : E) (Real.sqrt 3), -x ∈ Metric.ball (0 : E) (Real.sqrt 3) := by
    intro x hx
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hx
  let : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  obtain ⟨x, hx0, hxball⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L.toAddSubgroup) hF hsym (convex_ball (0 : E) (Real.sqrt 3)) hvol
  refine ⟨x.val, x.prop, ?_, ?_⟩
  · exact fun h => hx0 (Subtype.ext h)
  · have hxnorm : ‖x.val‖ < Real.sqrt 3 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxball
    calc
      ‖x.val‖^2 < (Real.sqrt 3)^2 := by gcongr
      _ = 3 := Real.sq_sqrt (by norm_num)

/-- Integrality converts the genuine Minkowski vector into a unit or root. -/
theorem exists_unit_or_root_of_covolume
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hnpos : 0 < Module.finrank ℝ E) (hn8 : Module.finrank ℝ E ≤ 8)
    (hc : ZLattice.covolume L ≤ shortVectorCovolumeCap (Module.finrank ℝ E))
    (hInt : ∀ x ∈ L, ∃ k : ℤ, ‖x‖^2 = (k : ℝ)) :
    ∃ x : E, x ∈ L ∧ (‖x‖^2 = 1 ∨ ‖x‖^2 = 2) := by
  obtain ⟨x, hxL, hx0, hxnorm⟩ := exists_norm_sq_lt_three_of_covolume L hnpos hn8 hc
  obtain ⟨k, hk⟩ := hInt x hxL
  have hkpos : 0 < (k : ℝ) := by
    rw [← hk]
    exact sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hklt : k < (3 : ℤ) := by
    rw [hk] at hxnorm
    exact_mod_cast hxnorm
  have hcases : k = 1 ∨ k = 2 := by omega
  refine ⟨x, hxL, ?_⟩
  rcases hcases with h | h <;> rw [hk, h] <;> simp

/-- The unimodular short-vector bound in ranks one through eight. The
remaining classification bridge must prove covolume one from self-duality. -/
theorem exists_unit_or_root_covolume_one
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hnpos : 0 < Module.finrank ℝ E) (hn8 : Module.finrank ℝ E ≤ 8)
    (hc : ZLattice.covolume L = 1)
    (hInt : ∀ x ∈ L, ∃ k : ℤ, ‖x‖^2 = (k : ℝ)) :
    ∃ x : E, x ∈ L ∧ (‖x‖^2 = 1 ∨ ‖x‖^2 = 2) := by
  apply exists_unit_or_root_of_covolume L hnpos hn8 _ hInt
  rw [hc]
  unfold shortVectorCovolumeCap
  split_ifs <;> norm_num

/-- The determinant-at-most-two short-vector bound in ranks one through
seven, stated using the actual geometric covolume. -/
theorem exists_unit_or_root_covolume_sq_le_two
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hnpos : 0 < Module.finrank ℝ E) (hn7 : Module.finrank ℝ E ≤ 7)
    (hc : (ZLattice.covolume L)^2 ≤ 2)
    (hInt : ∀ x ∈ L, ∃ k : ℤ, ‖x‖^2 = (k : ℝ)) :
    ∃ x : E, x ∈ L ∧ (‖x‖^2 = 1 ∨ ‖x‖^2 = 2) := by
  apply exists_unit_or_root_of_covolume L hnpos (by omega) _ hInt
  have hn8 : Module.finrank ℝ E ≠ 8 := by omega
  simp only [shortVectorCovolumeCap, ite_eq_right_iff.mpr (fun h => (hn8 h).elim)]
  have hcpos := ZLattice.covolume_pos L volume
  nlinarith

#print axioms ball_sqrt_three_volume
#print axioms exists_unit_or_root_covolume_one
#print axioms exists_unit_or_root_covolume_sq_le_two
end Wang38I.Classification
