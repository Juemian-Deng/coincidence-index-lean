import FrameOrientation
import RankBridge

/-!
All source-level matrix conditions follow from an orthonormal frame in the
concrete neighbor. This is an intermediate extraction theorem, not a proof
that such a frame exists in ranks ≤ 8.
-/
open scoped BigOperators
namespace Wang38I
open Wang38

lemma frame_reconstruction {n : ℕ} (Q : QMatrix n) (ho : Orthogonal Q)
    (x : QVector n) (i : Fin n) :
    x i = ∑ j, Q i j * dotQ x (fun k => Q k j) := by
  have he : (Matrix.of Q).mulVec ((Matrix.transpose (Matrix.of Q)).mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, orthogonal_transpose_identity ho, Matrix.one_mulVec]
  have hi := congrFun he i
  simpa [Matrix.mulVec, dotProduct, dotQ, mul_comm] using hi.symm

/-- An orthonormal frame inside an integral full lattice is automatically
an integral spanning family. -/
theorem neighbor_frame_integral_span {p n : ℕ} (hp : p ≠ 0)
    (u : IVector n) (hu : (p : ℤ) * p ∣ dotI u u)
    (Q : QMatrix n) (ho : Orthogonal Q)
    (hcol : ∀ j, (fun i => Q i j) ∈ neighbor p u)
    (x : QVector n) (hx : x ∈ neighbor p u) :
    ∃ c : Fin n → ℤ, ∀ i, x i = ∑ j, (c j : ℚ) * Q i j := by
  have hi : ∀ j, ∃ c : ℤ, dotQ x (fun i => Q i j) = (c : ℚ) := by
    intro j
    exact neighbor_integral hp u hu hx (hcol j)
  choose c hc using hi
  refine ⟨c, ?_⟩
  intro i
  simpa [hc, mul_comm] using frame_reconstruction Q ho x i

/-- An orthonormal neighbor frame cannot be an integer matrix. The proof
uses the nonintegral vector u/p and the proved integral spanning identity. -/
theorem neighbor_frame_nonintegral {p n : ℕ} (hp : p ≠ 0)
    (u : IVector n) (huj : ∃ j, u j % (p : ℤ) ≠ 0)
    (hu : (p : ℤ) * p ∣ dotI u u)
    (Q : QMatrix n) (ho : Orthogonal Q)
    (hcol : ∀ j, (fun i => Q i j) ∈ neighbor p u) :
    ¬ (∀ i j, Integral (Q i j)) := by
  intro h
  choose B hB using h
  obtain ⟨j, hj⟩ := huj
  obtain ⟨c, hc⟩ := neighbor_frame_integral_span hp u hu Q ho hcol
    (fun i => (u i : ℚ) / p) (lift_mem_neighbor hp u)
  have he : (u j : ℚ) / p = ((∑ k, c k * B j k : ℤ) : ℚ) := by
    rw [hc]
    simp [hB]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hz : u j = (p : ℤ) * ∑ k, c k * B j k := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    simpa [mul_comm] using (div_eq_iff hpQ).mp he
  exact hj (Int.emod_eq_zero_of_dvd ⟨_, hz⟩)

/-- A prime-cleared matrix with one nonzero numerator residue has exact
least positive denominator p, not merely a denominator dividing p. -/
theorem exactLevel_of_numerator_nonzero {p n : ℕ} (hp : OddPrime p)
    (Q : QMatrix n) (A : IMatrix n) (hn : Numerator p Q A)
    (hnz : ∃ i j, A i j % (p : ℤ) ≠ 0) : ExactLevel p Q := by
  refine ⟨by have := hp.1; omega, ?_, ?_⟩
  · intro i j
    exact ⟨A i j, (hn i j).symm⟩
  · intro d hd hclear
    obtain ⟨i, j, hij⟩ := hnz
    obtain ⟨z, hz⟩ := hclear i j
    have he : (d : ℤ) * A i j = (p : ℤ) * z := by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hn]
      calc
        _ = (p : ℚ) * ((d : ℚ) * Q i j) := by ring
        _ = _ := by rw [hz]
    have hpdiv : (p : ℤ) ∣ (d : ℤ) := by
      apply prime_cancel_nonzero_residue hp (A i j) (d : ℤ) hij
      exact ⟨z, by nlinarith [he]⟩
    have hpn : p ∣ d := by exact_mod_cast hpdiv
    exact Nat.le_of_dvd hd hpn

/-- The concrete neighbor frame supplies every original matrix condition,
including exact denominator and actual finite-field rank. Existence of the
frame remains a separate mathematical step. -/
theorem published_matrix_of_neighbor_frame {p n : ℕ} (hp : OddPrime p)
    (v u : IVector n) (huj : ∃ j, u j % (p : ℤ) ≠ 0)
    (hu : (p : ℤ) * p ∣ dotI u u) (husum : sumI u % (p : ℤ) = 0)
    (hres : ∀ i, u i % (p : ℤ) = v i % (p : ℤ))
    (Q : QMatrix n) (ho : Orthogonal Q)
    (hcol : ∀ j, (fun i => Q i j) ∈ neighbor p u) :
    ∃ R : QMatrix n, PublishedGeneratedPrimitive p v R := by
  classical
  have hp0 : p ≠ 0 := by have := hp.1; omega
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  obtain ⟨R, hRo, hRr, hRc⟩ := orient_neighbor_frame hp u hu husum Q ho hcol
  have ha : ∀ j, ∃ a : IVector n, (∀ i, (a i : ℚ) = (p : ℚ) * R i j) ∧
      ∃ k : ℤ, ∀ i, a i % (p : ℤ) = (k * u i) % (p : ℤ) := by
    intro j
    exact neighbor_numerator (hRc j)
  choose a ha hc using ha
  let A : IMatrix n := fun i j => a j i
  have hAn : Numerator p R A := by intro i j; exact ha j i
  have hAz : ∃ i j, A i j % (p : ℤ) ≠ 0 := by
    by_contra h
    push Not at h
    apply neighbor_frame_nonintegral hp0 u huj hu R hRo hRc
    intro i j
    obtain ⟨z, hz⟩ := Int.dvd_of_emod_eq_zero (h i j)
    refine ⟨z, ?_⟩
    have he := hAn i j
    rw [hz] at he
    push_cast at he
    exact (mul_left_cancel₀ hpQ he).symm
  have hAc : ColumnsInLine p v A := by
    intro j
    obtain ⟨k, hk⟩ := hc j
    refine ⟨k, ?_⟩
    intro i
    change a j i % (p : ℤ) = _
    rw [hk, Int.mul_emod, hres]
    exact (Int.mul_emod k (v i) (p : ℤ)).symm
  have hvn : ∃ i, v i % (p : ℤ) ≠ 0 := by
    obtain ⟨i, hi⟩ := huj
    exact ⟨i, by rwa [← hres]⟩
  refine ⟨R, generated_implies_published hp v R ?_⟩
  exact ⟨hRo, hRr, exactLevel_of_numerator_nonzero hp R A hAn hAz,
    A, hAn, ⟨hAz, v, hvn, hAc⟩, hAc⟩

#print axioms neighbor_frame_integral_span
#print axioms neighbor_frame_nonintegral
#print axioms exactLevel_of_numerator_nonzero
#print axioms published_matrix_of_neighbor_frame
end Wang38I
