import RankBridge
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-! Exact complete (vacuous) cases n = 1 and n = 2 of the published target. -/
namespace Wang38I
open Wang38

 theorem no_admissible_dimension_two {p : ℕ} (hp : OddPrime p) (v : IVector 2) :
    ¬ Admissible p v := by
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  intro hv
  have hsI : (v 0 + v 1) % (p : ℤ) = 0 := by
    simpa [sumI, List.ofFn_succ] using hv.2.1
  have hnI : (v 0 * v 0 + v 1 * v 1) % (p : ℤ) = 0 := by
    simpa [dotI, sumI, List.ofFn_succ] using hv.2.2
  have hs : (v 0 : ZMod p) + (v 1 : ZMod p) = 0 := by
    exact_mod_cast (intCast_mod_zero_iff p _).mpr hsI
  have hn : (v 0 : ZMod p) * (v 0 : ZMod p) + (v 1 : ZMod p) * (v 1 : ZMod p) = 0 := by
    exact_mod_cast (intCast_mod_zero_iff p _).mpr hnI
  have he : (2 : ZMod p) * (v 0 : ZMod p) * (v 0 : ZMod p) = 0 := by
    linear_combination hn + ((v 0 : ZMod p) - (v 1 : ZMod p)) * hs
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hz' : (2 : ℤ) % (p : ℤ) = 0 :=
      (intCast_mod_zero_iff p 2).mp (by simpa using hz)
    have hp3 := oddPrime_ge_three hp
    have hm : (2 : ℤ) % (p : ℤ) = 2 := Int.emod_eq_of_lt (by omega) (by omega)
    omega
  have hz : (v 0 : ZMod p) = 0 := by
    rcases mul_eq_zero.mp he with h | h
    · exact (mul_eq_zero.mp h).resolve_left htwo
    · exact h
  exact hv.1 0 ((intCast_mod_zero_iff p _).mp hz)

/-- Full source-level conclusion for dimensions one and two, with literal
finite-field rank. Both cases have contradictory source hypotheses. -/
theorem published_conjecture38I_dimension_le_two {p n : ℕ}
    (hp : Nat.Prime p) (ho : p % 2 = 1) (hn : 0 < n) (hn2 : n ≤ 2)
    (v : IVector n) (hv : Admissible p v) :
    ∃ Q : QMatrix n, PublishedGeneratedPrimitive p v Q := by
  have hp' : OddPrime p := ⟨hp.two_le, ho, (Nat.prime_def.mp hp).2⟩
  have hn' : n = 1 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl
  · exact (no_admissible_dimension_one p v hv).elim
  · exact (no_admissible_dimension_two hp' v hv).elim

#print axioms published_conjecture38I_dimension_le_two
end Wang38I
