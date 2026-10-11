import MathlibBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
The norm-divisible lift in the prime-neighbor construction. All primes and
all positive dimensions are allowed; no low-rank lattice theorem is assumed.
-/
open scoped BigOperators
namespace Wang38I
open Wang38

lemma dotI_single {n : ℕ} (v : IVector n) (j : Fin n) (c : ℤ) :
    dotI v (fun i => if i = j then c else 0) = v j * c := by
  simp [dotI, sumI, List.sum_ofFn, mul_ite]

/-- Every nonzero isotropic residue vector lifts to a vector whose norm is
zero modulo `p²`, without changing its residue class. -/
theorem exists_norm_divisible_lift {p n : ℕ} (hp : OddPrime p)
    (v : IVector n) (hvn : ∃ j, v j % (p : ℤ) ≠ 0)
    (hvnorm : dotI v v % (p : ℤ) = 0) :
    ∃ u : IVector n,
      (∀ i, u i % (p : ℤ) = v i % (p : ℤ)) ∧
      (p : ℤ) * p ∣ dotI u u := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  obtain ⟨j, hj⟩ := hvn
  obtain ⟨h, hh⟩ := Int.dvd_of_emod_eq_zero hvnorm
  have hp3 := oddPrime_ge_three hp
  have hvj : (v j : ZMod p) ≠ 0 := by
    exact fun hz => hj ((intCast_mod_zero_iff p (v j)).mp hz)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hz' : (2 : ℤ) % (p : ℤ) = 0 :=
      (intCast_mod_zero_iff p 2).mp (by simpa using hz)
    have hm : (2 : ℤ) % (p : ℤ) = 2 := Int.emod_eq_of_lt (by omega) (by omega)
    omega
  let c : ℤ := ((-(h : ZMod p)) / (2 * (v j : ZMod p))).val
  have hc : (c : ZMod p) = -(h : ZMod p) / (2 * (v j : ZMod p)) := by
    simp [c]
  have hc0 : (h + 2 * v j * c : ℤ) % (p : ℤ) = 0 := by
    apply (intCast_mod_zero_iff p _).mp
    push_cast
    rw [hc, mul_div_cancel₀ _ (mul_ne_zero htwo hvj)]
    ring
  obtain ⟨r, hr⟩ := Int.dvd_of_emod_eq_zero hc0
  let t : IVector n := fun i => if i = j then c else 0
  let u : IVector n := fun i => v i + (p : ℤ) * t i
  refine ⟨u, ?_, ?_⟩
  · intro i
    simp [u, Int.add_emod]
  · refine ⟨r + dotI t t, ?_⟩
    have ht : dotI v t = v j * c := dotI_single v j c
    have he := dotI_linear_combination 1 (p : ℤ) v t
    simp only [one_mul] at he
    change dotI u u = (p : ℤ) * p * (r + dotI t t)
    dsimp [u]
    rw [he, hh, ht]
    nlinarith [hr]

/-- The lift preserves all source congruences, including full support and
orthogonality to the all-ones vector. -/
theorem exists_admissible_norm_divisible_lift {p n : ℕ} (hp : OddPrime p)
    (hn : 0 < n) (v : IVector n) (hv : Admissible p v) :
    ∃ u : IVector n, Admissible p u ∧
      (∀ i, u i % (p : ℤ) = v i % (p : ℤ)) ∧
      (p : ℤ) * p ∣ dotI u u := by
  obtain ⟨u, hu, hu2⟩ := exists_norm_divisible_lift hp v
    ⟨⟨0, hn⟩, hv.1 ⟨0, hn⟩⟩ hv.2.2
  have hs : sumI u % (p : ℤ) = sumI v % (p : ℤ) := by
    simp only [sumI, List.sum_ofFn]
    calc
      _ = (∑ i, u i % (p : ℤ)) % (p : ℤ) := Finset.sum_int_mod _ _ _
      _ = (∑ i, v i % (p : ℤ)) % (p : ℤ) := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hu i)
      _ = _ := (Finset.sum_int_mod _ _ _).symm
  refine ⟨u, ⟨?_, ?_, ?_⟩, hu, hu2⟩
  · intro i
    rw [hu]
    exact hv.1 i
  · exact hs.trans hv.2.1
  · exact Int.emod_eq_zero_of_dvd (dvd_trans (dvd_mul_right (p : ℤ) (p : ℤ)) hu2)

#print axioms exists_norm_divisible_lift
#print axioms exists_admissible_norm_divisible_lift
end Wang38I
