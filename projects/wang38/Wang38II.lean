import ExchangeLemma
import ResidueBlocks

/-! Full all-prime nonexistence half, Conjecture 38(ii), using the actual
primitive-matrix definitions from Wang38Targets. No rank-one support bound,
exchange classification, or lattice theorem is supplied as an assumption. -/
open scoped BigOperators
namespace Wang38

 theorem signed_vector_norm {n : Nat} (e a : IVector n) (he : ∀ i, e i*e i = 1) :
    dotI (fun i => e i*a i) (fun i => e i*a i) = dotI a a := by
  simp only [dotI, sumI, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  calc
    e i*a i*(e i*a i) = (e i*e i)*(a i*a i) := by ring
    _ = _ := by rw [he]; simp

 theorem signed_rows_differ {p n : Nat} (hp : OddPrime p)
    {Q : QMatrix n} {A : IMatrix n} (ho : Orthogonal Q) (hn : Numerator p Q A)
    (e : IVector n) (he : ∀ i, e i*e i = 1) (i k : Fin n) (hik : i ≠ k) :
    ∃ j, e i*A i j ≠ e k*A k j := by
  classical
  by_contra h
  push Not at h
  have hnT : Numerator p (fun i j => Q j i) (fun i j => A j i) := by
    intro i j; exact hn j i
  have hoT : Orthogonal (fun i j => Q j i) := orthogonal_transpose ho
  have hrow := numerator_column_gram hoT hnT i k
  rw [ite_eq_right hik] at hrow
  have hnorm := numerator_column_norm hoT hnT i
  let u : IVector n := fun j => e i*A i j
  let w : IVector n := fun j => e k*A k j
  have huw : u = w := funext h
  have hu : dotI u u = (p : Int)*(p : Int) := by
    rw [signed_vector_norm (fun _ => e i) (fun j => A i j) (fun _ => he i)]
    exact hnorm
  have hd : dotI u w = 0 := by
    dsimp [u, w]
    rw [dotI_smul_right, dotI_comm (fun j => e i*A i j) (fun j => A k j),
      dotI_smul_right, dotI_comm (fun j => A k j) (fun j => A i j)]
    rw [hrow]
    simp
  rw [← huw, hu] at hd
  have hp0 : 0 < (p : Int) := by have := hp.1; omega
  have := Int.mul_pos hp0 hp0
  omega

/-- The strong matrix theorem: no regularity or zero coordinate-sum
hypothesis is needed for this support bound. Those source conditions remain
present in GeneratedPrimitive and the final Conjecture38II theorem. -/
theorem generated_dimension_le_twice_prime {p n : Nat} (hp : OddPrime p)
    (v : IVector n) (hv : FullSupport p v) (Q : QMatrix n)
    (hQ : GeneratedPrimitive p v Q) : n ≤ 2*p := by
  classical
  by_contra hdim
  have hnp : p < n := by omega
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  rcases hQ with ⟨ho, _, _, A, hn, hk, hl⟩
  have hfull := numerator_full_support hp hv ho hn hk hl
  rcases exists_maximal_absResidueBlock hp v hnp with ⟨b, hcard, hmax⟩
  let I := absResidueBlock (p := p) v b
  let e : IVector n := orientSign (p := p) v b
  have he : ∀ i, e i*e i = 1 := orientSign_square v b
  have hecases : ∀ i, e i = 1 ∨ e i = -1 := orientSign_cases v b
  have hIcard : 2 ≤ I.card := hcard
  rcases Finset.one_lt_card.mp (by omega : 1 < I.card) with ⟨i, hi, k, hkI, hik⟩
  rcases signed_rows_differ hp ho hn e he i k hik with ⟨j, hvary⟩
  let a : IVector n := fun t => e t*A t j
  have ha : dotI a a = (p : Int)*(p : Int) := by
    rw [signed_vector_norm e (fun t => A t j) he]
    exact numerator_column_norm ho hn j
  have hafull : FullSupport p a := by
    intro t hz
    have hzZ := (intCast_mod_zero_iff p (a t)).mpr hz
    have hAZ : (A t j : ZMod p) ≠ 0 := by
      intro hzero
      exact hfull t j ((intCast_mod_zero_iff p _).mp hzero)
    have heZ : (e t : ZMod p) ≠ 0 := by
      rcases hecases t with h | h <;> rw [h] <;> simp
    have habs : (a t : ZMod p) = (e t : ZMod p)*(A t j : ZMod p) := by simp [a]
    rw [habs] at hzZ
    exact mul_ne_zero heZ hAZ hzZ
  rcases hl j with ⟨c, hc⟩
  have hcZ : (c : ZMod p) ≠ 0 := by
    intro hz
    have hcB : (A b j : ZMod p) = (c : ZMod p)*(v b : ZMod p) := by
      rw [← Int.cast_mul]
      exact (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hc b)
    rw [hz, zero_mul] at hcB
    exact hfull b j ((intCast_mod_zero_iff p _).mp hcB)
  have haZ : ∀ t, (a t : ZMod p) = (e t : ZMod p)*((c : ZMod p)*(v t : ZMod p)) := by
    intro t
    have hA : (A t j : ZMod p) = (c : ZMod p)*(v t : ZMod p) := by
      rw [← Int.cast_mul]
      exact (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hc t)
    simp only [a, Int.cast_mul]
    rw [hA]
  have haI : ∀ t ∈ I, (a t : ZMod p) = (c : ZMod p)*(v b : ZMod p) := by
    intro t ht
    rw [haZ]
    have heB := orientSign_on_block v b t ht
    change (e t : ZMod p)*(v t : ZMod p) = (v b : ZMod p) at heB
    calc
      (e t : ZMod p)*((c : ZMod p)*(v t : ZMod p)) =
        (c : ZMod p)*((e t : ZMod p)*(v t : ZMod p)) := by ring
      _ = _ := by rw [heB]
  have hres : ∀ t ∈ I, ∀ r ∈ I, a t % (p : Int) = a r % (p : Int) := by
    intro t ht r hr
    exact (ZMod.intCast_eq_intCast_iff' _ _ p).mp ((haI t ht).trans (haI r hr).symm)
  rcases residue_block_exchange_vector hp a ha hafull I hres i k hi hkI hvary with
    ⟨u, s, ε, hspos, hslt, hε, hunorm, huI, hures⟩
  have huAbs : ∀ t, SameAbs (u t : ZMod p) ((c : ZMod p)*(v t : ZMod p)) := by
    intro t
    have hucast : (u t : ZMod p) = (ε : ZMod p)*(a t : ZMod p) := by
      rw [← Int.cast_mul]
      exact (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hures t)
    have hua : SameAbs (u t : ZMod p) (a t : ZMod p) := by
      rw [hucast]
      exact sameAbs_sign_mul ε hε _
    have hac : SameAbs (a t : ZMod p) ((c : ZMod p)*(v t : ZMod p)) := by
      rw [haZ]
      exact sameAbs_sign_mul (e t) (hecases t) _
    exact sameAbs_trans hua hac
  have hu0 : ∀ t, u t ≠ 0 := by
    intro t ht
    have hvZ : (v t : ZMod p) ≠ 0 := by
      intro hz
      exact hv t ((intCast_mod_zero_iff p _).mp hz)
    have hcv := mul_ne_zero hcZ hvZ
    have habs := huAbs t
    rw [ht] at habs
    rcases habs with h | h
    · exact hcv (by simpa using h.symm)
    · exact hcv (by simpa using h.symm)
  let S := s.toNat
  have hS : (S : Int) = s := by dsimp [S]; omega
  have hSpos : 1 ≤ S := by omega
  have humax : ∀ t, magnitudeCount u t ≤ I.card := by
    intro t
    exact magnitudeCount_le_maximal_block hp u v (c : ZMod p) hcZ b hmax huAbs t
  have huattain : magnitudeCount u S = I.card := by
    apply Nat.le_antisymm (humax S)
    apply Finset.card_le_card
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [huI t ht]
    dsimp [S]
    have hs0 : 0 ≤ s := by omega
    have he := Int.natAbs_of_nonneg hs0
    omega
  have hbound := vector_frequency_dimension_bound u hu0 hSpos (by omega : 0 < I.card)
    huattain (fun t _ => humax t) (by simpa only [hS] using hunorm)
  exact hdim hbound

/-- Full Wang--Wang--Yu Conjecture 38(ii), for EVERY odd prime and all dimensions. -/
theorem conjecture38II : Conjecture38II := by
  intro p n hp hdim v hv hQ
  rcases hQ with ⟨Q, hQ⟩
  have hbound := generated_dimension_le_twice_prime hp v hv.1 Q hQ
  omega

#print axioms generated_dimension_le_twice_prime
#print axioms conjecture38II

end Wang38
