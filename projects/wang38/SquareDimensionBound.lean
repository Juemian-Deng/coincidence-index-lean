import InnerProduct

/-!
A source-level, unconditional but weaker dimension obstruction: a vector with
full residue support cannot generate a primitive matrix when n > p^2.
This is NOT the desired n > 2p obstruction of Conjecture 38(ii).
-/
namespace Wang38

theorem sumQ_smul {n : Nat} (c : Rat) (v : Fin n → Rat) :
    sumQ (fun i => c * v i) = c * sumQ v := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih =>
    simp only [sumQ, List.ofFn_succ, List.sum_cons] at ih ⊢
    rw [ih]
    grind

theorem sumQ_intCast {n : Nat} (v : IVector n) :
    sumQ (fun i => (v i : Rat)) = (sumI v : Rat) := by
  induction n with
  | zero => simp [sumQ, sumI]
  | succ n ih =>
    simp only [sumQ, sumI, List.ofFn_succ, List.sum_cons] at ih ⊢
    rw [ih]
    exact (Rat.intCast_add _ _).symm

theorem numerator_column_norm {p n : Nat} {Q : QMatrix n} {A : IMatrix n}
    (ho : Orthogonal Q) (hn : Numerator p Q A) (j : Fin n) :
    dotI (fun i => A i j) (fun i => A i j) = (p : Int)*(p : Int) := by
  have h : ((dotI (fun i => A i j) (fun i => A i j)) : Rat) =
      (p : Rat)*(p : Rat) := by
    unfold dotI
    rw [← sumQ_intCast]
    have hf : (fun i => ((A i j * A i j : Int) : Rat)) =
        (fun i => (p : Rat)*(p : Rat)*(Q i j * Q i j)) := by
      funext i
      rw [Rat.intCast_mul, hn]
      grind
    rw [hf, sumQ_smul, ho]
    simp
  apply Rat.intCast_inj.mp
  simpa only [Rat.intCast_mul, Rat.intCast_natCast] using h

theorem nonzero_norm_bound {n : Nat} (a : IVector n) (ha : ∀ i, a i ≠ 0) :
    (n : Int) ≤ dotI a a := by
  induction n with
  | zero => simp [dotI, sumI]
  | succ n ih =>
    have h0 := int_square_positive (ha 0)
    have ht := ih (fun i => a i.succ) (fun i => ha i.succ)
    simp only [dotI, sumI, List.ofFn_succ, List.sum_cons] at ht ⊢
    omega

theorem nonzero_product_mod {p : Nat} (hp : OddPrime p) (a b : Int)
    (ha : a % (p : Int) ≠ 0) (hb : b % (p : Int) ≠ 0) :
    (a*b) % (p : Int) ≠ 0 := by
  intro hz
  have hd := Int.dvd_of_emod_eq_zero hz
  have hd' := prime_cancel_nonzero_residue hp a b ha hd
  exact hb (Int.emod_eq_zero_of_dvd hd')

/-- This theorem applies to the actual Definitions 13/16 predicate, without
assuming a histogram, an exchange family, or a matrix support bound. Its weaker
p^2 cutoff is explicitly retained in its name and statement. -/
theorem generated_dimension_le_prime_square {p n : Nat} (hp : OddPrime p)
    (v : IVector n) (hv : FullSupport p v) (Q : QMatrix n)
    (hQ : GeneratedPrimitive p v Q) : n ≤ p*p := by
  rcases hQ with ⟨ho, _, _, A, hn, hk, hl⟩
  rcases hk.1 with ⟨i, j, haij⟩
  rcases hl j with ⟨c, hc⟩
  have hc0 : c % (p : Int) ≠ 0 := by
    intro hz
    have he := hc i
    rw [Int.mul_emod, hz] at he
    simp at he
    exact haij he
  have hcol : ∀ k, A k j ≠ 0 := by
    intro k hz
    have he := hc k
    rw [hz] at he
    have hpmod := nonzero_product_mod hp c (v k) hc0 (hv k)
    simp at he
    exact hpmod he.symm
  have hnorm := numerator_column_norm ho hn j
  have hbound := nonzero_norm_bound (fun i => A i j) hcol
  rw [hnorm] at hbound
  have hcast : ((p*p : Nat) : Int) = (p : Int)*(p : Int) := by simp
  omega

theorem no_generated_above_prime_square {p n : Nat} (hp : OddPrime p)
    (v : IVector n) (hv : FullSupport p v) (hn : p*p < n) :
    ¬ ∃ Q : QMatrix n, GeneratedPrimitive p v Q := by
  rintro ⟨Q, hQ⟩
  have := generated_dimension_le_prime_square hp v hv Q hQ
  omega

#print axioms numerator_column_norm
#print axioms generated_dimension_le_prime_square
#print axioms no_generated_above_prime_square

end Wang38
