import Wang38Targets

/-! The arithmetic and orthogonality lemma in Section 2 of the matrix proof.
No matrix-completeness or exchange-family theorem is assumed here. -/
namespace Wang38

theorem sumI_add {n : Nat} (v w : IVector n) :
    sumI (fun i => v i + w i) = sumI v + sumI w := by
  induction n with
  | zero => simp [sumI]
  | succ n ih =>
    simp only [sumI, List.ofFn_succ, List.sum_cons] at ih ⊢
    rw [ih]
    grind

theorem sumI_smul {n : Nat} (c : Int) (v : IVector n) :
    sumI (fun i => c * v i) = c * sumI v := by
  induction n with
  | zero => simp [sumI]
  | succ n ih =>
    simp only [sumI, List.ofFn_succ, List.sum_cons] at ih ⊢
    rw [ih]
    grind

theorem dotI_comm {n : Nat} (v w : IVector n) : dotI v w = dotI w v := by
  unfold dotI
  congr 1
  funext i
  exact Int.mul_comm _ _

theorem dotI_add_right {n : Nat} (u v w : IVector n) :
    dotI u (fun i => v i + w i) = dotI u v + dotI u w := by
  unfold dotI
  simp only [Int.mul_add]
  exact sumI_add _ _

theorem dotI_smul_right {n : Nat} (c : Int) (u v : IVector n) :
    dotI u (fun i => c * v i) = c * dotI u v := by
  unfold dotI
  have h : (fun i => u i * (c * v i)) = (fun i => c * (u i * v i)) := by
    funext i
    grind
  rw [h, sumI_smul]

theorem dotI_linear_combination {n : Nat} (a b : Int) (u v : IVector n) :
    dotI (fun i => a*u i+b*v i) (fun i => a*u i+b*v i) =
      a*a*dotI u u + 2*a*b*dotI u v + b*b*dotI v v := by
  rw [dotI_add_right, dotI_smul_right, dotI_smul_right]
  rw [dotI_comm (fun i => a*u i+b*v i) u,
    dotI_comm (fun i => a*u i+b*v i) v]
  rw [dotI_add_right, dotI_add_right]
  simp only [dotI_smul_right]
  rw [dotI_comm v u]
  grind

theorem int_square_nonnegative (z : Int) : 0 ≤ z*z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem int_square_positive {z : Int} (h : z ≠ 0) : 0 < z*z := by
  by_cases hp : 0 < z
  · exact Int.mul_pos hp hp
  · exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)

theorem dotI_self_nonnegative {n : Nat} (v : IVector n) : 0 ≤ dotI v v := by
  induction n with
  | zero => simp [dotI, sumI]
  | succ n ih =>
    have h := int_square_nonnegative (v 0)
    have ht := ih (fun i => v i.succ)
    simp only [dotI, sumI, List.ofFn_succ, List.sum_cons] at ht ⊢
    omega

theorem dotI_self_eq_zero {n : Nat} (v : IVector n) (h : dotI v v = 0) :
    ∀ i, v i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    have h0 := int_square_nonnegative (v 0)
    have ht := dotI_self_nonnegative (fun i : Fin n => v i.succ)
    have he : v 0 * v 0 + dotI (fun i : Fin n => v i.succ) (fun i => v i.succ) = 0 := by
      simpa only [dotI, sumI, List.ofFn_succ, List.sum_cons] using h
    have hz : v 0 = 0 := by
      by_cases hh : v 0 = 0
      · exact hh
      · have hp := int_square_positive hh
        omega
    have htz : dotI (fun i : Fin n => v i.succ) (fun i => v i.succ) = 0 := by omega
    intro i
    exact Fin.cases hz (ih (fun i => v i.succ) htz) i

theorem oddPrime_ge_three {p : Nat} (hp : OddPrime p) : 3 ≤ p := by
  rcases hp with ⟨hp, ho, _⟩
  omega

theorem gcd_prime_nonzero_residue {p : Nat} (hp : OddPrime p) (k : Int)
    (hk : k % (p : Int) ≠ 0) : Int.gcd (p : Int) k = 1 := by
  have hd : Int.gcd (p : Int) k ∣ p := by
    simpa using Int.gcd_dvd_natAbs_left (p : Int) k
  rcases hp.2.2 _ hd with h | h
  · exact h
  · have hkdiv := Int.gcd_dvd_right (p : Int) k
    rw [h] at hkdiv
    exact False.elim (hk (Int.emod_eq_zero_of_dvd hkdiv))

theorem prime_cancel_nonzero_residue {p : Nat} (hp : OddPrime p) (k x : Int)
    (hk : k % (p : Int) ≠ 0) (h : (p : Int) ∣ k*x) : (p : Int) ∣ x := by
  have he := (Int.dvd_gcd_mul_iff_dvd_mul (k := (p : Int)) (n := k) (m := x)).mpr h
  rw [gcd_prime_nonzero_residue hp k hk] at he
  simpa using he

/-- Norm-`p²` integer vectors in the same nonzero residue line have inner
product divisible by `p²`. This is an unbounded theorem for all odd primes. -/
theorem inner_product_divisible {p n : Nat} (hp : OddPrime p)
    (a b : IVector n) (ha : dotI a a = (p : Int)*(p : Int))
    (hb : dotI b b = (p : Int)*(p : Int)) (k : Int)
    (hk : k % (p : Int) ≠ 0)
    (hres : ∀ i, (b i-k*a i) % (p : Int) = 0) :
    (p : Int)*(p : Int) ∣ dotI a b := by
  let t : IVector n := fun i => (b i-k*a i)/(p : Int)
  have ht : b = fun i => k*a i+(p : Int)*t i := by
    funext i
    have he := Int.emod_add_mul_ediv (b i-k*a i) (p : Int)
    rw [hres i] at he
    dsimp [t]
    omega
  have hn := dotI_linear_combination k (p : Int) a t
  rw [← ht, ha, hb] at hn
  have hp0 : (p : Int) ≠ 0 := by have := hp.1; omega
  have he : 2*k*dotI a t = (p : Int)*(1-k*k-dotI t t) := by
    apply Int.eq_of_mul_eq_mul_left hp0
    grind
  have hd : (p : Int) ∣ 2*(k*dotI a t) := by
    refine ⟨1-k*k-dotI t t, ?_⟩
    grind
  have htwo : (2 : Int) % (p : Int) ≠ 0 := by
    have hge := oddPrime_ge_three hp
    rw [Int.emod_eq_of_lt (by decide : (0 : Int) ≤ 2) (by omega : (2 : Int) < (p : Int))]
    decide
  have hd' := prime_cancel_nonzero_residue hp 2 (k*dotI a t) htwo hd
  have hd'' := prime_cancel_nonzero_residue hp k (dotI a t) hk hd'
  rcases hd'' with ⟨r, hr⟩
  refine ⟨k+r, ?_⟩
  rw [ht, dotI_add_right, dotI_smul_right, dotI_smul_right, ha, hr]
  grind

/-- Source Lemma 20, in a slightly stronger form: only the nonzero scalar
relation is needed, rather than full support of both integer vectors. -/
theorem orthogonal_or_equal_up_to_sign {p n : Nat} (hp : OddPrime p)
    (a b : IVector n) (ha : dotI a a = (p : Int)*(p : Int))
    (hb : dotI b b = (p : Int)*(p : Int)) (k : Int)
    (hk : k % (p : Int) ≠ 0)
    (hres : ∀ i, (b i-k*a i) % (p : Int) = 0) :
    dotI a b = 0 ∨ b = a ∨ b = fun i => -a i := by
  rcases inner_product_divisible hp a b ha hb k hk hres with ⟨r, hr⟩
  have hp0 : 0 < (p : Int) := by have := hp.1; omega
  have hp2 := Int.mul_pos hp0 hp0
  have hplus := dotI_self_nonnegative (fun i => a i+b i)
  have hminus := dotI_self_nonnegative (fun i => a i-b i)
  have ep := dotI_linear_combination 1 1 a b
  have em := dotI_linear_combination 1 (-1) a b
  simp only [Int.one_mul, Int.neg_one_mul] at ep em
  have eadd : (fun i => a i + -b i) = (fun i => a i-b i) := by funext i; omega
  rw [eadd] at em
  rw [ha, hb] at ep em
  have hrlo : -1 ≤ r := by
    have h : (p : Int)*(p : Int)*(-1) ≤ (p : Int)*(p : Int)*r := by grind
    exact Int.le_of_mul_le_mul_left h hp2
  have hrhi : r ≤ 1 := by
    have h : (p : Int)*(p : Int)*r ≤ (p : Int)*(p : Int)*1 := by grind
    exact Int.le_of_mul_le_mul_left h hp2
  have casesr : r = 0 ∨ r = 1 ∨ r = -1 := by omega
  rcases casesr with h | h | h
  · left; rw [h] at hr; simpa using hr
  · right; left
    have hz : dotI (fun i => a i-b i) (fun i => a i-b i) = 0 := by
      rw [h] at hr
      grind
    have he := dotI_self_eq_zero (fun i => a i-b i) hz
    funext i
    have := he i
    omega
  · right; right
    have hz : dotI (fun i => a i+b i) (fun i => a i+b i) = 0 := by
      rw [h] at hr
      grind
    have he := dotI_self_eq_zero (fun i => a i+b i) hz
    funext i
    have := he i
    omega

#print axioms inner_product_divisible
#print axioms orthogonal_or_equal_up_to_sign

end Wang38
