import SwapArithmetic

open scoped BigOperators
namespace Wang38

/-- On a constant-residue block that varies, all entries have two values. -/
theorem residue_block_two_values {p n : Nat} (hp : OddPrime p)
    (a : IVector n) (ha : dotI a a = (p : Int)*(p : Int)) (hfull : FullSupport p a)
    (I : Finset (Fin n)) (hres : ∀ i ∈ I, ∀ j ∈ I, a i % (p : Int) = a j % (p : Int))
    (i j : Fin n) (hi : i ∈ I) (hj : j ∈ I) (hne : a i ≠ a j) :
    ∀ k ∈ I, a k = a i ∨ a k = a j := by
  intro k hk
  by_cases hki : a k = a i
  · exact Or.inl hki
  by_cases hkj : a k = a j
  · exact Or.inr hkj
  have hijgap := residue_pair_gap hp a ha hfull i j (hres i hi j hj) hne
  have hikgap := residue_pair_gap hp a ha hfull i k (hres i hi k hk) (Ne.symm hki)
  have hjkgap := residue_pair_gap hp a ha hfull j k (hres j hj k hk) (Ne.symm hkj)
  have hp0 : 0 < (p : Int) := by have := hp.1; omega
  rcases hijgap with hijgap | hijgap <;>
    rcases hikgap with hikgap | hikgap <;>
    rcases hjkgap with hjkgap | hjkgap <;> omega

/-- The varying constant-residue block has exactly one exceptional position.
No completeness assumption or root-system classification is used. -/
theorem residue_block_one_exception {p n : Nat} (hp : OddPrime p)
    (a : IVector n) (ha : dotI a a = (p : Int)*(p : Int)) (hfull : FullSupport p a)
    (I : Finset (Fin n)) (hres : ∀ i ∈ I, ∀ j ∈ I, a i % (p : Int) = a j % (p : Int))
    (i j : Fin n) (hi : i ∈ I) (hj : j ∈ I) (hne : a i ≠ a j) :
    (∀ k ∈ I, k ≠ i → a k = a j) ∨ (∀ k ∈ I, k ≠ j → a k = a i) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨⟨k, hk, hki, hka⟩, ⟨l, hl, hlj, hla⟩⟩
  have hkval := (residue_block_two_values hp a ha hfull I hres i j hi hj hne k hk).resolve_right hka
  have hlval := (residue_block_two_values hp a ha hfull I hres i j hi hj hne l hl).resolve_left hla
  have hij : i ≠ j := by intro he; subst j; exact hne rfl
  have hkj : k ≠ j := by intro he; subst k; exact hne hkval.symm
  have hli : l ≠ i := by intro he; subst l; exact hne hlval
  have hkl : k ≠ l := by intro he; subst l; exact hne (hkval.symm.trans hlval)
  have hnkl : a k ≠ a l := by rw [hkval, hlval]; exact hne
  exact no_disjoint_varying_pairs hp a ha hfull i j k l hij hkl hki hkj hli hlj
    (hres i hi j hj) (hres k hk l hl) hne hnkl

 theorem square_pair_le_norm {n : Nat} (a : IVector n) (i j : Fin n) (hij : i ≠ j) :
    a i*a i+a j*a j ≤ dotI a a := by
  have hs : ({i,j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun k _ _ => int_square_nonnegative (a k))
  simpa [dotI, sumI, List.sum_ofFn, Finset.sum_pair hij] using h

 theorem coordinate_abs_lt_prime {p n : Nat} (hp : OddPrime p)
    (a : IVector n) (ha : dotI a a = (p : Int)*(p : Int)) (hfull : FullSupport p a)
    (i j : Fin n) (hij : i ≠ j) : -(p : Int) < a i ∧ a i < (p : Int) := by
  have hj0 : a j ≠ 0 := by intro h; have hz := hfull j; simp [h] at hz
  have hjpos := int_square_positive hj0
  have hpair := square_pair_le_norm a i j hij
  rw [ha] at hpair
  have hp0 : 0 < (p : Int) := by have := hp.1; omega
  constructor <;> nlinarith [sq_nonneg (a i+(p : Int)), sq_nonneg (a i-(p : Int))]

 theorem delta_norm {n : Nat} (i : Fin n) : dotI (deltaVector i) (deltaVector i) = 1 := by
  rw [dotI_delta]
  simp [deltaVector]

 theorem add_delta_norm {n : Nat} (a : IVector n) (c : Int) (i : Fin n) :
    dotI (fun k => a k+c*deltaVector i k) (fun k => a k+c*deltaVector i k) =
      dotI a a+2*c*a i+c*c := by
  have h := dotI_linear_combination 1 c a (deltaVector i)
  simpa [dotI_delta, delta_norm, deltaVector] using h

/-- A varying residue block produces the actual integer vector needed by the
frequency inequality. `ε` is a single global sign, not independent choices. -/
theorem residue_block_exchange_vector {p n : Nat} (hp : OddPrime p)
    (a : IVector n) (ha : dotI a a = (p : Int)*(p : Int)) (hfull : FullSupport p a)
    (I : Finset (Fin n)) (hres : ∀ i ∈ I, ∀ j ∈ I, a i % (p : Int) = a j % (p : Int))
    (i j : Fin n) (hi : i ∈ I) (hj : j ∈ I) (hne : a i ≠ a j) :
    ∃ (u : IVector n) (s : Int) (ε : Int),
      0 < s ∧ s < (p : Int) ∧ (ε = 1 ∨ ε = -1) ∧
      dotI u u = 2*(p : Int)*s ∧
      (∀ k ∈ I, u k = s) ∧
      (∀ k, u k % (p : Int) = (ε*a k) % (p : Int)) := by
  have hij : i ≠ j := by intro h; subst j; exact hne rfl
  have hform : ∃ e ∈ I, ∃ r : Int, (∀ k ∈ I, k ≠ e → a k = r) ∧
      (a e = r-(p : Int) ∨ a e = r+(p : Int)) ∧
      -(p : Int) < r ∧ r < (p : Int) := by
    rcases residue_block_one_exception hp a ha hfull I hres i j hi hj hne with h | h
    · refine ⟨i, hi, a j, h, ?_, ?_⟩
      · have hg := residue_pair_gap hp a ha hfull i j (hres i hi j hj) hne
        omega
      · exact coordinate_abs_lt_prime hp a ha hfull j i (Ne.symm hij)
    · refine ⟨j, hj, a i, h, ?_, ?_⟩
      · have hg := residue_pair_gap hp a ha hfull j i (hres j hj i hi) (Ne.symm hne)
        omega
      · exact coordinate_abs_lt_prime hp a ha hfull i j hij
  rcases hform with ⟨e, he, r, hr, hae, hrlo, hrhi⟩
  have hp0 : 0 < (p : Int) := by have := hp.1; omega
  rcases hae with hae | hae
  · let u : IVector n := fun k => a k+(p : Int)*deltaVector e k
    have hnorm : dotI u u = 2*(p : Int)*r := by
      dsimp [u]
      rw [add_delta_norm, ha, hae]
      ring
    have hr0 : 0 < r := by
      have hnonneg := dotI_self_nonnegative u
      rw [hnorm] at hnonneg
      have hrne : r ≠ 0 := by
        intro hz
        have h := hfull e
        rw [hae, hz] at h
        simp at h
      have hrnonneg := Int.nonneg_of_mul_nonneg_right hnonneg (by omega : 0 < 2*(p : Int))
      omega
    refine ⟨u, r, 1, hr0, hrhi, Or.inl rfl, hnorm, ?_, ?_⟩
    · intro k hk
      by_cases hke : k = e
      · subst k; simp [u, deltaVector, hae]
      · simp [u, deltaVector, hke, hr k hk hke]
    · intro k
      simp [u, Int.add_emod]
  · let u : IVector n := fun k => -a k+(p : Int)*deltaVector e k
    have hnorm : dotI u u = 2*(p : Int)*(-r) := by
      have hn := dotI_linear_combination (-1) (p : Int) a (deltaVector e)
      rw [delta_norm, dotI_delta, ha, hae] at hn
      simp only [Int.neg_one_mul] at hn
      change dotI u u = _ at hn
      nlinarith
    have hr0 : 0 < -r := by
      have hnonneg := dotI_self_nonnegative u
      rw [hnorm] at hnonneg
      have hrne : r ≠ 0 := by
        intro hz
        have h := hfull e
        rw [hae, hz] at h
        simp at h
      have hrnonneg := Int.nonneg_of_mul_nonneg_right hnonneg (by omega : 0 < 2*(p : Int))
      omega
    refine ⟨u, -r, -1, hr0, by omega, Or.inr rfl, hnorm, ?_, ?_⟩
    · intro k hk
      by_cases hke : k = e
      · subst k; simp [u, deltaVector, hae]
      · simp [u, deltaVector, hke, hr k hk hke]
    · intro k
      simp [u, Int.add_emod]

#print axioms residue_block_two_values
#print axioms residue_block_one_exception
#print axioms residue_block_exchange_vector

end Wang38
