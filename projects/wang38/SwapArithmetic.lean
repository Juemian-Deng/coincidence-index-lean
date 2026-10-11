import MathlibBridge
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators
namespace Wang38

def swapVector {n : Nat} (a : IVector n) (i j : Fin n) : IVector n :=
  fun k => a (Equiv.swap i j k)

def deltaVector {n : Nat} (i : Fin n) : IVector n := fun k => if k = i then 1 else 0

 theorem dotI_delta {n : Nat} (a : IVector n) (i : Fin n) :
    dotI a (deltaVector i) = a i := by
  simp [dotI, sumI, deltaVector, List.sum_ofFn]

 theorem swapVector_expansion {n : Nat} (a : IVector n) (i j : Fin n) (hij : i ≠ j) :
    swapVector a i j = fun k => a k + (a j-a i)*deltaVector i k +
      (a i-a j)*deltaVector j k := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [swapVector, deltaVector, hij]
  · by_cases hkj : k = j
    · subst k
      simp [swapVector, deltaVector, Ne.symm hij]
    · simp [swapVector, deltaVector, Equiv.swap_apply_def, hki, hkj]

 theorem dotI_swapVector {n : Nat} (a b : IVector n) (i j : Fin n) (hij : i ≠ j) :
    dotI a (swapVector b i j) = dotI a b + (a i-a j)*(b j-b i) := by
  rw [swapVector_expansion b i j hij, dotI_add_right, dotI_add_right,
    dotI_smul_right, dotI_smul_right, dotI_delta, dotI_delta]
  ring

 theorem swapVector_norm {n : Nat} (a : IVector n) (i j : Fin n) :
    dotI (swapVector a i j) (swapVector a i j) = dotI a a := by
  simp only [dotI, sumI, List.sum_ofFn, swapVector]
  exact Equiv.sum_comp (Equiv.swap i j) (fun k => a k*a k)

 theorem same_residue_orthogonal_or_equal {p n : Nat} (hp : OddPrime p)
    (a b : IVector n) (ha : dotI a a = (p : Int)*(p : Int))
    (hb : dotI b b = (p : Int)*(p : Int))
    (hnz : ∃ i, a i % (p : Int) ≠ 0)
    (hres : ∀ i, b i % (p : Int) = a i % (p : Int)) :
    dotI a b = 0 ∨ b = a := by
  have hp3 := oddPrime_ge_three hp
  have hone : (1 : Int) % (p : Int) ≠ 0 := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    decide
  have hres' : ∀ i, (b i-1*a i) % (p : Int) = 0 := by
    intro i
    simpa using (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (hres i))
  rcases orthogonal_or_equal_up_to_sign hp a b ha hb 1 hone hres' with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rcases hnz with ⟨i, hi⟩
    have he := (hres i).symm
    rw [h] at he
    have hz := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he
    have hid : a i - -a i = 2*a i := by ring
    rw [hid] at hz
    have htwo : (2 : Int) % (p : Int) ≠ 0 := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      decide
    have hd := prime_cancel_nonzero_residue hp 2 (a i) htwo (Int.dvd_of_emod_eq_zero hz)
    exact False.elim (hi (Int.emod_eq_zero_of_dvd hd))

 theorem swapVector_residue {p n : Nat} (a : IVector n) (i j : Fin n)
    (hres : a i % (p : Int) = a j % (p : Int)) :
    ∀ k, swapVector a i j k % (p : Int) = a k % (p : Int) := by
  intro k
  by_cases hki : k = i
  · subst k; simpa [swapVector] using hres.symm
  · by_cases hkj : k = j
    · subst k; simpa [swapVector] using hres
    · simp [swapVector, Equiv.swap_apply_def, hki, hkj]

 theorem unequal_swap_orthogonal {p n : Nat} (hp : OddPrime p)
    (a : IVector n) (ha : dotI a a = (p : Int)*(p : Int))
    (hfull : FullSupport p a) (i j : Fin n)
    (hres : a i % (p : Int) = a j % (p : Int)) (hne : a i ≠ a j) :
    dotI a (swapVector a i j) = 0 := by
  have hn : dotI (swapVector a i j) (swapVector a i j) = (p : Int)*(p : Int) := by
    rw [swapVector_norm, ha]
  rcases same_residue_orthogonal_or_equal hp a (swapVector a i j) ha hn
    ⟨i, hfull i⟩ (swapVector_residue a i j hres) with h | h
  · exact h
  · have he := congrFun h i
    simp only [swapVector, Equiv.swap_apply_left] at he
    exact False.elim (hne he.symm)

 theorem residue_pair_gap {p n : Nat} (hp : OddPrime p)
    (a : IVector n) (ha : dotI a a = (p : Int)*(p : Int))
    (hfull : FullSupport p a) (i j : Fin n)
    (hres : a i % (p : Int) = a j % (p : Int)) (hne : a i ≠ a j) :
    a i-a j = (p : Int) ∨ a i-a j = -(p : Int) := by
  have hij : i ≠ j := by intro h; subst j; exact hne rfl
  have hz := unequal_swap_orthogonal hp a ha hfull i j hres hne
  rw [dotI_swapVector a a i j hij, ha] at hz
  have he : ((a i-a j)-(p : Int))*((a i-a j)+(p : Int)) = 0 := by nlinarith
  rcases mul_eq_zero.mp he with h | h
  · left; omega
  · right; omega

 theorem no_disjoint_varying_pairs {p n : Nat} (hp : OddPrime p)
    (a : IVector n) (ha : dotI a a = (p : Int)*(p : Int))
    (hfull : FullSupport p a) (i j k l : Fin n)
    (_hij : i ≠ j) (hkl : k ≠ l)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (hrij : a i % (p : Int) = a j % (p : Int))
    (hrkl : a k % (p : Int) = a l % (p : Int))
    (hnij : a i ≠ a j) (hnkl : a k ≠ a l) : False := by
  let b := swapVector a i j
  let c := swapVector b k l
  have hb : dotI b b = (p : Int)*(p : Int) := by dsimp [b]; rw [swapVector_norm, ha]
  have hc : dotI c c = (p : Int)*(p : Int) := by dsimp [c]; rw [swapVector_norm, hb]
  have br : ∀ t, b t % (p : Int) = a t % (p : Int) := swapVector_residue a i j hrij
  have cr : ∀ t, c t % (p : Int) = a t % (p : Int) := by
    have hbrkl : b k % (p : Int) = b l % (p : Int) := by rw [br k, br l, hrkl]
    intro t
    exact (swapVector_residue b k l hbrkl t).trans (br t)
  have hci : c i = a j := by
    simp [c, b, swapVector, Equiv.swap_apply_def, Ne.symm hki, Ne.symm hli]
  have hca : c ≠ a := by
    intro h
    have := congrFun h i
    rw [hci] at this
    exact hnij this.symm
  have horth := (same_residue_orthogonal_or_equal hp a c ha hc ⟨i, hfull i⟩ cr).resolve_right hca
  have hborth := unequal_swap_orthogonal hp a ha hfull i j hrij hnij
  have he := dotI_swapVector a b k l hkl
  have hbk : b k = a k := by simp [b, swapVector, Equiv.swap_apply_def, hki, hkj]
  have hbl : b l = a l := by simp [b, swapVector, Equiv.swap_apply_def, hli, hlj]
  change dotI a c = _ at he
  rw [horth, hbk, hbl] at he
  change dotI a b = 0 at hborth
  rw [hborth] at he
  have hgap := residue_pair_gap hp a ha hfull k l hrkl hnkl
  have hp0 : 0 < (p : Int) := by have := hp.1; omega
  rcases hgap with hgap | hgap <;> nlinarith [sq_nonneg (p : Int)]

#print axioms same_residue_orthogonal_or_equal
#print axioms residue_pair_gap
#print axioms no_disjoint_varying_pairs

end Wang38
