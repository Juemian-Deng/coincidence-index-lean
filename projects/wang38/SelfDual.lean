import Characteristic

/-! A direct self-duality proof, avoiding an assumed index or covolume formula. -/
open scoped BigOperators
namespace Wang38I
open Wang38

lemma dotQ_single_right {n : ℕ} (x : QVector n) (j : Fin n) (c : ℚ) :
    dotQ x (fun i => if i = j then c else 0) = x j * c := by
  simp [dotQ, mul_ite]

lemma dotI_sub_right {n : ℕ} (x y z : IVector n) :
    dotI x (fun i => y i - z i) = dotI x y - dotI x z := by
  simp [dotI, sumI, List.sum_ofFn, mul_sub, Finset.sum_sub_distrib]

lemma dotQ_sub_right {n : ℕ} (x y z : QVector n) :
    dotQ x (fun i => y i - z i) = dotQ x y - dotQ x z := by
  simp [dotQ, mul_sub, Finset.sum_sub_distrib]

/-- A vector pairing integrally with the neighbor has denominator dividing p. -/
lemma dual_has_numerator {p n : ℕ} (u : IVector n) (x : QVector n)
    (hx : ∀ y ∈ neighbor p u, Integral (dotQ x y)) :
    ∃ a : IVector n, ∀ i, (a i : ℚ) = (p : ℚ) * x i := by
  classical
  have hi : ∀ j : Fin n, ∃ a : ℤ, (a : ℚ) = (p : ℚ) * x j := by
    intro j
    let m : IVector n := fun i => if i = j then (p : ℤ) else 0
    have hm : castVector m ∈ neighbor p u := by
      apply base_mem_neighbor
      rw [dotI_comm]
      dsimp [m]
      rw [dotI_single]
      exact dvd_mul_left _ _
    obtain ⟨a, ha⟩ := hx (castVector m) hm
    refine ⟨a, ?_⟩
    simpa [castVector, m, dotQ, mul_ite, mul_comm] using ha.symm
  choose a ha using hi
  exact ⟨a, ha⟩

/-- The residue numerator of a dual vector lies in the same line as u. -/
lemma dual_numerator_line {p n : ℕ} (hp : OddPrime p)
    (u : IVector n) (huj : ∃ j, u j % (p : ℤ) ≠ 0)
    (x : QVector n) (hx : ∀ y ∈ neighbor p u, Integral (dotQ x y))
    (a : IVector n) (ha : ∀ i, (a i : ℚ) = (p : ℚ) * x i) :
    ∃ k : ℤ, ∀ i, (p : ℤ) ∣ a i - k * u i := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  obtain ⟨j, hj⟩ := huj
  have hujZ : (u j : ZMod p) ≠ 0 := by
    exact fun hh => hj ((intCast_mod_zero_iff p _).mp hh)
  let q : ZMod p := (a j : ZMod p) / (u j : ZMod p)
  let k : ℤ := q.val
  have hk : (k : ZMod p) = q := by simp [k]
  refine ⟨k, ?_⟩
  intro i
  let m : IVector n := fun t =>
    (if t = i then u j else 0) - (if t = j then u i else 0)
  have hm : dotI m u = 0 := by
    rw [dotI_comm]
    dsimp [m]
    rw [dotI_sub_right, dotI_single, dotI_single]
    ring
  obtain ⟨b, hb⟩ := hx (castVector m) (base_mem_neighbor u m (hm ▸ dvd_zero _))
  have hb' : x i * (u j : ℚ) - x j * (u i : ℚ) = (b : ℚ) := by
    simpa [dotQ, castVector, m, mul_sub, mul_ite, Finset.sum_sub_distrib] using hb
  have hrel : a i * u j - a j * u i = (p : ℤ) * b := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [ha i, ha j]
    nlinarith [hb']
  have hz : (a i : ZMod p) * (u j : ZMod p) = (a j : ZMod p) * (u i : ZMod p) := by
    have hh := congrArg (fun t : ℤ => (t : ZMod p)) hrel
    push_cast at hh
    simp only [ZMod.natCast_self, zero_mul] at hh
    exact sub_eq_zero.mp hh
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  rw [hk]
  apply sub_eq_zero.mpr
  dsimp [q]
  apply (mul_left_inj' hujZ).mp
  calc
    _ = (a j : ZMod p) * (u i : ZMod p) := hz
    _ = ((a j : ZMod p) / (u j : ZMod p) * (u j : ZMod p)) * (u i : ZMod p) := by
      rw [div_mul_cancel₀ _ hujZ]
    _ = _ := by ring

/-- The constructed prime-neighbor equals its integral Euclidean dual.
This is the unimodularity step, proved rather than assumed. -/
theorem neighbor_self_dual {p n : ℕ} (hp : OddPrime p)
    (u : IVector n) (huj : ∃ j, u j % (p : ℤ) ≠ 0)
    (hu : (p : ℤ) * p ∣ dotI u u) (x : QVector n) :
    (∀ y ∈ neighbor p u, Integral (dotQ x y)) ↔ x ∈ neighbor p u := by
  have hp0 : p ≠ 0 := by have := hp.1; omega
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := dual_has_numerator u x hx
    obtain ⟨k, hk⟩ := dual_numerator_line hp u huj x hx a ha
    let m : IVector n := fun i => (a i - k * u i) / (p : ℤ)
    have hm : ∀ i, a i = (p : ℤ) * m i + k * u i := by
      intro i
      have hh := Int.emod_add_mul_ediv (a i - k * u i) (p : ℤ)
      rw [Int.emod_eq_zero_of_dvd (hk i)] at hh
      dsimp [m]
      omega
    obtain ⟨t, ht⟩ := hx (fun i => (u i : ℚ) / p) (lift_mem_neighbor hp0 u)
    have ha' : castVector a = fun i => (p : ℚ) * x i := funext ha
    have hu' : castVector u = fun i => (p : ℚ) * ((u i : ℚ) / p) := by
      funext i
      simp [castVector, mul_div_cancel₀, hpQ]
    have hn : dotI a u = (p : ℤ) * p * t := by
      apply Int.cast_injective (α := ℚ)
      rw [← dotQ_cast, ha', hu', dotQ_mul_left, dotQ_mul_right, ht]
      push_cast
      ring
    obtain ⟨s, hs⟩ := hu
    have ham : a = fun i => (p : ℤ) * m i + k * u i := funext hm
    have hmnorm : dotI m u = (p : ℤ) * (t - k * s) := by
      have he : dotI a u = (p : ℤ) * dotI m u + k * dotI u u := by
        rw [ham, dotI_comm, dotI_add_right, dotI_smul_right, dotI_smul_right, dotI_comm]
      rw [hn, hs] at he
      apply mul_left_cancel₀ hpZ
      nlinarith [he]
    refine ⟨m, k, ⟨t - k * s, hmnorm⟩, ?_⟩
    intro i
    rw [← ha i, hm i]
    push_cast
    rfl
  · intro hx y hy
    exact neighbor_integral hp0 u hu hx hy

#print axioms neighbor_self_dual
end Wang38I
