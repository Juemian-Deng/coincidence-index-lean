import SquareDimensionBound

/-! Source-level bridges from primitive rational matrices to their integer
numerators, including full support in BOTH matrix directions. -/
namespace Wang38

theorem dotI_zero_left {n : Nat} (v : IVector n) :
    dotI (fun _ => 0) v = 0 := by
  induction n with
  | zero => simp [dotI, sumI]
  | succ n ih => simpa [dotI, sumI, List.ofFn_succ] using ih (fun i => v i.succ)

theorem integer_unit_dot_nonzero {n : Nat} (u v : IVector n)
    (hu : dotI u u = 1) (hv : ∀ i, v i ≠ 0) : dotI u v ≠ 0 := by
  induction n with
  | zero => simp [dotI, sumI] at hu
  | succ n ih =>
    have he : u 0*u 0 + dotI (fun i : Fin n => u i.succ) (fun i => u i.succ) = 1 := by
      simpa only [dotI, sumI, List.ofFn_succ, List.sum_cons] using hu
    by_cases hz : u 0 = 0
    · have ht : dotI (fun i : Fin n => u i.succ) (fun i => u i.succ) = 1 := by
        rw [hz] at he
        simpa using he
      have hi := ih (fun i => u i.succ) (fun i => v i.succ) ht (fun i => hv i.succ)
      simpa only [dotI, sumI, List.ofFn_succ, List.sum_cons, hz,
        Int.zero_mul, Int.zero_add] using hi
    · have hp := int_square_positive hz
      have htpos := dotI_self_nonnegative (fun i : Fin n => u i.succ)
      have ht : dotI (fun i : Fin n => u i.succ) (fun i => u i.succ) = 0 := by omega
      have htz := dotI_self_eq_zero (fun i : Fin n => u i.succ) ht
      have heq : (fun i : Fin n => u i.succ) = (fun _ => 0) := funext htz
      have huv : dotI u v = u 0*v 0 := by
        calc
          dotI u v = u 0*v 0 + dotI (fun i : Fin n => u i.succ) (fun i => v i.succ) := by
            simp only [dotI, sumI, List.ofFn_succ, List.sum_cons]
          _ = _ := by rw [heq, dotI_zero_left, Int.add_zero]
      rw [huv]
      intro hh
      rcases Int.mul_eq_zero.mp hh with h | h
      · exact hz h
      · exact hv 0 h

theorem numerator_column_gram {p n : Nat} {Q : QMatrix n} {A : IMatrix n}
    (ho : Orthogonal Q) (hn : Numerator p Q A) (j k : Fin n) :
    dotI (fun i => A i j) (fun i => A i k) =
      if j = k then (p : Int)*(p : Int) else 0 := by
  have h : ((dotI (fun i => A i j) (fun i => A i k)) : Rat) =
      if j = k then (p : Rat)*(p : Rat) else 0 := by
    unfold dotI
    rw [← sumQ_intCast]
    have hf : (fun i => ((A i j * A i k : Int) : Rat)) =
        (fun i => (p : Rat)*(p : Rat)*(Q i j * Q i k)) := by
      funext i
      rw [Rat.intCast_mul, hn, hn]
      grind
    rw [hf, sumQ_smul, ho]
    split <;> simp_all
  apply Rat.intCast_inj.mp
  split <;> simp_all [Rat.intCast_mul, Rat.intCast_natCast]

theorem nonzero_residue_column {p n : Nat} (hp : OddPrime p)
    {v : IVector n} (hv : FullSupport p v) {A : IMatrix n}
    (hl : ColumnsInLine p v A) {i j : Fin n}
    (hnz : A i j % (p : Int) ≠ 0) :
    ∀ k, A k j % (p : Int) ≠ 0 := by
  rcases hl j with ⟨c, hc⟩
  have hc0 : c % (p : Int) ≠ 0 := by
    intro hz
    have he := hc i
    rw [Int.mul_emod, hz] at he
    simp at he
    exact hnz he
  intro k
  rw [hc k]
  exact nonzero_product_mod hp c (v k) hc0 (hv k)

/-- The full-support line and orthogonality exclude zero residue columns.
This closes Section 1 of the matrix proof for the actual source definitions. -/
theorem numerator_full_support {p n : Nat} (hp : OddPrime p)
    {v : IVector n} (hv : FullSupport p v) {Q : QMatrix n} {A : IMatrix n}
    (ho : Orthogonal Q) (hn : Numerator p Q A)
    (hk : RankOneMod p A) (hl : ColumnsInLine p v A) :
    ∀ i j, A i j % (p : Int) ≠ 0 := by
  rcases hk.1 with ⟨i₀, j₀, hz⟩
  have href := nonzero_residue_column hp hv hl hz
  have hrefInt : ∀ i, A i j₀ ≠ 0 := by
    intro i hi
    have := href i
    simp [hi] at this
  have hp0 : (p : Int) ≠ 0 := by have := hp.1; omega
  have hp20 : (p : Int)*(p : Int) ≠ 0 := by
    intro h
    rcases Int.mul_eq_zero.mp h with h | h <;> exact hp0 h
  intro i j hzero
  rcases hl j with ⟨c, hc⟩
  have hc0 : c % (p : Int) = 0 := by
    by_cases h : c % (p : Int) = 0
    · exact h
    · have hprod := nonzero_product_mod hp c (v i) h (hv i)
      rw [← hc i] at hprod
      exact False.elim (hprod hzero)
  have hall : ∀ k, A k j % (p : Int) = 0 := by
    intro k
    rw [hc k, Int.mul_emod, hc0]
    simp
  have hj : j ≠ j₀ := by
    intro h
    subst j
    exact hz (hall i₀)
  let t : IVector n := fun i => A i j / (p : Int)
  have ht : (fun i => A i j) = (fun i => (p : Int)*t i) := by
    funext i
    have he := Int.emod_add_mul_ediv (A i j) (p : Int)
    rw [hall i] at he
    dsimp [t]
    omega
  have hnorm := numerator_column_norm ho hn j
  rw [ht, dotI_smul_right, dotI_comm (fun i => (p : Int)*t i) t,
    dotI_smul_right] at hnorm
  have hunit : dotI t t = 1 := by
    apply Int.eq_of_mul_eq_mul_left hp20
    grind
  have horth := numerator_column_gram ho hn j j₀
  rw [ite_eq_right hj, ht, dotI_comm (fun i => (p : Int)*t i) (fun i => A i j₀),
    dotI_smul_right, dotI_comm (fun i => A i j₀) t] at horth
  have hdot : dotI t (fun i => A i j₀) = 0 := by
    apply Int.eq_of_mul_eq_mul_left hp0
    simpa using horth
  exact integer_unit_dot_nonzero t (fun i => A i j₀) hunit hrefInt hdot

#print axioms integer_unit_dot_nonzero
#print axioms numerator_column_gram
#print axioms numerator_full_support

end Wang38
