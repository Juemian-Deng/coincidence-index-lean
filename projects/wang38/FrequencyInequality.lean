import Std

/-!
The all-prime frequency inequality in Section 5 of the accepted matrix-only
written proof. This file proves that inequality, not the matrix-to-histogram
construction, and not Conjecture 38(ii).
-/
namespace Wang38.Frequency

def sumN : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumN n f + f n

theorem sumN_add (a b : Nat) (f : Nat → Int) :
    sumN (a+b) f = sumN a f + sumN b (fun i => f (a+i)) := by
  induction b with
  | zero => simp [sumN]
  | succ b ih => simp [sumN, ih, Int.add_assoc]

theorem sumN_lower (n : Nat) (f : Nat → Int) (z : Int)
    (h : ∀ i, i < n → z ≤ f i) : (n : Int) * z ≤ sumN n f := by
  induction n with
  | zero => simp [sumN]
  | succ n ih =>
    have hb := ih (fun i hi => h i (by omega))
    have hl := h n (by omega)
    simp only [sumN, Int.natCast_add, Int.natCast_one]
    grind

theorem sumN_nonnegative (n : Nat) (f : Nat → Int)
    (h : ∀ i, i < n → 0 ≤ f i) : 0 ≤ sumN n f := by
  simpa using sumN_lower n f 0 h

def mass (N : Nat) (c : Nat → Nat) : Int :=
  sumN N (fun i => (c (i+1) : Int))

def squareMass (N : Nat) (c : Nat → Nat) : Int :=
  sumN N (fun i => (c (i+1) : Int) * (i+1 : Nat) * (i+1 : Nat))

def excessTerm (s : Nat) (c : Nat → Nat) (i : Nat) : Int :=
  (c (i+1) : Int) * (((i+1 : Nat) : Int) * ((i+1 : Nat) : Int) - (s : Int))

theorem sum_excess (N s : Nat) (c : Nat → Nat) :
    sumN N (excessTerm s c) = squareMass N c - (s : Int) * mass N c := by
  induction N with
  | zero => simp [sumN, squareMass, mass]
  | succ N ih =>
    simp only [sumN, squareMass, mass] at ih ⊢
    simp only [excessTerm]
    grind

/-- The exact useful strengthening from the written proof. Here `c t` is
the number of coordinates whose nonzero integer magnitude is `t`.
The maximal multiplicity `m` is attained at `s`. -/
theorem most_frequent_magnitude (N s m : Nat) (c : Nat → Nat)
    (hs : 1 ≤ s) (hsN : s ≤ N)
    (hmax : ∀ t, 1 ≤ t → t ≤ N → c t ≤ m)
    (hattain : c s = m) :
    (s : Int) * mass N c + (m : Int) * ((s : Int)-1) ≤ squareMass N c := by
  have hsI : 1 ≤ (s : Int) := by omega
  have hmI : 0 ≤ (m : Int) := by omega
  have hhead : ∀ i, i < s-1 →
      -(m : Int) * ((s : Int)-1) ≤ excessTerm s c i := by
    intro i hi
    have hci : (c (i+1) : Int) ≤ (m : Int) := by
      have h := hmax (i+1) (by omega) (by omega)
      omega
    have hc0 : 0 ≤ (c (i+1) : Int) := by omega
    have hi1 : 1 ≤ ((i+1 : Nat) : Int) := by omega
    have hsq := Int.mul_le_mul hi1 hi1 (by omega : (0 : Int) ≤ 1)
      (by omega : (0 : Int) ≤ ((i+1 : Nat) : Int))
    have hmul := Int.mul_le_mul_of_nonneg_left
      (show -((s : Int)-1) ≤ ((i+1 : Nat) : Int)*((i+1 : Nat) : Int)-(s : Int) by omega) hc0
    have hmul2 := Int.mul_le_mul_of_nonneg_right hci
      (show 0 ≤ (s : Int)-1 by omega)
    unfold excessTerm
    grind
  have head := sumN_lower (s-1) (excessTerm s c)
    (-(m : Int) * ((s : Int)-1)) hhead
  have htail : ∀ i, i < N-s → 0 ≤ excessTerm s c (s+i) := by
    intro i hi
    have hti : (s : Int) ≤ ((s+i+1 : Nat) : Int) := by omega
    have ht1 : 1 ≤ ((s+i+1 : Nat) : Int) := by omega
    have hsq := Int.mul_le_mul_of_nonneg_left ht1
      (show 0 ≤ ((s+i+1 : Nat) : Int) by omega)
    have hn : 0 ≤ ((s+i+1 : Nat) : Int)*((s+i+1 : Nat) : Int)-(s : Int) := by
      simp only [Int.mul_one] at hsq
      omega
    exact Int.mul_nonneg (by omega) hn
  have tail := sumN_nonnegative (N-s) (fun i => excessTerm s c (s+i)) htail
  have hsplit : sumN N (excessTerm s c) =
      sumN (s-1) (excessTerm s c) + excessTerm s c (s-1) +
      sumN (N-s) (fun i => excessTerm s c (s+i)) := by
    have hN : N = s + (N-s) := by omega
    have ha := sumN_add s (N-s) (excessTerm s c)
    rw [← hN] at ha
    have hs' : s = (s-1)+1 := by omega
    have hb : sumN s (excessTerm s c) =
        sumN (s-1) (excessTerm s c) + excessTerm s c (s-1) := by
      calc
        sumN s (excessTerm s c) = sumN ((s-1)+1) (excessTerm s c) :=
          congrArg (fun k => sumN k (excessTerm s c)) hs'
        _ = _ := rfl
    rw [hb] at ha
    exact ha
  have hmid : excessTerm s c (s-1) =
      (m : Int) * ((s : Int)*(s : Int)-(s : Int)) := by
    unfold excessTerm
    have he : s-1+1 = s := by omega
    rw [he, hattain]
  have hcast : ((s-1 : Nat) : Int) = (s : Int)-1 := by omega
  rw [hcast] at head
  rw [hmid] at hsplit
  have he := sum_excess N s c
  grind

theorem weighted_dimension_bound (N s m p : Nat) (c : Nat → Nat)
    (hs : 1 ≤ s) (hsN : s ≤ N)
    (hmax : ∀ t, 1 ≤ t → t ≤ N → c t ≤ m)
    (hattain : c s = m)
    (hnorm : squareMass N c = 2 * (p : Int) * (s : Int)) :
    mass N c ≤ 2 * (p : Int) := by
  have h := most_frequent_magnitude N s m c hs hsN hmax hattain
  have hm : 0 ≤ (m : Int) * ((s : Int)-1) :=
    Int.mul_nonneg (by omega) (by omega)
  have hl : (s : Int) * mass N c ≤ (s : Int) * (2 * (p : Int)) := by
    rw [hnorm] at h
    grind
  exact Int.le_of_mul_le_mul_left hl (by omega)

#print axioms most_frequent_magnitude
#print axioms weighted_dimension_bound

end Wang38.Frequency
