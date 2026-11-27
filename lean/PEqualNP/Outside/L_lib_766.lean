import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_766

open MvPolynomial

def cnt {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → ZMod 2 => f x ≠ 0)).card

theorem cnt_split {n : ℕ} (F : (Fin (n + 1) → ZMod 2) → ZMod 2) :
    cnt F = cnt (fun y => F (Fin.cons 0 y)) + cnt (fun y => F (Fin.cons 1 y)) := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2))]
  rw [Fintype.sum_prod_type]
  exact Fin.sum_univ_two _

theorem cnt_pos {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) (h : ∃ x, f x ≠ 0) : 0 < cnt f := by
  obtain ⟨x, hx⟩ := h
  exact Finset.card_pos.mpr ⟨x, by simp [hx]⟩

theorem z2 (a b : ZMod 2) (h : a + b = 0) : b = a := by
  revert a b; decide

theorem slice {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin (n + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    ∃ q r : MvPolynomial (Fin n) (ZMod 2), q.totalDegree ≤ d ∧
      (r = 0 ∨ r.totalDegree + 1 ≤ d) ∧
      ∀ y : Fin n → ZMod 2, eval (Fin.cons 0 y : Fin (n + 1) → ZMod 2) p = eval y q ∧
        eval (Fin.cons 1 y : Fin (n + 1) → ZMod 2) p = eval y q + eval y r := by
  set P := finSuccEquiv (ZMod 2) n p with hP
  have hc : ∀ i, (P.coeff i).totalDegree + i ≤ d ∨ P.coeff i = 0 := by
    intro i
    by_cases h : P.coeff i = 0
    · exact Or.inr h
    · exact Or.inl ((totalDegree_coeff_finSuccEquiv_add_le p i h).trans hp)
  refine ⟨P.coeff 0, ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1), ?_, ?_, ?_⟩
  · rcases hc 0 with h | h
    · exact h
    · rw [h, totalDegree_zero]; exact Nat.zero_le _
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · left
      apply Finset.sum_eq_zero
      intro i _
      rcases hc (i + 1) with h | h
      · omega
      · exact h
    · right
      have : (∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1)).totalDegree ≤ d - 1 := by
        apply totalDegree_finsetSum_le
        intro i _
        rcases hc (i + 1) with h | h
        · omega
        · rw [h, totalDegree_zero]; exact Nat.zero_le _
      omega
  · intro y
    have key : ∀ a : ZMod 2, eval (Fin.cons a y : Fin (n + 1) → ZMod 2) p =
        eval y (P.coeff 0) + ∑ i ∈ Finset.range P.natDegree, eval y (P.coeff (i + 1)) * a ^ (i + 1) := by
      intro a
      rw [eval_eq_eval_mv_eval', Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
        Finset.sum_range_succ']
      simp [hP, add_comm]
    constructor
    · rw [key 0]; simp
    · rw [key 1]; simp [map_sum]

theorem core (n : ℕ) : ∀ (d : ℕ) (p : MvPolynomial (Fin n) (ZMod 2)), p.totalDegree ≤ d →
    (∃ x : Fin n → ZMod 2, eval x p ≠ 0) → 2 ^ n ≤ 2 ^ d * cnt (fun x => eval x p) := by
  induction n with
  | zero =>
    intro d p _ hx
    have h1 := cnt_pos (fun x => eval x p) hx
    rw [pow_zero]
    exact Nat.mul_pos (Nat.two_pow_pos d) h1
  | succ n ih =>
    intro d p hp hx
    obtain ⟨q, r, hq, hr, hs⟩ := slice d p hp
    have e0 : (fun y : Fin n → ZMod 2 => eval (Fin.cons 0 y : Fin (n + 1) → ZMod 2) p) =
        fun y => eval y q := funext (fun y => (hs y).1)
    have e1 : (fun y : Fin n → ZMod 2 => eval (Fin.cons 1 y : Fin (n + 1) → ZMod 2) p) =
        fun y => eval y q + eval y r := funext (fun y => (hs y).2)
    rw [cnt_split, e0, e1]
    have low : ∀ c0 c1 : ℕ, (∃ y : Fin n → ZMod 2, eval y r ≠ 0) →
        (cnt (fun y => eval y r) = c0 ∨ cnt (fun y => eval y r) = c1) →
        2 ^ (n + 1) ≤ 2 ^ d * (c0 + c1) := by
      intro c0 c1 hy hc
      have hr0 : r ≠ 0 := by
        rintro rfl
        obtain ⟨y, hy⟩ := hy
        exact hy (by simp)
      have hd : r.totalDegree + 1 ≤ d := hr.resolve_left hr0
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      have h := ih d' r (by omega) hy
      have hle : cnt (fun y => eval y r) ≤ c0 + c1 := by omega
      have h3 := Nat.mul_le_mul_left (2 ^ d') hle
      rw [pow_succ, pow_succ]
      nlinarith
    by_cases h0 : ∃ y : Fin n → ZMod 2, eval y q ≠ 0
    · by_cases h1 : ∃ y : Fin n → ZMod 2, eval y q + eval y r ≠ 0
      · have hqr : (q + r).totalDegree ≤ d := by
          refine (totalDegree_add q r).trans (max_le hq ?_)
          rcases hr with h | h
          · rw [h, totalDegree_zero]; exact Nat.zero_le _
          · omega
        have a0 := ih d q hq h0
        have a1 := ih d (q + r) hqr (by simpa using h1)
        simp only [map_add] at a1
        rw [pow_succ, Nat.mul_add]
        omega
      · simp only [not_exists, not_not] at h1
        have hrq : (fun y : Fin n → ZMod 2 => eval y r) = fun y => eval y q :=
          funext (fun y => z2 _ _ (h1 y))
        apply low
        · obtain ⟨y, hy⟩ := h0
          exact ⟨y, by rw [z2 _ _ (h1 y)]; exact hy⟩
        · left; rw [hrq]
    · simp only [not_exists, not_not] at h0
      have hrq : (fun y : Fin n → ZMod 2 => eval y q + eval y r) = fun y => eval y r :=
        funext (fun y => by rw [h0 y, zero_add])
      apply low
      · obtain ⟨x, hx⟩ := hx
        have hxc : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
        have hx0 : x 0 = 0 ∨ x 0 = 1 := by
          generalize x 0 = a
          fin_cases a
          · left; rfl
          · right; rfl
        rcases hx0 with h | h
        · rw [hxc, h, (hs _).1, h0] at hx
          exact absurd rfl hx
        · rw [hxc, h, (hs _).2, h0, zero_add] at hx
          exact ⟨_, hx⟩
      · right; rw [hrq]

end PEqualNP.Outside.L_lib_766

theorem PEqualNP.Outside.L_lib_766 : ∀ (n d : ℕ) (p : MvPolynomial (Fin n) (ZMod 2)), p.totalDegree ≤ d →
  (∃ x : Fin n → ZMod 2, MvPolynomial.eval x p ≠ 0) →
  2 ^ n ≤ 2 ^ d * (Finset.univ.filter (fun x : Fin n → ZMod 2 => MvPolynomial.eval x p ≠ 0)).card := by
  intro n d p hp hx
  exact PEqualNP.Outside.L_lib_766.core n d p hp hx
