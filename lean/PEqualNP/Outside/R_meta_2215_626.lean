import Mathlib
import PEqualNP.Defs

-- Peel the six points on the first two lines of the missing point: each is one star of
-- four lines, five gates. The core keeps six points and must supply the flag of the
-- other two lines; two more gates join the flag of the first two lines.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem PEqualNP.Outside.R_meta_2215_626
    (core : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 29 ∧
      C.output < 25 + C.size ∧ q < 25 + C.size ∧ ∀ x : Fin 25 → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ i j : Fin 25,
        i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        i.val ∉ ([0, 1, 2, 7, 8, 11] : List ℕ) ∧ x i = true ∧ x j = true) ∧
      (C.eval (List.ofFn x) = false → (C.wires (List.ofFn x)).getD q false =
        (x 15 || x 21)))
    (star : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p a b c d : Fin 25),
      PEqualNP.MetaComplexity.Monotone2 C → C.output < 25 + C.size →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧ C.size ≤ D.size ∧ D.size ≤ C.size + 5 ∧
      D.output < 25 + D.size ∧ ∀ x : Fin 25 → Bool,
      D.eval (List.ofFn x) = (C.eval (List.ofFn x) || (x p && (x a || x b || x c || x d))) ∧
      ∀ w : ℕ, w < 25 + C.size →
        (D.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn x)).getD w false)
    (join : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ) (i : Fin 25),
      PEqualNP.MetaComplexity.Monotone2 C → q < 25 + C.size →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (r : ℕ),
      PEqualNP.MetaComplexity.Monotone2 D ∧ C.size ≤ D.size ∧ D.size ≤ C.size + 1 ∧
      D.output = C.output ∧ r < 25 + D.size ∧ ∀ x : Fin 25 → Bool,
      (D.wires (List.ofFn x)).getD r false = ((C.wires (List.ofFn x)).getD q false || x i) ∧
      ∀ w : ℕ, w < 25 + C.size →
        (D.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn x)).getD w false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  obtain ⟨C0, q, m0, s0, o0, hq, h0⟩ := core
  obtain ⟨C1, m1, l1, s1, o1, h1⟩ := star C0 0 12 14 20 24 m0 o0
  obtain ⟨C2, m2, l2, s2, o2, h2⟩ := star C1 2 12 18 22 23 m1 o1
  obtain ⟨C3, m3, l3, s3, o3, h3⟩ := star C2 8 12 16 17 19 m2 o2
  obtain ⟨C4, m4, l4, s4, o4, h4⟩ := star C3 1 13 19 23 24 m3 o3
  obtain ⟨C5, m5, l5, s5, o5, h5⟩ := star C4 7 13 17 18 20 m4 o4
  obtain ⟨C6, m6, l6, s6, o6, h6⟩ := star C5 11 13 14 16 22 m5 o5
  obtain ⟨C7, r1, m7, l7, s7, e7, hr1, h7⟩ := join C6 q 12 m6 (by omega)
  obtain ⟨C8, r2, m8, l8, s8, e8, hr2, h8⟩ := join C7 r1 13 m7 hr1
  have key : ∀ i j : Fin 25, i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
      i.val ∈ ([0, 1, 2, 7, 8, 11] : List ℕ) →
      (i = 0 ∧ (j = 12 ∨ j = 14 ∨ j = 20 ∨ j = 24)) ∨
      (i = 2 ∧ (j = 12 ∨ j = 18 ∨ j = 22 ∨ j = 23)) ∨
      (i = 8 ∧ (j = 12 ∨ j = 16 ∨ j = 17 ∨ j = 19)) ∨
      (i = 1 ∧ (j = 13 ∨ j = 19 ∨ j = 23 ∨ j = 24)) ∨
      (i = 7 ∧ (j = 13 ∨ j = 17 ∨ j = 18 ∨ j = 20)) ∨
      (i = 11 ∧ (j = 13 ∨ j = 14 ∨ j = 16 ∨ j = 22)) := by
    decide +kernel
  refine ⟨C8, r2, m8, by omega, by omega, hr2, fun x => ?_⟩
  have ev7 : C7.eval (List.ofFn x) = C6.eval (List.ofFn x) := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [e7]
    exact (h7 x).2 _ o6
  have ev8 : C8.eval (List.ofFn x) = C6.eval (List.ofFn x) := by
    rw [← ev7]
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [e8]
    exact (h8 x).2 _ (by omega)
  have hqw : (C6.wires (List.ofFn x)).getD q false = (C0.wires (List.ofFn x)).getD q false := by
    rw [(h6 x).2 q (by omega), (h5 x).2 q (by omega), (h4 x).2 q (by omega), (h3 x).2 q (by omega), (h2 x).2 q (by omega), (h1 x).2 q hq]
  have hr : (C8.wires (List.ofFn x)).getD r2 false = (((C0.wires (List.ofFn x)).getD q false || x 12) || x 13) := by
    rw [(h8 x).1, (h7 x).1, hqw]
  have hev : C8.eval (List.ofFn x) = (C0.eval (List.ofFn x) || (x 0 && (x 12 || x 14 || x 20 || x 24)) || (x 2 && (x 12 || x 18 || x 22 || x 23)) || (x 8 && (x 12 || x 16 || x 17 || x 19)) || (x 1 && (x 13 || x 19 || x 23 || x 24)) || (x 7 && (x 13 || x 17 || x 18 || x 20)) || (x 11 && (x 13 || x 14 || x 16 || x 22))) := by
    rw [ev8, (h6 x).1, (h5 x).1, (h4 x).1, (h3 x).1, (h2 x).1, (h1 x).1]
  have hc := (h0 x).1
  have ha := (h0 x).2
  have main : C8.eval (List.ofFn x) = true ↔ ∃ i j : Fin 25, ((i : ℕ) < 12 ∧ 12 ≤ (j : ℕ) ∧ ((i : ℕ) + (j : ℕ) + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∧ x i = true ∧ x j = true := by
    rw [hev]
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · intro h
      rcases h with (((((h | h) | h) | h) | h) | h) | h
      · obtain ⟨i, j, a1, a2, a3, _, xi, xj⟩ := hc.mp h
        exact ⟨i, j, ⟨a1, a2, a3⟩, xi, xj⟩
      · obtain ⟨hp, hl⟩ := h
        rcases hl with ((hl | hl) | hl) | hl
        · exact ⟨0, 12, by decide, hp, hl⟩
        · exact ⟨0, 14, by decide, hp, hl⟩
        · exact ⟨0, 20, by decide, hp, hl⟩
        · exact ⟨0, 24, by decide, hp, hl⟩
      · obtain ⟨hp, hl⟩ := h
        rcases hl with ((hl | hl) | hl) | hl
        · exact ⟨2, 12, by decide, hp, hl⟩
        · exact ⟨2, 18, by decide, hp, hl⟩
        · exact ⟨2, 22, by decide, hp, hl⟩
        · exact ⟨2, 23, by decide, hp, hl⟩
      · obtain ⟨hp, hl⟩ := h
        rcases hl with ((hl | hl) | hl) | hl
        · exact ⟨8, 12, by decide, hp, hl⟩
        · exact ⟨8, 16, by decide, hp, hl⟩
        · exact ⟨8, 17, by decide, hp, hl⟩
        · exact ⟨8, 19, by decide, hp, hl⟩
      · obtain ⟨hp, hl⟩ := h
        rcases hl with ((hl | hl) | hl) | hl
        · exact ⟨1, 13, by decide, hp, hl⟩
        · exact ⟨1, 19, by decide, hp, hl⟩
        · exact ⟨1, 23, by decide, hp, hl⟩
        · exact ⟨1, 24, by decide, hp, hl⟩
      · obtain ⟨hp, hl⟩ := h
        rcases hl with ((hl | hl) | hl) | hl
        · exact ⟨7, 13, by decide, hp, hl⟩
        · exact ⟨7, 17, by decide, hp, hl⟩
        · exact ⟨7, 18, by decide, hp, hl⟩
        · exact ⟨7, 20, by decide, hp, hl⟩
      · obtain ⟨hp, hl⟩ := h
        rcases hl with ((hl | hl) | hl) | hl
        · exact ⟨11, 13, by decide, hp, hl⟩
        · exact ⟨11, 14, by decide, hp, hl⟩
        · exact ⟨11, 16, by decide, hp, hl⟩
        · exact ⟨11, 22, by decide, hp, hl⟩
    · rintro ⟨i, j, hinc, xi, xj⟩
      by_cases hm : i.val ∈ ([0, 1, 2, 7, 8, 11] : List ℕ)
      · rcases key i j hinc hm with ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩
        all_goals simp [xi, xj]
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hc.mpr ⟨i, j, hinc.1, hinc.2.1, hinc.2.2, hm, xi, xj⟩))))))
  refine ⟨main, fun hf => ?_⟩
  have hf0 : C0.eval (List.ofFn x) = false := by
    have hf' := hf
    rw [hev] at hf'
    simp only [Bool.or_eq_false_iff] at hf'
    exact hf'.1.1.1.1.1.1
  rw [hr, ha hf0]
  cases x 12 <;> cases x 13 <;> cases x 15 <;> cases x 21 <;> rfl
