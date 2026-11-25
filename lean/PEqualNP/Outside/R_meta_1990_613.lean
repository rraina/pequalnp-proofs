import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1990_613
    (compile : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      ∃ T : List (Set (Fin n → Bool)),
        T.length ≤ {j : ℕ | ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ∧
        (∀ i : Fin T.length, ∃ A B : Set (Set (Fin n → Bool)),
          (∀ a ∈ A, a ∈ T.take i.val ∨ a = Set.univ ∨ ∃ v : Fin n, a = {x | x v = true}) ∧
          (∀ b ∈ B, b ∈ T.take i.val ∨ b = Set.univ ∨ ∃ v : Fin n, b = {x | x v = true}) ∧
          T.get i = ⋃₀ A ∩ ⋃₀ B) ∧
        ∀ w : ℕ, ∃ A : Set (Set (Fin n → Bool)),
          (∀ a ∈ A, a ∈ T ∨ a = Set.univ ∨ ∃ v : Fin n, a = {x | x v = true}) ∧
          {x : Fin n → Bool | (C.wires (List.ofFn x)).getD w false = true} = ⋃₀ A)
    (andCore : ∀ T : List (Set (Fin 26 → Bool)),
      (∀ i : Fin T.length, ∃ A B : Set (Set (Fin 26 → Bool)),
          (∀ a ∈ A, a ∈ T.take i.val ∨ a = Set.univ ∨ ∃ v : Fin 26, a = {x | x v = true}) ∧
          (∀ b ∈ B, b ∈ T.take i.val ∨ b = Set.univ ∨ ∃ v : Fin 26, b = {x | x v = true}) ∧
          T.get i = ⋃₀ A ∩ ⋃₀ B) →
      ∀ O : Set (Set (Fin 26 → Bool)),
        (∀ a ∈ O, a ∈ T ∨ a = Set.univ ∨ ∃ v : Fin 26, a = {x | x v = true}) →
        (let inc : Fin 13 → Fin 13 → Prop := fun p l => (p.val + l.val) % 13 ∈ [0, 1, 3, 9]
         let vec : Finset (Fin 13) → Finset (Fin 13) → Fin 26 → Bool := fun s t i =>
           if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
         let off : Finset (Fin 13) → Finset (Fin 13) := fun s => {l : Fin 13 | ∀ p ∈ s, ¬ inc p l}
         (∀ p l : Fin 13, inc p l → vec {p} {l} ∈ ⋃₀ O) ∧
           ∀ s : Finset (Fin 13), s.card ≤ 3 → vec s (off s) ∉ ⋃₀ O ∧ vec (off s) s ∉ ⋃₀ O) →
        13 ≤ T.length)
    (orSide : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (50 : ℕ) ≤ {j : ℕ | ∃ g, x1.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C x2 hM hlen hP
  have hor := orSide C x2 hM hlen hP
  dsimp only at hP
  obtain ⟨hE, hN⟩ := hP
  obtain ⟨T, hTlen, hprog, hw⟩ := compile 26 C hM
  choose Aw hAw hAeq using hw
  have key : ∀ x : Fin 26 → Bool,
      (PEqualNP.CircuitLowerBounds.GateOp.or.eval (x2.map fun k =>
        (C.wires (List.ofFn x)).getD k false) = true ↔
        x ∈ ⋃₀ {a | ∃ w ∈ x2, a ∈ Aw w}) := by
    intro x
    have e : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id :=
      fun l => rfl
    rw [e]
    simp only [List.any_eq_true, List.mem_map, Set.mem_sUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨b, ⟨k, hk, rfl⟩, hb⟩
      have hx : x ∈ {x : Fin 26 → Bool | (C.wires (List.ofFn x)).getD k false = true} := hb
      rw [hAeq k] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      exact ⟨a, ⟨k, hk, ha⟩, hxa⟩
    · rintro ⟨a, ⟨k, hk, ha⟩, hxa⟩
      have hx : x ∈ {x : Fin 26 → Bool | (C.wires (List.ofFn x)).getD k false = true} := by
        rw [hAeq k]
        exact ⟨a, ha, hxa⟩
      exact ⟨_, ⟨k, hk, rfl⟩, hx⟩
  have h13 : 13 ≤ T.length := by
    refine andCore T hprog {a | ∃ w ∈ x2, a ∈ Aw w} ?_ ?_
    · rintro a ⟨w, _, ha⟩
      exact hAw w a ha
    · dsimp only
      refine ⟨fun p l hpl => (key _).1 (hE p l hpl), fun s hs => ⟨?_, ?_⟩⟩
      · intro hmem
        have h1 := (key _).2 hmem
        have h2 := (hN s hs).1
        exact absurd (h2.symm.trans h1) (by decide)
      · intro hmem
        have h1 := (key _).2 hmem
        have h2 := (hN s hs).2
        exact absurd (h2.symm.trans h1) (by decide)
  have hsub : {j : ℕ | ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and} ∪
      {j : ℕ | ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or} ⊆
      (↑(Finset.range C.gates.length) : Set ℕ) := by
    rintro j (⟨g, hg, _⟩ | ⟨g, hg, _⟩)
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact (List.getElem?_eq_some_iff.1 hg).1
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact (List.getElem?_eq_some_iff.1 hg).1
  have hfin : (↑(Finset.range C.gates.length) : Set ℕ).Finite := Finset.finite_toSet _
  have hdisj : Disjoint {j : ℕ | ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and}
      {j : ℕ | ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or} := by
    rw [Set.disjoint_left]
    rintro j ⟨g, hg, hga⟩ ⟨g', hg', hgo⟩
    rw [hg] at hg'
    cases hg'
    rw [hga] at hgo
    cases hgo
  have hcard := Set.ncard_union_eq hdisj (hfin.subset (Set.subset_union_left.trans hsub))
    (hfin.subset (Set.subset_union_right.trans hsub))
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_range] at hle
  have hsize : C.size = C.gates.length := rfl
  omega
