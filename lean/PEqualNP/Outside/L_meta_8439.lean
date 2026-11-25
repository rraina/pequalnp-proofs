import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8439


namespace Live516

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k+1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

end Live516

namespace Live516
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end Live516

namespace Check516

abbrev W := BitVec 320
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 160)).setWidth 160
def cuts (ws : List W) : BitVec 160 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 160) ++ (0 : BitVec 160)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

def advance (k : ℕ) (next : List W → Bool) (a b : W) (rest : List W) : Bool :=
  let ds := ops a b
  let base := cuts rest
  let attempt := fun (kept : List W) (covered : BitVec 160) =>
    if kept.length + 1 ≤ k+1 then
      ds.any (fun z => (covered ||| sep z == -1) && next (z :: kept))
    else false
  attempt rest base || attempt (a :: rest) (sep a ||| base) ||
    attempt (b :: rest) (sep b ||| base) || attempt (a :: b :: rest) (sep a ||| (sep b ||| base))

def search : ℕ → List W → Bool
  | 0, ws => ws == [goal]
  | k+1, ws => ws == [goal] || (pairs ws).any (fun (a,b,rest) => advance k (search k) a b rest)

def rawInputs : List W :=
  [0xc21f8084447e043f010888fc087e047c11f044afc00f8000003e001f0000007c003e003c00f00007,
   0x45f0817c0bc20be102f8178417c20bc42f10bc5901f0007c03c003e000f8078007c003c00f003c18,
   0xbe210f883c847c421f107908f8843c88f223c8723e000f803c007c001f007800f8003c00f003c060,
   0x8421fffc00810843fff8010210851114447ff8400000fffc00000001fff8000000000000003ff80,
   0x3ffff2108000210844212221ffffc000fffd11003ffff0000000000000000000ffffc000fffc0000,
   0x108424211110ffffe8420000ffffffff000222000000000000007fffe0000000ffffffff00000000,
   0x2108484222217fffffffffff42108000888800000000000000007fffffffffff0000000000000000,
   0x3fffffffffffc2109084444284212222000000003fffffffffff8000000000000000000000000000]

def inputs := rawInputs.map canon

end Check516
namespace Check516
variable {α : Type}

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end Check516

namespace Check516
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 160) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (160+i.val)

theorem neg_differs (i : Fin 160) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 320 := by omega
  have hi : 160+i.val < 320 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 160) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 160) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (160+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (160+i.val) := by simpa [differs] using h.2
  have lo : i.val < 320 := by omega
  have hi : 160+i.val < 320 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 160) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬160 + i.val < 160 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 160) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {k : ℕ} {ws : List W} (h : Live516.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := Live516.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 160)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end Check516

namespace Check516

def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

theorem advance_has {k : ℕ} {next : List W → Bool} {a b z : W} {r kept : List W}
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hn : kept.length+1 ≤ k+1) (hc : cuts (z::kept) = -1) (ht : next (z::kept) = true) :
    advance k next a b r = true := by
  have hh : (ops a b).any (fun w => (cuts kept ||| sep w == -1) && next (w :: kept)) := by
    apply List.any_eq_true.mpr
    refine ⟨z, by simpa [basicOps] using hz, ?_⟩
    change sep z ||| cuts kept = -1 at hc
    simp [BitVec.or_comm (cuts kept), hc, ht]
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [advance, hn, ite_true, cuts, List.foldr_cons] at * <;> simp_all

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem search_complete (n : ℕ) (ws : List W) (hn : ws.Nodup)
    (h : Live516.live basicOps goal n ws.toFinset) : search n ws = true := by
  induction n generalizing ws with
  | zero => simp [search, singleton_list hn h]
  | succ k ih =>
    rcases Live516.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [search, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          advance k (search k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live516.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        apply advance_has hop hk _ (cuts_full hl) (ih _ hnd hl)
        have hc := Live516.live_card hl
        rw [List.toFinset_card_of_nodup hnd] at hc
        exact hc
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end Check516

namespace Check516
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 320) (z : W) := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 320) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩


theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]

theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide)


def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 320 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 160) ++ (0 : BitVec 160))) :
    Live516.build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide : ((-1 : BitVec 160) ++ (0 : BitVec 160)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide)
  | cons g gs ih =>
    obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
        bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
      intro k; simpa only [List.foldl_cons,hstep] using he k
    have appendOK (h : canon z = 0 ∨ canon z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old|fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h|h|⟨a,ha,b,hb,hab,hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr h)) he')
    · refine Or.inr ⟨a,ha,b,hb,hab,canon z,hop,fn (insert (canon z) av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact (hw _ hu).imp_right (Finset.mem_insert_of_mem ·)
      · simp_all


def graph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)

def assignment (k : Fin 320) (i : Fin 8) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live516.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 160) := [3, 0, 1, 2, 8, 9, 19, 33]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (160+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := Live516.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 320) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 320) : graph (assignment k) =
    bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 4 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7) =
      ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by decide
  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 320) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    Live516.build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : Live516.build basicOps goal k inputs.toFinset) :
    Live516.live basicOps goal k inputs.toFinset := by
  obtain ⟨S,hsub,hLive⟩ := Live516.compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : Live516.live basicOps goal m inputs.toFinset) :
    Live516.live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem lower_of_check (check : search 11 inputs = false) (s : ℕ)
    (h : HasCircuitSize 8 graph s) : 12 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 11 := by change C.gates.length ≤ s at hsize; omega
  have searched := search_complete 11 inputs (by decide) (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check516
namespace Check516

def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z::kept) = -1) (ht : next (k-kept.length) (z::kept) = true) :
    dispatch extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w,hw,?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [cuts, List.foldr_cons, sep_canon] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2 <;> omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1 <;> ac_rfl⟩, by convert ht using 2 <;> omega⟩

end Check516

namespace Check516

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live516.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases Live516.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live516.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := Live516.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem lower_of_optimized (check : optimized 11 4 inputs = false) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize 8 graph s) : 12 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 11 := by change C.gates.length ≤ s at hsize; omega
  have searched := optimized_complete 11 inputs 4 (by decide) (by decide)
    (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check516

namespace Live516
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def kept (p : α → Option β) (s : Finset α) : Finset β := s.biUnion (fun a => (p a).toFinset)
def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card

theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]

theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]

theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]

theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le

theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem build_mono {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a,hs ha,b,hs hb,hab,z,hz,ih (Finset.insert_subset_insert _ hs) tail⟩

def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w

theorem zeros_step {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : projects p ops ops') {a b z : α} (hz : z ∈ ops a b) (r : Finset α)
    (fresh : z ∉ insert a (insert b r)) :
    zeros p (insert a (insert b r)) ≤ zeros p (insert z r)+1 := by
  have mono := zeros_mono p (Finset.subset_insert z r)
  cases ha : p a with
  | some u =>
    rw [zeros_some ha]
    have h := zeros_le p b r
    omega
  | none =>
    cases hb : p b with
    | some v =>
      have h := zeros_le p a (insert b r)
      rw [zeros_some hb] at h
      omega
    | none =>
      have hzn : p z = none := by
        cases he : p z with
        | none => rfl
        | some v => simpa [ha, hb] using P a b z hz v he
      have hzout : z ∉ r := by intro h; exact fresh (by simp [h])
      rw [zeros_none hzn hzout]
      have u := zeros_le p a (insert b r)
      have v := zeros_le p b r
      omega

theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))

theorem project_live {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) (n : ℕ) (budget : k ≤ n + zeros p s) :
    build ops' g' n (kept p s) := by
  induction k generalizing s n with
  | zero =>
    change s = {g} at h
    have mem : g' ∈ kept p s := by simp [h, kept, hg]
    induction n with
    | zero => exact mem
    | succ n ih => exact Or.inl (ih (by omega))
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact ih skip n (by omega)
    · have dz := zeros_step P hz r hn
      have free (hs : kept p (insert z r) ⊆ kept p (insert a (insert b r))) :
          build ops' g' n (kept p (insert a (insert b r))) :=
        build_mono hs (ih tail n (by omega))
      cases hZ : p z with
      | none =>
        apply free
        simp [kept_insert, hZ]
        exact fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      | some v =>
        rcases P a b z hz v hZ with ha|hb|⟨u,w,hA,hB,hw,hop⟩
        · apply free
          simp [kept_insert, hZ, ha]
        · apply free
          simp [kept_insert, hZ, hb]
        · rw [zeros_some hA, zeros_some hB] at budget
          have dz' := zeros_some hZ r
          have bound := zeros_budget hg P tail
          cases n with
          | zero => omega
          | succ n =>
            have next := ih tail n (by omega)
            have covers : kept p (insert z r) ⊆ insert v (kept p (insert a (insert b r))) := by
              simp [kept_insert,hZ,hA,hB]
              intro x hx
              simp only [Finset.mem_insert] at hx ⊢
              tauto
            exact Or.inr ⟨u, by simp [kept_insert,hA], w, by simp [kept_insert,hB],
                hw, v, hop, build_mono covers next⟩

end Live516

namespace Check516

abbrev Half := BitVec 160
def fill (m : Half) (r : Fin 160) (x : Half) : Half :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)

def crop (m : Half) (r : Fin 160) (x : W) : W :=
  (fill m r ((x >>> 160).setWidth 160)) ++ (fill m r (x.setWidth 160))

theorem fill_bit (m x : Half) (r : Fin 160) {i : ℕ} (hi : i < 160) :
    (fill m r x)[i] = if m[i] then x[i] else x[r.val] := by
  unfold fill
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr, hm]

def pos (m : Half) (r : Fin 160) (i : Nat) :=
  if i < 160 then (if m.getLsbD i then i else r.val)
  else (if m.getLsbD (i-160) then i else 160+r.val)

theorem pos_lt (m : Half) (r : Fin 160) {i : Nat} (hi : i < 320) : pos m r i < 320 := by
  unfold pos; split <;> split <;> omega

theorem fill_lsb (m x : Half) (r : Fin 160) {i : Nat} (hi : i < 160) :
    (fill m r x).getLsbD i = if m.getLsbD i then x.getLsbD i else x.getLsbD r.val := by
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem r.isLt] using fill_bit m x r hi

theorem crop_bit (m : Half) (r : Fin 160) (x : W) (i : ℕ) (hi : i < 320) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_append]
  by_cases h : i < 160
  · rw [if_pos h, if_pos h, fill_lsb _ _ _ h]
    cases e : m.getLsbD i <;> simp only [BitVec.getLsbD_setWidth, h, r.isLt, decide_true,
      Bool.true_and, Bool.false_eq_true, if_false, if_true]
  · have hr : i-160 < 160 := by omega
    rw [if_neg h, if_neg h, fill_lsb _ _ _ hr]
    cases e : m.getLsbD (i-160) <;> simp only [BitVec.getLsbD_setWidth, hr, r.isLt,
      decide_true, Bool.true_and, Bool.false_eq_true, if_false, if_true, BitVec.getLsbD_ushiftRight,
      show 160+(i-160)=i by omega]

theorem crop_and (m : Half) (r : Fin 160) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]

theorem crop_neg (m : Half) (r : Fin 160) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]

def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]

def cropOpt (m : Half) (r : Fin 160) (x : W) := wrap (crop m r x)

theorem crop_canon (m : Half) (r : Fin 160) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl

set_option maxRecDepth 2500 in
theorem crop_goal (m : Half) (r : Fin 160) : cropOpt m r goal = some goal := by
  have g : goal = (BitVec.allOnes 160 ++ (0 : Half)) := by decide
  have eq : crop m r goal = goal := by
    change (fill m r (BitVec.allOnes 160) ++ fill m r 0) = (BitVec.allOnes 160 ++ (0 : Half))
    congr 1
    · apply BitVec.eq_of_getElem_eq
      intro i hi; rw [fill_bit _ _ _ hi]; simp only [BitVec.getElem_allOnes, ite_self]
    · apply BitVec.eq_of_getElem_eq
      intro i hi; rw [fill_bit _ _ _ hi]; simp

  rw [cropOpt, eq]
  decide

set_option maxRecDepth 2500 in
theorem binary_project {x y v : W} (h : wrap (x &&& y) = some v) :
    wrap x = some v ∨ wrap y = some v ∨
    ∃ u w, wrap x = some u ∧ wrap y = some w ∧ u ≠ w ∧ v ∈ basicOps u w := by
  have trivial (t : W) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 320 := by
    rcases sign t with h'|h' <;> rw [ht] at h'
    · exact .inl h'
    · exact .inr h'
  by_cases hx : canon x = 0
  · rcases trivial _ hx with rfl|rfl
    · rw [show (0 : W) &&& y = 0 from BitVec.zero_and] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.allOnes_and] at h; exact .inr (.inl h)
  by_cases hy : canon y = 0
  · rcases trivial _ hy with rfl|rfl
    · rw [show x &&& (0 : W) = 0 from BitVec.and_zero] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.and_allOnes] at h; exact .inl h
  have hn : canon (x &&& y) ≠ 0 := by intro hn; simp [wrap, hn] at h
  have hval : canon (x &&& y) = v := by simpa only [wrap, if_neg hn, Option.some.injEq] using h
  by_cases eq : canon x = canon y
  · rcases same_both eq with same|bad
    · exact .inl (by simp only [wrap, if_neg hx, ← hval, same])
    · exact False.elim (hn bad)
  · exact .inr (.inr ⟨canon x,canon y,by simp only [wrap,if_neg hx],by simp only [wrap,if_neg hy],eq,
        hval ▸ signed_both (sign x) (sign y)⟩)

theorem mask_projects (m : Half) (r : Fin 160) : Live516.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv

end Check516

namespace Check516

def maybeBuild (n : Nat) (av : List W) : Bool :=
  av.sublists.any (fun ws => ws.length ≤ n+1 && cuts ws == -1 &&
    optimized n (n+1-ws.length) ws)

theorem maybeBuild_complete {n : ℕ} {av : List W} (hn : av.Nodup)
    (h : Live516.build basicOps goal n av.toFinset) : maybeBuild n av = true := by
  obtain ⟨s,hs,hr⟩ := Live516.compress h
  let xs := av.filter (fun a => decide (a ∈ s))
  have hsub : xs.Sublist av := List.filter_sublist
  have hnd : xs.Nodup := hn.sublist hsub
  have heq : xs.toFinset = s := by
    ext a
    simp only [List.mem_toFinset, xs, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hs ha),ha⟩⟩
  rw [←heq] at hr
  have bound := Live516.live_card hr
  rw [List.toFinset_card_of_nodup hnd] at bound
  apply List.any_eq_true.mpr
  refine ⟨xs,List.mem_sublists.mpr hsub,?_⟩
  have ok := optimized_complete n xs (n+1-xs.length) hnd (by omega) hr
  simp [bound, cuts_full hr, ok]

def projectedBudget (m : Half) (r : Fin 160) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length

def available (m : Half) (r : Fin 160) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup

theorem available_spec (m : Half) (r : Fin 160) (ws : List W) :
    (available m r ws).toFinset = Live516.kept (cropOpt m r) ws.toFinset := by
  ext y; simp [available, Live516.kept, List.mem_filterMap]

theorem projected_bound (m : Half) (r : Fin 160) (n : Nat) {ws : List W} (hn : ws.Nodup) :
    n ≤ projectedBudget m r n ws + Live516.zeros (cropOpt m r) ws.toFinset := by
  let xs := ws.filter (fun w => (cropOpt m r w).isNone)
  have eq : (xs.toFinset) = ws.toFinset.filter (fun w => cropOpt m r w = none) := by
    ext w; simp [xs]
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist :
    xs.Sublist ws))
  rw [eq] at card
  change (ws.toFinset.filter (fun w => cropOpt m r w = none)).card = xs.length at card
  change n ≤ n-xs.length + (ws.toFinset.filter (fun w => cropOpt m r w = none)).card
  omega

theorem projection_survives (m : Half) (r : Fin 160) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (h : Live516.live basicOps goal k ws.toFinset) :
    maybeBuild (projectedBudget m r k ws) (available m r ws) = true := by
  have hbuild := Live516.project_live (crop_goal m r) (mask_projects m r) h _ (projected_bound m r k hn)
  rw [← available_spec] at hbuild
  exact maybeBuild_complete (List.nodup_dedup _) hbuild

end Check516

namespace Check516

abbrev Claim := Nat × List W
abbrev Hint := Half × Fin 160 × Nat

def goodClaim (c : Claim) : Bool := decide c.2.Nodup && !(maybeBuild c.1 c.2)

def usable (c : Claim) (m : Half) (r : Fin 160) (n : Nat) (ws : List W) : Bool :=
  projectedBudget m r n ws ≤ c.1 &&
  ws.all (fun w => match cropOpt m r w with | none => true | some y => c.2.contains y)

theorem unusable (c : Claim) (m : Half) (r : Fin 160) {n : Nat} {ws : List W}
    (hn : ws.Nodup) (live : Live516.live basicOps goal n ws.toFinset) (hc : goodClaim c) :
    usable c m r n ws = false := by
  apply Bool.eq_false_iff.mpr
  intro u
  simp only [goodClaim, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  simp only [usable, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at u
  have budget := projected_bound m r n hn
  have bound : n ≤ c.1 + Live516.zeros (cropOpt m r) ws.toFinset := by omega
  have build := Live516.project_live (crop_goal m r) (mask_projects m r) live _ bound
  have sub : Live516.kept (cropOpt m r) ws.toFinset ⊆ c.2.toFinset := by
    intro y hy
    obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp hy
    have hy' : cropOpt m r w = some y := by simpa using hv
    have hu := u.2 w (List.mem_toFinset.mp hw)
    simpa [hy'] using hu
  have ok := maybeBuild_complete hc.1 (Live516.build_mono sub build)
  exact Bool.noConfusion (hc.2.symm.trans ok)

end Check516

namespace Check516

abbrev G3 := W × W × W

def NB (e : Nat) (X : Finset W) : Prop := ∀ n, n < e → ¬ Live516.build basicOps goal n X

def GoodC (c : Claim) : Prop := ¬ Live516.build basicOps goal c.1 c.2.toFinset

theorem build_le {k n : ℕ} {X : Finset W} (h : Live516.build basicOps goal k X) (le : k ≤ n) :
    Live516.build basicOps goal n X := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem kept_mono (p : W → Option W) {s t : Finset W} (h : s ⊆ t) :
    Live516.kept p s ⊆ Live516.kept p t := by
  intro y hy
  obtain ⟨w, hw, hv⟩ := Finset.mem_biUnion.mp hy
  exact Finset.mem_biUnion.mpr ⟨w, h hw, hv⟩

theorem kept_mem {p : W → Option W} {s : Finset W} {a v : W} (ha : a ∈ s) (hp : p a = some v) :
    v ∈ Live516.kept p s :=
  Finset.mem_biUnion.mpr ⟨a, ha, by simp [hp]⟩

def isC (MM w : W) : Bool := (w &&& MM == 0) || (w &&& MM == MM)

def elim (MM : W) (g : G3) : Bool :=
  (g.1 &&& MM == 0) || (g.1 &&& MM == MM) || (g.1 &&& MM == g.2.1 &&& MM) ||
    (g.1 &&& MM == (~~~g.2.1) &&& MM) || (g.1 &&& MM == g.2.2 &&& MM) ||
    (g.1 &&& MM == (~~~g.2.2) &&& MM)

def zcount (MM : W) (l : List W) : Nat := (l.filter (isC MM)).length

def cnt (MM : W) (h : List G3) : Nat := (h.filter (fun g => !(elim MM g))).length

theorem crop_masked {m : Half} {r : Fin 160} {MM : W} (hM : crop m r MM = BitVec.allOnes 320)
    (x : W) : crop m r (x &&& MM) = crop m r x := by
  rw [crop_and, hM, BitVec.and_allOnes]

theorem crop_zero (m : Half) (r : Fin 160) : crop m r 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [crop_bit _ _ _ _ hi]
  simp

theorem wrap_zero : wrap (0 : W) = none := by decide

theorem wrap_ones : wrap (BitVec.allOnes 320 : W) = none := by decide

theorem crop_of_eq {m : Half} {r : Fin 160} {MM : W} (hM : crop m r MM = BitVec.allOnes 320)
    {x y : W} (h : x &&& MM = y &&& MM) : crop m r x = crop m r y := by
  rw [← crop_masked hM x, ← crop_masked hM y, h]

theorem isC_none {m : Half} {r : Fin 160} {MM : W} (hM : crop m r MM = BitVec.allOnes 320)
    {w : W} (h : isC MM w = true) : cropOpt m r w = none := by
  simp only [isC, Bool.or_eq_true, beq_iff_eq] at h
  unfold cropOpt
  rcases h with h | h
  · have e : crop m r w = 0 := by
      rw [← crop_masked hM w, h, crop_zero]
    rw [e]; exact wrap_zero
  · have e : crop m r w = BitVec.allOnes 320 := by
      rw [← crop_masked hM w, h, hM]
    rw [e]; exact wrap_ones

theorem elim_true {m : Half} {r : Fin 160} {MM : W} (hM : crop m r MM = BitVec.allOnes 320)
    {z a b : W} (h : elim MM (z, a, b) = true) :
    cropOpt m r z = none ∨ cropOpt m r z = cropOpt m r a ∨ cropOpt m r z = cropOpt m r b := by
  simp only [elim, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact .inl (isC_none hM (by simp [isC, h]))
  · exact .inl (isC_none hM (by simp [isC, h]))
  · exact .inr (.inl (by unfold cropOpt; rw [crop_of_eq hM h]))
  · exact .inr (.inl (by unfold cropOpt; rw [crop_of_eq hM h, crop_neg, wrap_neg]))
  · exact .inr (.inr (by unfold cropOpt; rw [crop_of_eq hM h]))
  · exact .inr (.inr (by unfold cropOpt; rw [crop_of_eq hM h, crop_neg, wrap_neg]))

def availH (A0 : Finset W) : List G3 → Finset W
  | [] => A0
  | g :: h => insert g.1 (availH A0 h)

def validH (A0 : Finset W) : List G3 → Prop
  | [] => True
  | g :: h => validH A0 h ∧ g.2.1 ∈ availH A0 h ∧ g.2.2 ∈ availH A0 h ∧ g.1 ∈ basicOps g.2.1 g.2.2

theorem cnt_cons (MM : W) (g : G3) (h : List G3) :
    cnt MM (g :: h) = cnt MM h + (if elim MM g = true then 0 else 1) := by
  unfold cnt
  rw [List.filter_cons]
  cases elim MM g <;> simp

theorem hist_nb (m : Half) (r : Fin 160) (MM : W) (hM : crop m r MM = BitVec.allOnes 320)
    (A0 : Finset W) (e : Nat) (h0 : NB e (Live516.kept (cropOpt m r) A0)) :
    ∀ hist : List G3, validH A0 hist →
      NB (e - cnt MM hist) (Live516.kept (cropOpt m r) (availH A0 hist)) := by
  intro hist
  induction hist with
  | nil =>
    intro _
    simpa [cnt, availH] using h0
  | cons g h ih =>
    intro hv
    obtain ⟨vh, ha, hb, hz⟩ := hv
    obtain ⟨z, a, b⟩ := g
    have ihh := ih vh
    intro n hn hbuild
    change Live516.build basicOps goal n
      (Live516.kept (cropOpt m r) (insert z (availH A0 h))) at hbuild
    rw [Live516.kept_insert] at hbuild
    rw [cnt_cons] at hn
    have same (hb' : Live516.build basicOps goal n (Live516.kept (cropOpt m r) (availH A0 h))) :
        False := ihh n (by omega) hb'
    cases hZ : cropOpt m r z with
    | none =>
      rw [hZ] at hbuild
      exact same (by simpa using hbuild)
    | some v =>
      rw [hZ] at hbuild
      by_cases hvk : v ∈ Live516.kept (cropOpt m r) (availH A0 h)
      · apply same
        have e2 : (some v).toFinset ∪ Live516.kept (cropOpt m r) (availH A0 h)
            = Live516.kept (cropOpt m r) (availH A0 h) := by
          ext y; simp only [Option.toFinset_some, Finset.mem_union, Finset.mem_singleton]
          constructor
          · rintro (rfl | hy)
            · exact hvk
            · exact hy
          · exact fun hy => .inr hy
        rwa [e2] at hbuild
      · rcases mask_projects m r a b z hz v hZ with h1 | h1 | ⟨u, w, hA, hB, hne, hop⟩
        · exact hvk (kept_mem ha h1)
        · exact hvk (kept_mem hb h1)
        · have hel : elim MM (z, a, b) = false := by
            by_contra hc
            have ht : elim MM (z, a, b) = true := by simpa using hc
            rcases elim_true hM ht with h2 | h2 | h2
            · rw [hZ] at h2; cases h2
            · rw [hZ] at h2; exact hvk (kept_mem ha h2.symm)
            · rw [hZ] at h2; exact hvk (kept_mem hb h2.symm)
          rw [hel] at hn
          have e2 : (some v).toFinset ∪ Live516.kept (cropOpt m r) (availH A0 h)
              = insert v (Live516.kept (cropOpt m r) (availH A0 h)) := by
            ext y; simp only [Option.toFinset_some, Finset.mem_union, Finset.mem_singleton,
              Finset.mem_insert]
          rw [e2] at hbuild
          exact ihh (n + 1) (by simp at hn; omega)
            (Or.inr ⟨u, kept_mem ha hA, w, kept_mem hb hB, hne, v, hop, hbuild⟩)

theorem zcount_le {m : Half} {r : Fin 160} {MM : W} (hM : crop m r MM = BitVec.allOnes 320)
    {l : List W} (hn : l.Nodup) :
    zcount MM l ≤ Live516.zeros (cropOpt m r) l.toFinset := by
  let xs := l.filter (isC MM)
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist : xs.Sublist l))
  have sub : xs.toFinset ⊆ l.toFinset.filter (fun w => cropOpt m r w = none) := by
    intro w hw
    have hw' := List.mem_filter.mp (List.mem_toFinset.mp hw)
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw'.1, isC_none hM hw'.2⟩
  have le := Finset.card_le_card sub
  have fin : xs.length ≤ (l.toFinset.filter (fun w => cropOpt m r w = none)).card := card ▸ le
  exact fin

theorem prune_sound (m : Half) (r : Fin 160) (MM : W) (e : Nat)
    (hM : crop m r MM = BitVec.allOnes 320) {k : ℕ} {l : List W} (hn : l.Nodup)
    {A : Finset W} (hsub : l.toFinset ⊆ A) (hnb : NB e (Live516.kept (cropOpt m r) A))
    (hlt : k - zcount MM l < e) : ¬ Live516.live basicOps goal k l.toFinset := by
  intro hl
  have hz := zcount_le hM hn
  have hb := Live516.project_live (crop_goal m r) (mask_projects m r) hl (k - zcount MM l)
    (by omega)
  exact hnb _ hlt (Live516.build_mono (kept_mono _ hsub) hb)

abbrev RE := Half × Fin 160 × Nat
abbrev RR := Half × Fin 160 × W × Nat

def resolve (cl : List Claim) (av : List W) (x : RE) : RR :=
  match cl[x.2.2]? with
  | none => (x.1, x.2.1, x.1 ++ x.1, 0)
  | some c => (x.1, x.2.1, x.1 ++ x.1,
      if (crop x.1 x.2.1 (x.1 ++ x.1) == BitVec.allOnes 320 &&
        (available x.1 x.2.1 av).all c.2.contains) = true then c.1 + 1 else 0)

def RInv (A0 : Finset W) (y : RR) : Prop :=
  NB y.2.2.2 (Live516.kept (cropOpt y.1 y.2.1) A0) ∧
    (y.2.2.2 ≠ 0 → crop y.1 y.2.1 y.2.2.1 = BitVec.allOnes 320)

theorem resolve_inv (cl : List Claim) (hcl : ∀ c ∈ cl, GoodC c) (av : List W) (x : RE) :
    RInv av.toFinset (resolve cl av x) := by
  unfold resolve
  cases hc : cl[x.2.2]? with
  | none => exact ⟨fun n hn => absurd hn (Nat.not_lt_zero n), fun h => absurd rfl h⟩
  | some c =>
    dsimp only
    split_ifs with hcond
    · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcond
      refine ⟨?_, fun _ => hcond.1⟩
      intro n hn hb
      change n < c.1 + 1 at hn
      have sub : Live516.kept (cropOpt x.1 x.2.1) av.toFinset ⊆ c.2.toFinset := by
        rw [← available_spec]
        intro y hy
        have := hcond.2 y (List.mem_toFinset.mp hy)
        exact List.mem_toFinset.mpr (by simpa using this)
      exact hcl c (List.mem_of_getElem? hc) (Live516.build_mono sub (build_le hb (by omega)))
    · exact ⟨fun n hn => absurd hn (Nat.not_lt_zero n), fun h => absurd rfl h⟩

abbrev St := List W × List G3

def stepE (s : St) (code : Nat) : Option St :=
  if 4096 ≤ code then some (s.1.eraseIdx (code - 4096), s.2) else
  match s.1[code / 256]?, s.1[(code / 16) % 16]? with
  | some a, some b =>
    match (ops a b)[(code / 4) % 4]? with
    | some z => some (z :: ((if code % 2 = 1 then [a] else []) ++
        ((if (code / 2) % 2 = 1 then [b] else []) ++ (s.1.erase a).erase b)), (z, a, b) :: s.2)
    | none => none
  | _, _ => none

def execE : St → List Nat → Option St
  | s, [] => some s
  | s, c :: cs => match stepE s c with
    | some s' => execE s' cs
    | none => none

def SInv (A0 : Finset W) (s : St) : Prop := s.1.toFinset ⊆ availH A0 s.2 ∧ validH A0 s.2

theorem stepE_inv {A0 : Finset W} {s s' : St} {code : Nat} (hs : SInv A0 s)
    (h : stepE s code = some s') : SInv A0 s' := by
  unfold stepE at h
  by_cases hbig : 4096 ≤ code
  · rw [if_pos hbig] at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨fun y hy => hs.1 (List.mem_toFinset.mpr
      (List.mem_of_mem_eraseIdx (List.mem_toFinset.mp hy))), hs.2⟩
  rw [if_neg hbig] at h
  cases ha : s.1[code / 256]? with
  | none => simp [ha] at h
  | some a =>
    cases hb : s.1[(code / 16) % 16]? with
    | none => simp [ha, hb] at h
    | some b =>
      cases hz : (ops a b)[(code / 4) % 4]? with
      | none => simp [ha, hb, hz] at h
      | some z =>
        simp only [ha, hb, hz, Option.some.injEq] at h
        subst h
        have am : a ∈ s.1 := List.mem_of_getElem? ha
        have bm : b ∈ s.1 := List.mem_of_getElem? hb
        have zm : z ∈ basicOps a b := List.mem_toFinset.mpr (List.mem_of_getElem? hz)
        refine ⟨?_, hs.2, hs.1 (List.mem_toFinset.mpr am), hs.1 (List.mem_toFinset.mpr bm), zm⟩
        intro y hy
        change y ∈ insert z (availH A0 s.2)
        simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, List.mem_append] at hy
        rcases hy with rfl | hy | hy | hy
        · exact Finset.mem_insert_self _ _
        · split_ifs at hy
          · simp only [List.mem_singleton] at hy
            subst hy; exact Finset.mem_insert_of_mem (hs.1 (List.mem_toFinset.mpr am))
          · simp at hy
        · split_ifs at hy
          · simp only [List.mem_singleton] at hy
            subst hy; exact Finset.mem_insert_of_mem (hs.1 (List.mem_toFinset.mpr bm))
          · simp at hy
        · exact Finset.mem_insert_of_mem (hs.1 (List.mem_toFinset.mpr
            (List.mem_of_mem_erase (List.mem_of_mem_erase hy))))

theorem execE_inv {A0 : Finset W} : ∀ (cs : List Nat) (s s' : St), SInv A0 s →
    execE s cs = some s' → SInv A0 s' := by
  intro cs
  induction cs with
  | nil => intro s s' hs h; simp only [execE, Option.some.injEq] at h; exact h ▸ hs
  | cons c cs ih =>
    intro s s' hs h
    unfold execE at h
    cases hc : stepE s c with
    | none => simp [hc] at h
    | some t => rw [hc] at h; exact ih t s' (stepE_inv hs hc) h

def seteq (l1 l2 : List W) : Bool := l1.all l2.contains && l2.all l1.contains

theorem seteq_fin {l1 l2 : List W} (h : seteq l1 l2 = true) : l1.toFinset = l2.toFinset := by
  simp only [seteq, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  ext y
  simp only [List.mem_toFinset]
  exact ⟨fun hy => h.1 y hy, fun hy => h.2 y hy⟩

def pruneBy (y : RR) (k : Nat) (l : List W) (h : List G3) : Bool :=
  decide (k - zcount y.2.2.1 l < y.2.2.2 - cnt y.2.2.1 h)

def deadC (R : List RR) (T : List (List W)) (L tidx : List Nat) (hist : List G3) (k : Nat)
    (a b : W) (l : List W) : Bool :=
  match l with
  | [] => false
  | z :: kept =>
    kept.contains z || (k == 0 && (z :: kept) != [goal]) ||
    L.any (fun i => match R[i]? with
      | some y => pruneBy y k (z :: kept) ((z, a, b) :: hist)
      | none => false) ||
    tidx.any (fun t => match T[t]? with
      | some l' => seteq (z :: kept) l'
      | none => false)

def stateOK (R : List RR) (T : List (List W)) (K : Nat) (ws : List W) (hist : List G3)
    (L tidx : List Nat) : Bool :=
  match K with
  | 0 => false
  | k+1 => decide ws.Nodup && (decide (k + 2 < ws.length) ||
     (ws != [goal] && !((pairs ws).any (fun (a,b,r) =>
        dispatch (k + 2 - ws.length) (fun _ l => !(deadC R T L tidx hist k a b l)) a b r))))

theorem deadC_sound {A0 : Finset W} {R : List RR} (hR : ∀ y ∈ R, RInv A0 y)
    {T : List (List W)} {k : ℕ} (hT : ∀ l ∈ T, ¬ Live516.live basicOps goal k l.toFinset)
    {L tidx : List Nat} {hist : List G3} {a b z : W} {kept : List W}
    (hval : validH A0 ((z, a, b) :: hist))
    (hsub : (z :: kept).toFinset ⊆ availH A0 ((z, a, b) :: hist))
    (hnd : (z :: kept).Nodup)
    (hl : Live516.live basicOps goal k (z :: kept).toFinset) :
    deadC R T L tidx hist k a b (z :: kept) = false := by
  by_contra hc
  have ht : deadC R T L tidx hist k a b (z :: kept) = true := by simpa using hc
  simp only [deadC, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at ht
  rcases ht with ((h | h) | ⟨i, _, h⟩) | ⟨t, _, h⟩
  · exact (List.nodup_cons.mp hnd).1 (by simpa using h)
  · obtain ⟨hk, hne⟩ := h
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    have hne' : ¬ (z :: kept) = [goal] := by simpa using hne
    exact hne' (singleton_list hnd hl)
  · cases hy : R[i]? with
    | none => simp [hy] at h
    | some y =>
      rw [hy] at h
      simp only [pruneBy, decide_eq_true_eq] at h
      obtain ⟨hnb, hm⟩ := hR y (List.mem_of_getElem? hy)
      have hM := hm (by omega)
      have nb := hist_nb y.1 y.2.1 y.2.2.1 hM A0 y.2.2.2 hnb _ hval
      exact prune_sound y.1 y.2.1 y.2.2.1 _ hM hnd hsub nb h hl
  · cases hy : T[t]? with
    | none => simp [hy] at h
    | some l' =>
      rw [hy] at h
      have e := seteq_fin h
      rw [e] at hl
      exact hT l' (List.mem_of_getElem? hy) hl

theorem state_sound {A0 : Finset W} {R : List RR} (hR : ∀ y ∈ R, RInv A0 y)
    {T : List (List W)} {k : ℕ} (hT : ∀ l ∈ T, ¬ Live516.live basicOps goal k l.toFinset)
    {ws : List W} {hist : List G3} {L tidx : List Nat}
    (hok : stateOK R T (k+1) ws hist L tidx = true)
    (hsub : ws.toFinset ⊆ availH A0 hist) (hval : validH A0 hist) :
    ¬ Live516.live basicOps goal (k+1) ws.toFinset := by
  intro h
  simp only [stateOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hn, hrest⟩ := hok
  have hcard := Live516.live_card h
  rw [List.toFinset_card_of_nodup hn] at hcard
  rcases hrest with hbig | ⟨hne, hno⟩
  · omega
  · rcases Live516.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · have hne' : ¬ ws = [goal] := by simpa using hne
      exact hne' (singleton_list hn done)
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch (k + 2 - ws.length) (fun _ l => !(deadC R T L tidx hist k a b l)) a b r
            = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live516.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := Live516.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have am : a ∈ ws.toFinset := by rw [hset]; simp
        have bm : b ∈ ws.toFinset := by rw [hset]; simp
        have hv' : validH A0 ((z, a, b) :: hist) := ⟨hval, hsub am, hsub bm, hop⟩
        have hs' : (z :: kept).toFinset ⊆ availH A0 ((z, a, b) :: hist) := by
          intro y hy
          change y ∈ insert z (availH A0 hist)
          simp only [List.toFinset_cons, Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            apply hsub
            rw [hset, ← hfin]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)
        apply dispatch_complete (k := k) (extra := k + 2 - ws.length)
          (fun _ l => !(deadC R T L tidx hist k a b l)) hop hk (by omega) (by omega)
          (cuts_full hl)
        simp only [Bool.not_eq_true']
        exact deadC_sound hR hT hv' hs' hnd hl
      have hany : (pairs ws).any (fun (a,b,r) =>
          dispatch (k + 2 - ws.length) (fun _ l => !(deadC R T L tidx hist k a b l)) a b r)
            = true := by
        simp only [List.any_eq_true]
        rcases hm with direct | swap
        · exact ⟨(a,b,r), direct, go hp hs hz⟩
        · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
      rw [hany] at hno
      simp at hno

abbrev Entry := List Nat × List Nat × List Nat

def wsOf (av : List W) (e : Entry) : List W :=
  match execE (av, []) e.1 with
  | some s => s.1
  | none => []

def levelOK (R : List RR) (av : List W) (K : Nat) (D : List Entry) (T : List (List W)) : Bool :=
  D.all (fun e => match execE (av, []) e.1 with
    | some s => stateOK R T K s.1 s.2 e.2.1 e.2.2
    | none => false)

def chainOK (R : List RR) (av : List W) : Nat → List (List Entry) → Bool
  | _, [] => true
  | K, D :: rest => levelOK R av K D ((rest.headD []).map (wsOf av)) && chainOK R av (K - 1) rest

theorem chain_sound {R : List RR} {av : List W} (hR : ∀ y ∈ R, RInv av.toFinset y) :
    ∀ (levels : List (List Entry)) (K : Nat), chainOK R av K levels = true →
      ∀ e ∈ levels.headD [], ¬ Live516.live basicOps goal K (wsOf av e).toFinset := by
  intro levels
  induction levels with
  | nil => intro K _ e he; simp at he
  | cons D rest ih =>
    intro K hok e he
    simp only [chainOK, Bool.and_eq_true] at hok
    obtain ⟨hlev, hrest⟩ := hok
    simp only [List.headD_cons] at he
    have hE := List.all_eq_true.mp hlev e he
    cases hx : execE (av, []) e.1 with
    | none => simp [hx] at hE
    | some s =>
      rw [hx] at hE
      have hw : wsOf av e = s.1 := by simp [wsOf, hx]
      rw [hw]
      have inv : SInv av.toFinset s := execE_inv e.1 (av, []) s
        ⟨by simp [availH], trivial⟩ hx
      cases K with
      | zero => simp [stateOK] at hE
      | succ k =>
        have hT : ∀ l ∈ (rest.headD []).map (wsOf av),
            ¬ Live516.live basicOps goal k l.toFinset := by
          intro l hl
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hl
          exact ih k (by simpa using hrest) e' he'
        exact state_sound hR hT hE inv.1 inv.2

def claimOK (cl : List Claim) (rs : List RE) (D0 : List Entry) (rest : List (List Entry))
    (c : Claim) : Bool :=
  decide c.2.Nodup &&
    ((c.2.filter (fun a => cuts (c.2.erase a) == -1)).sublists.all (fun J =>
      (D0.map (wsOf c.2)).any (seteq ((c.2.filter (fun a => cuts (c.2.erase a) != -1)) ++ J)))) &&
    chainOK (rs.map (resolve cl c.2)) c.2 c.1 (D0 :: rest)

theorem claim_sound (cl : List Claim) (hcl : ∀ c ∈ cl, GoodC c) (rs : List RE)
    (D0 : List Entry) (rest : List (List Entry)) (c : Claim)
    (h : claimOK cl rs D0 rest c = true) : GoodC c := by
  intro hb
  simp only [claimOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hn, hsubl⟩, hchain⟩ := h
  obtain ⟨s, hs, hlive⟩ := Live516.compress hb
  have hess : ∀ a ∈ c.2, cuts (c.2.erase a) ≠ -1 → a ∈ s := by
    intro a ha' hcut
    by_contra hna
    have hsub : ∀ w ∈ s, w ∈ c.2.erase a := by
      intro w hw
      have hwc := List.mem_toFinset.mp (hs hw)
      exact (List.mem_erase_of_ne (fun e => hna (by rw [← e]; exact hw))).mpr hwc
    apply hcut
    apply BitVec.eq_of_getElem_eq
    intro j hj
    obtain ⟨w, hw, hd⟩ := Live516.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩)
      (ops_differs ⟨j,hj⟩) hlive
    have hbit := (cuts_spec (c.2.erase a) ⟨j,hj⟩).mpr ⟨w, hsub w hw, hd⟩
    change (cuts (c.2.erase a))[j] = (BitVec.allOnes 160)[j]
    rw [BitVec.getElem_allOnes]
    simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
  let ine := c.2.filter (fun a => cuts (c.2.erase a) == -1)
  let ess := c.2.filter (fun a => cuts (c.2.erase a) != -1)
  let J := ine.filter (fun a => decide (a ∈ s))
  have hJ : J ∈ ine.sublists := List.mem_sublists.mpr List.filter_sublist
  have hfin : (ess ++ J).toFinset = s := by
    ext w
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, ess, J, ine,
      List.mem_filter, decide_eq_true_eq, bne_iff_ne, beq_iff_eq]
    constructor
    · rintro (⟨hw, hc⟩ | ⟨_, hw⟩)
      · exact hess w hw hc
      · exact hw
    · intro hw
      have hwc := List.mem_toFinset.mp (hs hw)
      by_cases hc : cuts (c.2.erase w) = -1
      · exact .inr ⟨⟨hwc, hc⟩, hw⟩
      · exact .inl ⟨hwc, hc⟩
  have hfound := hsubl J hJ
  simp only [List.any_eq_true] at hfound
  obtain ⟨l, hl, hse⟩ := hfound
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
  have hR : ∀ y ∈ rs.map (resolve cl c.2), RInv c.2.toFinset y := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact resolve_inv cl hcl c.2 x
  have dead := chain_sound hR _ c.1 hchain e (by simpa using he)
  rw [← seteq_fin hse, hfin] at dead
  exact dead hlive

theorem final_bound (n : Nat) (hc : GoodC (n, inputs)) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize 8 graph s) : n + 1 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ n := by change C.gates.length ≤ s at hsize; omega
  exact hc (build_le (get_build C hg he) hl)


theorem gnil : ∀ c ∈ ([] : List Claim), GoodC c := fun _ h => absurd h List.not_mem_nil
theorem gcons {c : Claim} {l : List Claim} (h : GoodC c) (t : ∀ x ∈ l, GoodC x) :
    ∀ x ∈ c :: l, GoodC x := List.forall_mem_cons.mpr ⟨h, t⟩

def c0 : Claim := (3, available 0x180000003000300000006000600020008000000 27 inputs)
def r0 : List RE := []
def d0 : List Entry := [([],[],[])]
def e0 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g0 : GoodC c0 := claim_sound [] gnil r0 d0 e0 c0 (by decide +kernel)
def c1 : Claim := (3, available 0x600300028000c004000000030000002000 13 inputs)
def r1 : List RE := []
def d1 : List Entry := [([],[],[])]
def e1 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g1 : GoodC c1 := claim_sound [] gnil r1 d1 e1 c1 (by decide +kernel)
def c2 : Claim := (3, available 0x14000500200000000a00600000000000c001000 12 inputs)
def r2 : List RE := []
def d2 : List Entry := [([],[],[])]
def e2 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g2 : GoodC c2 := claim_sound [] gnil r2 d2 e2 c2 (by decide +kernel)
def c3 : Claim := (3, available 0xc0003001000000000000000500030004003000 12 inputs)
def r3 : List RE := []
def d3 : List Entry := [([],[],[])]
def e3 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g3 : GoodC c3 := claim_sound [] gnil r3 d3 e3 c3 (by decide +kernel)
def c4 : Claim := (3, available 0x18000600200030001000c003000 12 inputs)
def r4 : List RE := []
def d4 : List Entry := [([],[],[])]
def e4 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g4 : GoodC c4 := claim_sound [] gnil r4 d4 e4 c4 (by decide +kernel)
def c5 : Claim := (6, available 0x1c000700300038000e00600070003000c003000 12 inputs)
def r5 : List RE := [(0x180000003000300000006000600020008000000,27,0),(0x600300028000c004000000030000002000,13,1),(0x14000500200000000a00600000000000c001000,12,2),(0xc0003001000000000000000500030004003000,12,3),(0x18000600200030001000c003000,12,4)]
def d5 : List Entry := [([],[1,0,2,3,4],[0,1,2,3,4,5,6,7,8,9])]
def e5 : List (List Entry) := [[([23],[1],[]),([39],[0],[]),([55],[0],[0,1]),([71],[0],[2,3]),([303],[1],[4,5]),([319],[1],[]),([335],[1],[6,7]),([575],[2],[8,9]),([591],[2],[]),([847],[3],[])],[([55,56],[],[]),([55,60],[],[]),([71,72],[],[]),([71,76],[],[]),([303,48],[],[]),([303,52],[],[]),([335,80],[],[]),([335,84],[],[]),([575,80],[],[]),([575,84],[],[])]]
set_option maxRecDepth 100000 in
theorem g5 : GoodC c5 := claim_sound [c0,c1,c2,c3,c4] (gcons g0 (gcons g1 (gcons g2 (gcons g3 (gcons g4 gnil))))) r5 d5 e5 c5 (by decide +kernel)
def c6 : Claim := (7, available 0x1e00078038003c000f00700078003800e003810 4 inputs)
def r6 : List RE := [(0x1c000700300038000e00600070003000c003000,12,0)]
def d6 : List Entry := [([],[0],[])]
def e6 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g6 : GoodC c6 := claim_sound [c5] (gcons g5 gnil) r6 d6 e6 c6 (by decide +kernel)
def c7 : Claim := (8, available 0x3de07f7bbb81fbc0fef77703f781fb83ee0fbb50 4 inputs)
def r7 : List RE := [(0x1e00078038003c000f00700078003800e003810,4,0)]
def d7 : List Entry := [([],[0],[])]
def e7 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g7 : GoodC c7 := claim_sound [c6] (gcons g6 gnil) r7 d7 e7 c7 (by decide +kernel)
def c8 : Claim := (3, available 0x600000018000c00000030001800200080000 19 inputs)
def r8 : List RE := []
def d8 : List Entry := [([],[],[])]
def e8 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g8 : GoodC c8 := claim_sound [] gnil r8 d8 e8 c8 (by decide +kernel)
def c9 : Claim := (3, available 0x300018000a00600020000000300000200 9 inputs)
def r9 : List RE := []
def d9 : List Entry := [([],[],[])]
def e9 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g9 : GoodC c9 := claim_sound [] gnil r9 d9 e9 c9 (by decide +kernel)
def c10 : Claim := (3, available 0x5002800100000005000300000000000c0100 8 inputs)
def r10 : List RE := []
def d10 : List Entry := [([],[],[])]
def e10 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g10 : GoodC c10 := claim_sound [] gnil r10 d10 e10 c10 (by decide +kernel)
def c11 : Claim := (3, available 0x300180008000000000000001400300040300 8 inputs)
def r11 : List RE := []
def d11 : List Entry := [([],[],[])]
def e11 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g11 : GoodC c11 := claim_sound [] gnil r11 d11 e11 c11 (by decide +kernel)
def c12 : Claim := (3, available 0x600300010000c001000c0300 8 inputs)
def r12 : List RE := []
def d12 : List Entry := [([],[],[])]
def e12 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g12 : GoodC c12 := claim_sound [] gnil r12 d12 e12 c12 (by decide +kernel)
def c13 : Claim := (6, available 0x700380018000e00700030001c003000c0300 8 inputs)
def r13 : List RE := [(0x600000018000c00000030001800200080000,19,0),(0x300018000a00600020000000300000200,9,1),(0x5002800100000005000300000000000c0100,8,2),(0x300180008000000000000001400300040300,8,3),(0x600300010000c001000c0300,8,4)]
def d13 : List Entry := [([],[1,0,2,3,4],[0,1,2,3,4,5,6,7,8,9])]
def e13 : List (List Entry) := [[([23],[1],[]),([39],[0],[]),([55],[0],[0,1]),([71],[0],[2,3]),([303],[1],[4,5]),([319],[1],[]),([335],[1],[6,7]),([575],[2],[8,9]),([591],[2],[]),([847],[3],[])],[([55,56],[],[]),([55,60],[],[]),([71,72],[],[]),([71,76],[],[]),([303,48],[],[]),([303,52],[],[]),([335,80],[],[]),([335,84],[],[]),([575,80],[],[]),([575,84],[],[])]]
set_option maxRecDepth 100000 in
theorem g13 : GoodC c13 := claim_sound [c8,c9,c10,c11,c12] (gcons g8 (gcons g9 (gcons g10 (gcons g11 (gcons g12 gnil))))) r13 d13 e13 c13 (by decide +kernel)
def c14 : Claim := (6, available 0x38007e03b001f000fc076003e001f003c00f0300 8 inputs)
def r14 : List RE := [(0x700380018000e00700030001c003000c0300,8,0)]
def d14 : List Entry := [([4096],[0],[]),([],[0],[])]
def e14 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g14 : GoodC c14 := claim_sound [c13] (gcons g13 gnil) r14 d14 e14 c14 (by decide +kernel)
def c15 : Claim := (6, available 0x1c0707383018380e0e706030701c3030c0c3300 8 inputs)
def r15 : List RE := [(0x700380018000e00700030001c003000c0300,8,0)]
def d15 : List Entry := [([4096],[0],[]),([],[0],[])]
def e15 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g15 : GoodC c15 := claim_sound [c13] (gcons g13 gnil) r15 d15 e15 c15 (by decide +kernel)
def c16 : Claim := (3, available 0x300000003000600000006000c000200080000000 31 inputs)
def r16 : List RE := []
def d16 : List Entry := [([],[],[])]
def e16 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g16 : GoodC c16 := claim_sound [] gnil r16 d16 e16 c16 (by decide +kernel)
def c17 : Claim := (3, available 0xc0030005000180040000000300000020000 17 inputs)
def r17 : List RE := []
def d17 : List Entry := [([],[],[])]
def e17 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g17 : GoodC c17 := claim_sound [] gnil r17 d17 e17 c17 (by decide +kernel)
def c18 : Claim := (3, available 0x28000a00200000001400600000000000c0010000 16 inputs)
def r18 : List RE := []
def d18 : List Entry := [([],[],[])]
def e18 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g18 : GoodC c18 := claim_sound [] gnil r18 d18 e18 c18 (by decide +kernel)
def c19 : Claim := (3, available 0x180006001000000000000000a000300040030000 16 inputs)
def r19 : List RE := []
def d19 : List Entry := [([],[],[])]
def e19 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g19 : GoodC c19 := claim_sound [] gnil r19 d19 e19 c19 (by decide +kernel)
def c20 : Claim := (3, available 0x30000c00200060001000c0030000 16 inputs)
def r20 : List RE := []
def d20 : List Entry := [([],[],[])]
def e20 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g20 : GoodC c20 := claim_sound [] gnil r20 d20 e20 c20 (by decide +kernel)
def c21 : Claim := (6, available 0x38000e00300070001c006000e0003000c0030000 16 inputs)
def r21 : List RE := [(0x300000003000600000006000c000200080000000,31,0),(0xc0030005000180040000000300000020000,17,1),(0x28000a00200000001400600000000000c0010000,16,2),(0x180006001000000000000000a000300040030000,16,3),(0x30000c00200060001000c0030000,16,4)]
def d21 : List Entry := [([],[1,0,2,3,4],[0,1,2,3,4,5,6,7,8,9])]
def e21 : List (List Entry) := [[([23],[1],[]),([39],[0],[]),([55],[0],[0,1]),([71],[0],[2,3]),([303],[1],[4,5]),([319],[1],[]),([335],[1],[6,7]),([575],[2],[8,9]),([591],[2],[]),([847],[3],[])],[([55,56],[],[]),([55,60],[],[]),([71,72],[],[]),([71,76],[],[]),([303,48],[],[]),([303,52],[],[]),([335,80],[],[]),([335,84],[],[]),([575,80],[],[]),([575,84],[],[])]]
set_option maxRecDepth 100000 in
theorem g21 : GoodC c21 := claim_sound [c16,c17,c18,c19,c20] (gcons g16 (gcons g17 (gcons g18 (gcons g19 (gcons g20 gnil))))) r21 d21 e21 c21 (by decide +kernel)
def c22 : Claim := (7, available 0x3c000f00380078001e007000f0003800e0038040 6 inputs)
def r22 : List RE := [(0x38000e00300070001c006000e0003000c0030000,16,0)]
def d22 : List Entry := [([],[0],[])]
def e22 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g22 : GoodC c22 := claim_sound [c21] (gcons g21 gnil) r22 d22 e22 c22 (by decide +kernel)
def c23 : Claim := (3, available 0x300060003001e000c0006003c001a00280080000 19 inputs)
def r23 : List RE := []
def d23 : List Entry := [([4096],[],[]),([],[],[])]
def e23 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g23 : GoodC c23 := claim_sound [] gnil r23 d23 e23 c23 (by decide +kernel)
def c24 : Claim := (5, available 0x35a060003b81eb40c0007703d681aa82aa080050 4 inputs)
def r24 : List RE := [(0x300060003001e000c0006003c001a00280080000,19,0)]
def d24 : List Entry := [([],[0],[])]
def e24 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g24 : GoodC c24 := claim_sound [c23] (gcons g23 gnil) r24 d24 e24 c24 (by decide +kernel)
def c25 : Claim := (3, available 0x180036019000800000000000a001700340070300 8 inputs)
def r25 : List RE := []
def d25 : List Entry := [([4096],[],[]),([],[],[])]
def e25 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g25 : GoodC c25 := claim_sound [] gnil r25 d25 e25 c25 (by decide +kernel)
def c26 : Claim := (5, available 0x1ce037399980800000000000b5817b836607bb50 4 inputs)
def r26 : List RE := [(0x180036019000800000000000a001700340070300,8,0)]
def d26 : List Entry := [([],[0],[])]
def e26 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g26 : GoodC c26 := claim_sound [c25] (gcons g25 gnil) r26 d26 e26 c26 (by decide +kernel)
def c27 : Claim := (3, available 0x30006c0320016000d001c00f0300 8 inputs)
def r27 : List RE := []
def d27 : List Entry := [([4096],[],[]),([],[],[])]
def e27 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g27 : GoodC c27 := claim_sound [] gnil r27 d27 e27 c27 (by decide +kernel)
def c28 : Claim := (5, available 0x39c06e7333017380d981ee0fbb50 4 inputs)
def r28 : List RE := [(0x30006c0320016000d001c00f0300,8,0)]
def d28 : List Entry := [([],[0],[])]
def e28 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g28 : GoodC c28 := claim_sound [c27] (gcons g27 gnil) r28 d28 e28 c28 (by decide +kernel)
def c29 : Claim := (4, available 0xe00000038001c000000700038003000c00004 2 inputs)
def r29 : List RE := []
def d29 : List Entry := [([],[],[])]
def e29 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g29 : GoodC c29 := claim_sound [] gnil r29 d29 e29 c29 (by decide +kernel)
def c30 : Claim := (5, available 0x800f0000003c001e00000078003c003800e00006 1 inputs)
def r30 : List RE := [(0xe00000038001c000000700038003000c00004,2,0)]
def d30 : List Entry := [([],[0],[])]
def e30 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g30 : GoodC c30 := claim_sound [c29] (gcons g29 gnil) r30 d30 e30 c30 (by decide +kernel)
def c31 : Claim := (5, available 0x400e8000003a001d00000074003a003400d00005 0 inputs)
def r31 : List RE := [(0xe00000038001c000000700038003000c00004,2,0)]
def d31 : List Entry := [([],[0],[])]
def e31 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g31 : GoodC c31 := claim_sound [c29] (gcons g29 gnil) r31 d31 e31 c31 (by decide +kernel)
def c32 : Claim := (4, available 0x800d00000034001a000000680034002800a00002 1 inputs)
def r32 : List RE := []
def d32 : List Entry := [([],[],[])]
def e32 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g32 : GoodC c32 := claim_sound [] gnil r32 d32 e32 c32 (by decide +kernel)
def c33 : Claim := (5, available 0xc00d80000036001b0000006c0036002c00b00003 0 inputs)
def r33 : List RE := [(0x800d00000034001a000000680034002800a00002,1,0)]
def d33 : List Entry := [([],[0],[])]
def e33 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g33 : GoodC c33 := claim_sound [c32] (gcons g32 gnil) r33 d33 e33 c33 (by decide +kernel)
def c34 : Claim := (7, available 0xe7003c039801ce00780730039c03300cc0384 2 inputs)
def r34 : List RE := [(0x700380018000e00700030001c003000c0300,8,0)]
def d34 : List Entry := [([],[0],[])]
def e34 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g34 : GoodC c34 := claim_sound [c13] (gcons g13 gnil) r34 d34 e34 c34 (by decide +kernel)
def c35 : Claim := (7, available 0x3a000e80340074001d006800e8003400d0034020 5 inputs)
def r35 : List RE := [(0x38000e00300070001c006000e0003000c0030000,16,0)]
def d35 : List Entry := [([],[0],[])]
def e35 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g35 : GoodC c35 := claim_sound [c21] (gcons g21 gnil) r35 d35 e35 c35 (by decide +kernel)
def c36 : Claim := (5, available 0xb20d60003435e41ac000686bc835a42a90a80022 1 inputs)
def r36 : List RE := [(0x300060003001e000c0006003c001a00280080000,19,0)]
def d36 : List Entry := [([],[0],[])]
def e36 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g36 : GoodC c36 := claim_sound [c23] (gcons g23 gnil) r36 d36 e36 c36 (by decide +kernel)
def c37 : Claim := (3, available 0xc033001d000b80640020000300300020200 9 inputs)
def r37 : List RE := []
def d37 : List Entry := [([4096],[],[]),([],[],[])]
def e37 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g37 : GoodC c37 := claim_sound [] gnil r37 d37 e37 c37 (by decide +kernel)
def c38 : Claim := (4, available 0x340398014a00680520000003300000284 2 inputs)
def r38 : List RE := []
def d38 : List Entry := [([],[],[])]
def e38 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g38 : GoodC c38 := claim_sound [] gnil r38 d38 e38 c38 (by decide +kernel)
def c39 : Claim := (4, available 0xc8034005400190048000000340000024020 5 inputs)
def r39 : List RE := []
def d39 : List Entry := [([],[],[])]
def e39 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g39 : GoodC c39 := claim_sound [] gnil r39 d39 e39 c39 (by decide +kernel)
def c40 : Claim := (4, available 0x80000481541c8000000000000000343b000242a6 1 inputs)
def r40 : List RE := []
def d40 : List Entry := [([],[],[])]
def e40 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g40 : GoodC c40 := claim_sound [] gnil r40 d40 e40 c40 (by decide +kernel)
def c41 : Claim := (4, available 0x5416b906c85a0000000000000000 65 inputs)
def r41 : List RE := []
def d41 : List Entry := [([],[],[])]
def e41 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g41 : GoodC c41 := claim_sound [] gnil r41 d41 e41 c41 (by decide +kernel)
def c42 : Claim := (6, available 0x80000c83743dd416b906c85a0000343b000242a6 1 inputs)
def r42 : List RE := [(0xc033001d000b80640020000300300020200,9,0),(0x340398014a00680520000003300000284,2,1),(0xc8034005400190048000000340000024020,5,2),(0x80000481541c8000000000000000343b000242a6,1,3),(0x5416b906c85a0000000000000000,65,4)]
def d42 : List Entry := [([],[0,1,2,3,4],[])]
def e42 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g42 : GoodC c42 := claim_sound [c37,c38,c39,c40,c41] (gcons g37 (gcons g38 (gcons g39 (gcons g40 (gcons g41 gnil))))) r42 d42 e42 c42 (by decide +kernel)
def c43 : Claim := (3, available 0x28005a02a00100001405600300000000c00d0100 8 inputs)
def r43 : List RE := []
def d43 : List Entry := [([4096],[],[]),([],[],[])]
def e43 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g43 : GoodC c43 := claim_sound [] gnil r43 d43 e43 c43 (by decide +kernel)
def c44 : Claim := (4, available 0xa5002c0290000000580730000000000cc0184 2 inputs)
def r44 : List RE := []
def d44 : List Entry := [([],[],[])]
def e44 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g44 : GoodC c44 := claim_sound [] gnil r44 d44 e44 c44 (by decide +kernel)
def c45 : Claim := (4, available 0x2a000a80240000001500680000000000d0014020 5 inputs)
def r45 : List RE := []
def d45 : List Entry := [([],[],[])]
def e45 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g45 : GoodC c45 := claim_sound [] gnil r45 d45 e45 c45 (by decide +kernel)
def c46 : Claim := (4, available 0x80000000000000000501a83900000000d0ed41a6 1 inputs)
def r46 : List RE := []
def d46 : List Entry := [([],[],[])]
def e46 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g46 : GoodC c46 := claim_sound [] gnil r46 d46 e46 c46 (by decide +kernel)
def c47 : Claim := (4, available 0x2a0b5a82e42d0000000000000000000000000000 112 inputs)
def r47 : List RE := []
def d47 : List Entry := [([],[],[])]
def e47 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g47 : GoodC c47 := claim_sound [] gnil r47 d47 e47 c47 (by decide +kernel)
def c48 : Claim := (6, available 0xaa0b5a82e42d00001505e87b00000000d0ed41a6 1 inputs)
def r48 : List RE := [(0x28005a02a00100001405600300000000c00d0100,8,0),(0xa5002c0290000000580730000000000cc0184,2,1),(0x2a000a80240000001500680000000000d0014020,5,2),(0x80000000000000000501a83900000000d0ed41a6,1,3),(0x2a0b5a82e42d0000000000000000000000000000,112,4)]
def d48 : List Entry := [([],[0,1,2,3,4],[])]
def e48 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g48 : GoodC c48 := claim_sound [c43,c44,c45,c46,c47] (gcons g43 (gcons g44 (gcons g45 (gcons g46 (gcons g47 gnil))))) r48 d48 e48 c48 (by decide +kernel)
def c49 : Claim := (4, available 0x1a0006801400000000000000a800340050034020 5 inputs)
def r49 : List RE := []
def d49 : List Entry := [([],[],[])]
def e49 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g49 : GoodC c49 := claim_sound [] gnil r49 d49 e49 c49 (by decide +kernel)
def c50 : Claim := (3, available 0x80000000000000000000000000000000506541a6 1 inputs)
def r50 : List RE := []
def d50 : List Entry := [([],[],[])]
def e50 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g50 : GoodC c50 := claim_sound [] gnil r50 d50 e50 c50 (by decide +kernel)
def c51 : Claim := (3, available 0x80000000000000000000000000001419000242a6 1 inputs)
def r51 : List RE := []
def d51 : List Entry := [([],[],[])]
def e51 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g51 : GoodC c51 := claim_sound [] gnil r51 d51 e51 c51 (by decide +kernel)
def c52 : Claim := (4, available 0x800000000000000000000000280c5419506743a6 1 inputs)
def r52 : List RE := [(0x80000000000000000000000000001419000242a6,1,0)]
def d52 : List Entry := [([],[0],[])]
def e52 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g52 : GoodC c52 := claim_sound [c51] (gcons g51 gnil) r52 d52 e52 c52 (by decide +kernel)
def c53 : Claim := (4, available 0x1a073681d41c8000000000000000000000000000 111 inputs)
def r53 : List RE := []
def d53 : List Entry := [([],[],[])]
def e53 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g53 : GoodC c53 := claim_sound [] gnil r53 d53 e53 c53 (by decide +kernel)
def c54 : Claim := (6, available 0x9a073681d41c800000000000a82d743b506743a6 1 inputs)
def r54 : List RE := [(0x180036019000800000000000a001700340070300,8,0),(0x300180008000000000000001400300040300,8,1),(0x1a0006801400000000000000a800340050034020,5,2),(0x80000481541c8000000000000000343b000242a6,1,3),(0x80000000000000000000000000000000506541a6,1,4),(0x800000000000000000000000280c5419506743a6,1,5),(0x1a073681d41c8000000000000000000000000000,111,6)]
def d54 : List Entry := [([],[0,3,1,2,5,6,4],[0])]
def e54 : List (List Entry) := [[([565],[],[])]]
set_option maxRecDepth 100000 in
theorem g54 : GoodC c54 := claim_sound [c25,c11,c49,c40,c50,c52,c53] (gcons g25 (gcons g11 (gcons g49 (gcons g40 (gcons g50 (gcons g52 (gcons g53 gnil))))))) r54 d54 e54 c54 (by decide +kernel)
def c55 : Claim := (4, available 0x34000d00280068001400d0034020 5 inputs)
def r55 : List RE := []
def d55 : List Entry := [([],[],[])]
def e55 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g55 : GoodC c55 := claim_sound [] gnil r55 d55 e55 c55 (by decide +kernel)
def c56 : Claim := (4, available 0x340e6d03a8390000000000000000 64 inputs)
def r56 : List RE := []
def d56 : List Entry := [([],[],[])]
def e56 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g56 : GoodC c56 := claim_sound [] gnil r56 d56 e56 c56 (by decide +kernel)
def c57 : Claim := (6, available 0x800000000000340e6d03a839681cd419d0ef43a6 1 inputs)
def r57 : List RE := [(0x30006c0320016000d001c00f0300,8,0),(0x600300010000c001000c0300,8,1),(0x34000d00280068001400d0034020,5,2),(0x80000000000000000000000000001419000242a6,1,3),(0x80000000000000000501a83900000000d0ed41a6,1,4),(0x800000000000000000000000280c5419506743a6,1,5),(0x340e6d03a8390000000000000000,64,6)]
def d57 : List Entry := [([],[0,4,1,2,5,6,3],[0])]
def e57 : List (List Entry) := [[([581],[],[])]]
set_option maxRecDepth 100000 in
theorem g57 : GoodC c57 := claim_sound [c27,c12,c55,c51,c46,c52,c56] (gcons g27 (gcons g12 (gcons g55 (gcons g51 (gcons g46 (gcons g52 (gcons g56 gnil))))))) r57 d57 e57 c57 (by decide +kernel)
def c58 : Claim := (9, available 0xba0f7e83f43df41efd07e87be83df43bd0ef43a6 1 inputs)
def r58 : List RE := [(0x38007e03b001f000fc076003e001f003c00f0300,8,0),(0x700380018000e00700030001c003000c0300,8,1),(0xe7003c039801ce00780730039c03300cc0384,2,2),(0x3a000e80340074001d006800e8003400d0034020,5,3),(0xb20d60003435e41ac000686bc835a42a90a80022,1,4),(0x80000c83743dd416b906c85a0000343b000242a6,1,5),(0x80000481541c8000000000000000343b000242a6,1,6),(0x5416b906c85a0000000000000000,65,7),(0xaa0b5a82e42d00001505e87b00000000d0ed41a6,1,8),(0x80000000000000000501a83900000000d0ed41a6,1,9),(0x2a0b5a82e42d0000000000000000000000000000,112,10),(0x9a073681d41c800000000000a82d743b506743a6,1,11),(0x800000000000000000000000280c5419506743a6,1,12),(0x1a073681d41c8000000000000000000000000000,111,13),(0x800000000000340e6d03a839681cd419d0ef43a6,1,14)]
def d58 : List Entry := [([],[2,0,1,3,5,8,11,14],[0,1,2,3,4,5,6,7,8,9,10,11,12,13])]
def e58 : List (List Entry) := [[([567],[2,5,4,1,3,8,11,7,14],[0,1,2]),([575],[2,5,4,1,8,11,7,14,3],[3,4,5,6,7]),([583],[2,4,8,1,3,5,11,14,10],[8,9,10]),([591],[2,8,4,1,5,11,14,10,3],[11,4,12,13,14]),([599],[2,4,11,1,3,5,7,8,14,13],[15,16,17]),([607],[2,11,4,1,7,8,14,13,3],[18,19,20]),([615],[2,4,14,1,3,5,8,10,11,13],[21,22,23]),([623],[2,14,4,1,5,10,11,13,3],[24,25,26]),([847],[2,8,5,1,11,7,14,10,3],[27,28,29,4,7,14]),([863],[2,11,5,1,6,7,13,3],[]),([879],[2,14,5,1,10,11,7,13,3],[30,31,32,33,2]),([1119],[2,11,8,1,7,14,10,13,3],[34,35,36,37,10]),([1135],[2,14,8,1,9,10,13,3],[]),([1391],[2,14,11,1,12,7,3],[])],[([567,94],[2],[]),([567,126],[2],[0,1]),([567,638],[14],[2,3]),([575,86],[2],[]),([575,94],[2],[]),([575,118],[2],[]),([575,126],[2],[4,5,6,7]),([575,606],[8],[8]),([583,94],[2],[]),([583,110],[2],[9,10]),([583,622],[11],[11,12]),([591,86],[2],[]),([591,102],[2],[]),([591,110],[2],[13,14,15,16]),([591,606],[5],[17]),([599,110],[2],[]),([599,120],[4,14,0],[]),([599,124],[2,3],[]),([607,80],[5,2,3,11,7],[]),([607,84],[2,3],[]),([607,102],[2],[]),([615,94],[2],[]),([615,120],[4,11,0],[]),([615,124],[2,3],[]),([623,86],[2],[]),([623,96],[8,2,3,14,10],[]),([623,100],[2,3],[]),([847,82],[2,8,5,3],[18,19,20,21,22,8,17]),([847,86],[2,3],[]),([847,90],[2,3],[]),([879,82],[2,5,3,10],[]),([879,86],[2,14],[2]),([879,112],[5,11,1,10,14,3],[3]),([879,116],[0,2,3],[]),([1119,82],[2,8,3,7],[]),([1119,86],[2,11],[11]),([1119,112],[8,11,14,1,7,3],[12]),([1119,116],[0,2,3],[])],[([567,126,96],[],[]),([567,126,100],[],[]),([567,638,52],[],[]),([567,638,112],[],[]),([575,126,96],[],[]),([575,126,100],[],[]),([575,126,112],[],[]),([575,126,116],[],[]),([575,606,48],[],[]),([583,110,96],[],[]),([583,110,100],[],[]),([583,622,52],[],[]),([583,622,112],[],[]),([591,110,96],[],[]),([591,110,100],[],[]),([591,110,112],[],[]),([591,110,116],[],[]),([591,606,48],[],[]),([847,82,72],[3],[]),([847,82,104],[],[]),([847,82,108],[],[]),([847,82,120],[],[]),([847,82,124],[],[])]]
set_option maxRecDepth 100000 in
theorem g58 : GoodC c58 := claim_sound [c14,c13,c34,c35,c36,c42,c40,c41,c48,c46,c47,c54,c52,c53,c57] (gcons g14 (gcons g13 (gcons g34 (gcons g35 (gcons g36 (gcons g42 (gcons g40 (gcons g41 (gcons g48 (gcons g46 (gcons g47 (gcons g54 (gcons g52 (gcons g53 (gcons g57 gnil))))))))))))))) r58 d58 e58 c58 (by decide +kernel)
def c59 : Claim := (8, available 0x1f0007c03c003e000f8078007c003c00f003c18 3 inputs)
def r59 : List RE := [(0x1e00078038003c000f00700078003800e003810,4,0)]
def d59 : List Entry := [([],[0],[])]
def e59 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g59 : GoodC c59 := claim_sound [c6] (gcons g6 gnil) r59 d59 e59 c59 (by decide +kernel)
def c60 : Claim := (7, available 0x1d00074034003a000e80680074003400d003408 3 inputs)
def r60 : List RE := [(0x1c000700300038000e00600070003000c003000,12,0)]
def d60 : List Entry := [([],[0],[])]
def e60 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g60 : GoodC c60 := claim_sound [c5] (gcons g5 gnil) r60 d60 e60 c60 (by decide +kernel)
def c61 : Claim := (3, available 0x180600003018300c00006030601820208080000 19 inputs)
def r61 : List RE := []
def d61 : List Entry := [([4096],[],[]),([],[],[])]
def e61 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g61 : GoodC c61 := claim_sound [] gnil r61 d61 e61 c61 (by decide +kernel)
def c62 : Claim := (5, available 0x419ce00003738339c00006e70673826609980009 0 inputs)
def r62 : List RE := [(0x180600003018300c00006030601820208080000,19,0)]
def d62 : List Entry := [([],[0],[])]
def e62 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g62 : GoodC c62 := claim_sound [c61] (gcons g61 gnil) r62 d62 e62 c62 (by decide +kernel)
def c63 : Claim := (3, available 0x6303018280a0c604020000030300002200 9 inputs)
def r63 : List RE := []
def d63 : List Entry := [([4096],[],[]),([],[],[])]
def e63 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g63 : GoodC c63 := claim_sound [] gnil r63 d63 e63 c63 (by decide +kernel)
def c64 : Claim := (4, available 0x64034002a000c804800000034000002408 3 inputs)
def r64 : List RE := []
def d64 : List Entry := [([],[],[])]
def e64 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g64 : GoodC c64 := claim_sound [] gnil r64 d64 e64 c64 (by decide +kernel)
def c65 : Claim := (4, available 0x40000025415a800000000000000003770000268d 0 inputs)
def r65 : List RE := []
def d65 : List Entry := [([],[],[])]
def e65 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g65 : GoodC c65 := claim_sound [] gnil r65 d65 e65 c65 (by decide +kernel)
def c66 : Claim := (4, available 0x2b5a0ce84d60000000000000000 65 inputs)
def r66 : List RE := []
def d66 : List Entry := [([],[],[])]
def e66 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g66 : GoodC c66 := claim_sound [] gnil r66 d66 e66 c66 (by decide +kernel)
def c67 : Claim := (6, available 0x40000067437b82b5a0ce84d6000003770000268d 0 inputs)
def r67 : List RE := [(0x6303018280a0c604020000030300002200,9,0),(0x340398014a00680520000003300000284,2,1),(0x64034002a000c804800000034000002408,3,2),(0x40000025415a800000000000000003770000268d,0,3),(0x2b5a0ce84d60000000000000000,65,4)]
def d67 : List Entry := [([],[0,1,2,3,4],[])]
def e67 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g67 : GoodC c67 := claim_sound [c63,c38,c64,c65,c66] (gcons g63 (gcons g38 (gcons g64 (gcons g65 (gcons g66 gnil))))) r67 d67 e67 c67 (by decide +kernel)
def c68 : Claim := (3, available 0x14050528201000000a50603000000000c0c1100 8 inputs)
def r68 : List RE := []
def d68 : List Entry := [([4096],[],[]),([],[],[])]
def e68 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g68 : GoodC c68 := claim_sound [] gnil r68 d68 e68 c68 (by decide +kernel)
def c69 : Claim := (4, available 0x15000540240000000a80680000000000d001408 3 inputs)
def r69 : List RE := []
def d69 : List Entry := [([],[],[])]
def e69 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g69 : GoodC c69 := claim_sound [] gnil r69 d69 e69 c69 (by decide +kernel)
def c70 : Claim := (4, available 0x4000000000000000002982b5000000000ddc158d 0 inputs)
def r70 : List RE := []
def d70 : List Entry := [([],[],[])]
def e70 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g70 : GoodC c70 := claim_sound [] gnil r70 d70 e70 c70 (by decide +kernel)
def c71 : Claim := (4, available 0x15ad056c26b0000000000000000000000000000 112 inputs)
def r71 : List RE := []
def d71 : List Entry := [([],[],[])]
def e71 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g71 : GoodC c71 := claim_sound [] gnil r71 d71 e71 c71 (by decide +kernel)
def c72 : Claim := (6, available 0x415ad056c26b000000ad86f7000000000ddc158d 0 inputs)
def r72 : List RE := [(0x14050528201000000a50603000000000c0c1100,8,0),(0xa5002c0290000000580730000000000cc0184,2,1),(0x15000540240000000a80680000000000d001408,3,2),(0x4000000000000000002982b5000000000ddc158d,0,3),(0x15ad056c26b0000000000000000000000000000,112,4)]
def d72 : List Entry := [([],[0,1,2,3,4],[])]
def e72 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g72 : GoodC c72 := claim_sound [c68,c44,c69,c70,c71] (gcons g68 (gcons g44 (gcons g69 (gcons g70 (gcons g71 gnil))))) r72 d72 e72 c72 (by decide +kernel)
def c73 : Claim := (3, available 0xc0303181008000000000000501430304043300 8 inputs)
def r73 : List RE := []
def d73 : List Entry := [([4096],[],[]),([],[],[])]
def e73 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g73 : GoodC c73 := claim_sound [] gnil r73 d73 e73 c73 (by decide +kernel)
def c74 : Claim := (4, available 0xd0003401400000000000000540034005003408 3 inputs)
def r74 : List RE := []
def d74 : List Entry := [([],[],[])]
def e74 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g74 : GoodC c74 := claim_sound [] gnil r74 d74 e74 c74 (by decide +kernel)
def c75 : Claim := (3, available 0x400000000000000000000000000000000554158d 0 inputs)
def r75 : List RE := []
def d75 : List Entry := [([],[],[])]
def e75 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g75 : GoodC c75 := claim_sound [] gnil r75 d75 e75 c75 (by decide +kernel)
def c76 : Claim := (3, available 0x400000000000000000000000000001550000268d 0 inputs)
def r76 : List RE := []
def d76 : List Entry := [([],[],[])]
def e76 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g76 : GoodC c76 := claim_sound [] gnil r76 d76 e76 c76 (by decide +kernel)
def c77 : Claim := (4, available 0x400000000000000000000000014a41550554378d 0 inputs)
def r77 : List RE := [(0x400000000000000000000000000001550000268d,0,0)]
def d77 : List Entry := [([],[0],[])]
def e77 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g77 : GoodC c77 := claim_sound [c76] (gcons g76 gnil) r77 d77 e77 c77 (by decide +kernel)
def c78 : Claim := (4, available 0xd6b035c15a8000000000000000000000000000 111 inputs)
def r78 : List RE := []
def d78 : List Entry := [([],[],[])]
def e78 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g78 : GoodC c78 := claim_sound [] gnil r78 d78 e78 c78 (by decide +kernel)
def c79 : Claim := (6, available 0x40d6b035c15a800000000000056b43770554378d 0 inputs)
def r79 : List RE := [(0xc0303181008000000000000501430304043300,8,0),(0x300180008000000000000001400300040300,8,1),(0xd0003401400000000000000540034005003408,3,2),(0x40000025415a800000000000000003770000268d,0,3),(0x400000000000000000000000000000000554158d,0,4),(0x400000000000000000000000014a41550554378d,0,5),(0xd6b035c15a8000000000000000000000000000,111,6)]
def d79 : List Entry := [([],[0,3,1,2,5,6,4],[0])]
def e79 : List (List Entry) := [[([565],[],[])]]
set_option maxRecDepth 100000 in
theorem g79 : GoodC c79 := claim_sound [c73,c11,c74,c65,c75,c77,c78] (gcons g73 (gcons g11 (gcons g74 (gcons g65 (gcons g75 (gcons g77 (gcons g78 gnil))))))) r79 d79 e79 c79 (by decide +kernel)
def c80 : Claim := (3, available 0x180606302010300c1010c0c3300 8 inputs)
def r80 : List RE := []
def d80 : List Entry := [([4096],[],[]),([],[],[])]
def e80 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g80 : GoodC c80 := claim_sound [] gnil r80 d80 e80 c80 (by decide +kernel)
def c81 : Claim := (4, available 0x1a000680280034001400d003408 3 inputs)
def r81 : List RE := []
def d81 : List Entry := [([],[],[])]
def e81 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g81 : GoodC c81 := claim_sound [] gnil r81 d81 e81 c81 (by decide +kernel)
def c82 : Claim := (4, available 0x1ad606b82b50000000000000000 64 inputs)
def r82 : List RE := []
def d82 : List Entry := [([],[],[])]
def e82 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g82 : GoodC c82 := claim_sound [] gnil r82 d82 e82 c82 (by decide +kernel)
def c83 : Claim := (6, available 0x40000000000001ad606b82b5035ac1550ddc378d 0 inputs)
def r83 : List RE := [(0x180606302010300c1010c0c3300,8,0),(0x600300010000c001000c0300,8,1),(0x1a000680280034001400d003408,3,2),(0x400000000000000000000000000001550000268d,0,3),(0x4000000000000000002982b5000000000ddc158d,0,4),(0x400000000000000000000000014a41550554378d,0,5),(0x1ad606b82b50000000000000000,64,6)]
def d83 : List Entry := [([],[0,4,1,2,5,6,3],[0])]
def e83 : List (List Entry) := [[([581],[],[])]]
set_option maxRecDepth 100000 in
theorem g83 : GoodC c83 := claim_sound [c80,c12,c81,c76,c70,c77,c82] (gcons g80 (gcons g12 (gcons g81 (gcons g76 (gcons g70 (gcons g77 (gcons g82 gnil))))))) r83 d83 e83 c83 (by decide +kernel)
def c84 : Claim := (9, available 0x41def077c37b83bde0ef86f7077bc3770ddc378d 0 inputs)
def r84 : List RE := [(0x1c0707383018380e0e706030701c3030c0c3300,8,0),(0x700380018000e00700030001c003000c0300,8,1),(0xe7003c039801ce00780730039c03300cc0384,2,2),(0x1d00074034003a000e80680074003400d003408,3,3),(0x419ce00003738339c00006e70673826609980009,0,4),(0x40000067437b82b5a0ce84d6000003770000268d,0,5),(0x40000025415a800000000000000003770000268d,0,6),(0x2b5a0ce84d60000000000000000,65,7),(0x415ad056c26b000000ad86f7000000000ddc158d,0,8),(0x4000000000000000002982b5000000000ddc158d,0,9),(0x15ad056c26b0000000000000000000000000000,112,10),(0x40d6b035c15a800000000000056b43770554378d,0,11),(0x400000000000000000000000014a41550554378d,0,12),(0xd6b035c15a8000000000000000000000000000,111,13),(0x40000000000001ad606b82b5035ac1550ddc378d,0,14)]
def d84 : List Entry := [([],[2,0,1,3,5,8,11,14],[0,1,2,3,4,5,6,7,8,9,10,11,12,13])]
def e84 : List (List Entry) := [[([567],[2,5,4,1,3,8,11,7,14],[0,1,2]),([575],[2,5,4,1,8,11,7,14,3],[3,4,5,6,7]),([583],[2,4,8,1,3,5,11,14,10],[8,9,10]),([591],[2,8,4,1,5,11,14,10,3],[11,4,12,13,14]),([599],[2,4,11,1,3,5,7,8,14,13],[15,16,17]),([607],[2,11,4,1,7,8,14,13,3],[18,19,20]),([615],[2,4,14,1,3,5,8,10,11,13],[21,22,23]),([623],[2,14,4,1,5,10,11,13,3],[24,25,26]),([847],[2,8,5,1,11,7,14,10,3],[27,28,29,4,7,14]),([863],[2,11,5,1,6,7,13,3],[]),([879],[2,14,5,1,10,11,7,13,3],[30,31,32,33,2]),([1119],[2,11,8,1,7,14,10,13,3],[34,35,36,37,10]),([1135],[2,14,8,1,9,10,13,3],[]),([1391],[2,14,11,1,12,7,3],[])],[([567,94],[2],[]),([567,126],[2],[0,1]),([567,638],[14],[2,3]),([575,86],[2],[]),([575,94],[2],[]),([575,118],[2],[]),([575,126],[2],[4,5,6,7]),([575,606],[8],[8]),([583,94],[2],[]),([583,110],[2],[9,10]),([583,622],[11],[11,12]),([591,86],[2],[]),([591,102],[2],[]),([591,110],[2],[13,14,15,16]),([591,606],[5],[17]),([599,110],[2],[]),([599,120],[4,14,0],[]),([599,124],[2,3],[]),([607,80],[5,2,3,11,7],[]),([607,84],[2,3],[]),([607,102],[2],[]),([615,94],[2],[]),([615,120],[4,11,0],[]),([615,124],[2,3],[]),([623,86],[2],[]),([623,96],[8,2,3,14,10],[]),([623,100],[2,3],[]),([847,82],[2,8,5,3],[18,19,20,21,22,8,17]),([847,86],[2,3],[]),([847,90],[2,3],[]),([879,82],[2,5,3,10],[]),([879,86],[2,14],[2]),([879,112],[5,11,1,10,14,3],[3]),([879,116],[0,2,3],[]),([1119,82],[2,8,3,7],[]),([1119,86],[2,11],[11]),([1119,112],[8,11,14,1,7,3],[12]),([1119,116],[0,2,3],[])],[([567,126,96],[],[]),([567,126,100],[],[]),([567,638,52],[],[]),([567,638,112],[],[]),([575,126,96],[],[]),([575,126,100],[],[]),([575,126,112],[],[]),([575,126,116],[],[]),([575,606,48],[],[]),([583,110,96],[],[]),([583,110,100],[],[]),([583,622,52],[],[]),([583,622,112],[],[]),([591,110,96],[],[]),([591,110,100],[],[]),([591,110,112],[],[]),([591,110,116],[],[]),([591,606,48],[],[]),([847,82,72],[3],[]),([847,82,104],[],[]),([847,82,108],[],[]),([847,82,120],[],[]),([847,82,124],[],[])]]
set_option maxRecDepth 100000 in
theorem g84 : GoodC c84 := claim_sound [c15,c13,c34,c60,c62,c67,c65,c66,c72,c70,c71,c79,c77,c78,c83] (gcons g15 (gcons g13 (gcons g34 (gcons g60 (gcons g62 (gcons g67 (gcons g65 (gcons g66 (gcons g72 (gcons g70 (gcons g71 (gcons g79 (gcons g77 (gcons g78 (gcons g83 gnil))))))))))))))) r84 d84 e84 c84 (by decide +kernel)
def c85 : Claim := (4, available 0x1a000000380034000000700068002800a000010 4 inputs)
def r85 : List RE := []
def d85 : List Entry := [([],[],[])]
def e85 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g85 : GoodC c85 := claim_sound [] gnil r85 d85 e85 c85 (by decide +kernel)
def c86 : Claim := (5, available 0x1b0000003c003600000078006c002c00b000018 3 inputs)
def r86 : List RE := [(0x1a000000380034000000700068002800a000010,4,0)]
def d86 : List Entry := [([],[0],[])]
def e86 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g86 : GoodC c86 := claim_sound [c85] (gcons g85 gnil) r86 d86 e86 c86 (by decide +kernel)
def c87 : Claim := (4, available 0x340000003800680000007000d0002800a0000040 6 inputs)
def r87 : List RE := []
def d87 : List Entry := [([],[],[])]
def e87 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g87 : GoodC c87 := claim_sound [] gnil r87 d87 e87 c87 (by decide +kernel)
def c88 : Claim := (5, available 0x360000003c006c0000007800d8002c00b0000060 5 inputs)
def r88 : List RE := [(0x340000003800680000007000d0002800a0000040,6,0)]
def d88 : List Entry := [([],[0],[])]
def e88 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g88 : GoodC c88 := claim_sound [c87] (gcons g87 gnil) r88 d88 e88 c88 (by decide +kernel)
def c89 : Claim := (3, available 0xc00000000cc6000000000000000000000000007b 0 inputs)
def r89 : List RE := []
def d89 : List Entry := [([4099],[],[]),([],[],[])]
def e89 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g89 : GoodC c89 := claim_sound [] gnil r89 d89 e89 c89 (by decide +kernel)
def c90 : Claim := (3, available 0x198c0000000000000000 66 inputs)
def r90 : List RE := []
def d90 : List Entry := [([],[],[])]
def e90 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g90 : GoodC c90 := claim_sound [] gnil r90 d90 e90 c90 (by decide +kernel)
def c91 : Claim := (4, available 0x5dce0000000000000000 65 inputs)
def r91 : List RE := [(0x198c0000000000000000,66,0)]
def d91 : List Entry := [([],[0],[])]
def e91 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g91 : GoodC c91 := claim_sound [c90] (gcons g90 gnil) r91 d91 e91 c91 (by decide +kernel)
def c92 : Claim := (5, available 0xc00000002ee7000000005dce000000000000007b 0 inputs)
def r92 : List RE := [(0xc00000000cc6000000000000000000000000007b,0,0),(0x5dce0000000000000000,65,1)]
def d92 : List Entry := [([],[0,1],[])]
def e92 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g92 : GoodC c92 := claim_sound [c89,c91] (gcons g89 (gcons g91 gnil)) r92 d92 e92 c92 (by decide +kernel)
def c93 : Claim := (6, available 0xc00000003ff7ce7380005dce00002eee0000007b 0 inputs)
def r93 : List RE := [(0xc00000002ee7000000005dce000000000000007b,0,0)]
def d93 : List Entry := [([],[0],[])]
def e93 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g93 : GoodC c93 := claim_sound [c92] (gcons g92 gnil) r93 d93 e93 c93 (by decide +kernel)
def c94 : Claim := (3, available 0x18c6000000000000 49 inputs)
def r94 : List RE := []
def d94 : List Entry := [([],[],[])]
def e94 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g94 : GoodC c94 := claim_sound [] gnil r94 d94 e94 c94 (by decide +kernel)
def c95 : Claim := (4, available 0x9ce7000000000000 48 inputs)
def r95 : List RE := [(0x18c6000000000000,49,0)]
def d95 : List Entry := [([],[0],[])]
def e95 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g95 : GoodC c95 := claim_sound [c94] (gcons g94 gnil) r95 d95 e95 c95 (by decide +kernel)
def c96 : Claim := (5, available 0xdef7800000000000 47 inputs)
def r96 : List RE := [(0x9ce7000000000000,48,0)]
def d96 : List Entry := [([],[0],[])]
def e96 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g96 : GoodC c96 := claim_sound [c95] (gcons g95 gnil) r96 d96 e96 c96 (by decide +kernel)
def c97 : Claim := (6, available 0x37bde0000000000000000000def78000bbb80000 19 inputs)
def r97 : List RE := [(0xdef7800000000000,47,0)]
def d97 : List Entry := [([],[0],[])]
def e97 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g97 : GoodC c97 := claim_sound [c96] (gcons g96 gnil) r97 d97 e97 c97 (by decide +kernel)
def c98 : Claim := (6, available 0xe739c0002ee7000000007fef00000000bbb8007b 0 inputs)
def r98 : List RE := [(0xc00000002ee7000000005dce000000000000007b,0,0)]
def d98 : List Entry := [([],[0],[])]
def e98 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g98 : GoodC c98 := claim_sound [c92] (gcons g92 gnil) r98 d98 e98 c98 (by decide +kernel)
def c99 : Claim := (6, available 0x6f7bc0000000def7aeee00000000 33 inputs)
def r99 : List RE := [(0xdef7800000000000,47,0)]
def d99 : List Entry := [([],[0],[])]
def e99 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g99 : GoodC c99 := claim_sound [c96] (gcons g96 gnil) r99 d99 e99 c99 (by decide +kernel)
def c100 : Claim := (3, available 0xccc00000000 34 inputs)
def r100 : List RE := []
def d100 : List Entry := [([],[],[])]
def e100 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g100 : GoodC c100 := claim_sound [] gnil r100 d100 e100 c100 (by decide +kernel)
def c101 : Claim := (4, available 0x2eee00000000 33 inputs)
def r101 : List RE := [(0xccc00000000,34,0)]
def d101 : List Entry := [([],[0],[])]
def e101 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g101 : GoodC c101 := claim_sound [c100] (gcons g100 gnil) r101 d101 e101 c101 (by decide +kernel)
def c102 : Claim := (5, available 0xc00000001dd680000000000000002eee0000007b 0 inputs)
def r102 : List RE := [(0xc00000000cc6000000000000000000000000007b,0,0),(0x2eee00000000,33,1)]
def d102 : List Entry := [([],[0,1],[])]
def e102 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g102 : GoodC c102 := claim_sound [c89,c101] (gcons g89 (gcons g101 gnil)) r102 d102 e102 c102 (by decide +kernel)
def c103 : Claim := (5, available 0xd6b5a0001dd68000000000009ce72eee3330007b 0 inputs)
def r103 : List RE := [(0xc00000001dd680000000000000002eee0000007b,0,0)]
def d103 : List Entry := [([4099],[0],[]),([],[0],[])]
def e103 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g103 : GoodC c103 := claim_sound [c102] (gcons g102 gnil) r103 d103 e103 c103 (by decide +kernel)
def c104 : Claim := (4, available 0x4e7380005dce0000000000000000 65 inputs)
def r104 : List RE := [(0x5dce0000000000000000,65,0)]
def d104 : List Entry := [([4099],[0],[]),([],[],[])]
def e104 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g104 : GoodC c104 := claim_sound [c91] (gcons g91 gnil) r104 d104 e104 c104 (by decide +kernel)
def c105 : Claim := (5, available 0x6f7bc0007fef0000000000000000 64 inputs)
def r105 : List RE := [(0x4e7380005dce0000000000000000,65,0)]
def d105 : List Entry := [([4100],[0],[]),([],[0],[])]
def e105 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g105 : GoodC c105 := claim_sound [c104] (gcons g104 gnil) r105 d105 e105 c105 (by decide +kernel)
def c106 : Claim := (8, available 0xf7bde0003ff7ef7bc0007fefdef7aeeebbb8007b 0 inputs)
def r106 : List RE := [(0x35a060003b81eb40c0007703d681aa82aa080050,4,0),(0xc00d80000036001b0000006c0036002c00b00003,0,1),(0xb20d60003435e41ac000686bc835a42a90a80022,1,2),(0x1b0000003c003600000078006c002c00b000018,3,3),(0x419ce00003738339c00006e70673826609980009,0,4),(0x360000003c006c0000007800d8002c00b0000060,5,5),(0xc00000003ff7ce7380005dce00002eee0000007b,0,6),(0x37bde0000000000000000000def78000bbb80000,19,7),(0xe739c0002ee7000000007fef00000000bbb8007b,0,8),(0x6f7bc0000000def7aeee00000000,33,9),(0xd6b5a0001dd68000000000009ce72eee3330007b,0,10),(0x6f7bc0007fef0000000000000000,64,11)]
def d106 : List Entry := [([],[1,0,2,3,4,5,6,7,8,9,10,11],[])]
def e106 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g106 : GoodC c106 := claim_sound [c24,c33,c36,c86,c62,c88,c93,c97,c98,c99,c103,c105] (gcons g24 (gcons g33 (gcons g36 (gcons g86 (gcons g62 (gcons g88 (gcons g93 (gcons g97 (gcons g98 (gcons g99 (gcons g103 (gcons g105 gnil)))))))))))) r106 d106 e106 c106 (by decide +kernel)
def c107 : Claim := (5, available 0xd6b3b81dac0bad6550200003b830002aa50 4 inputs)
def r107 : List RE := [(0xc033001d000b80640020000300300020200,9,0)]
def d107 : List Entry := [([],[0],[])]
def e107 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g107 : GoodC c107 := claim_sound [c37] (gcons g37 gnil) r107 d107 e107 c107 (by decide +kernel)
def c108 : Claim := (4, available 0x68038002c000d005000000038000002810 4 inputs)
def r108 : List RE := []
def d108 : List Entry := [([],[],[])]
def e108 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g108 : GoodC c108 := claim_sound [] gnil r108 d108 e108 c108 (by decide +kernel)
def c109 : Claim := (4, available 0xd00380058001a0050000000380000028040 6 inputs)
def r109 : List RE := []
def d109 : List Entry := [([],[],[])]
def e109 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g109 : GoodC c109 := claim_sound [] gnil r109 d109 e109 c109 (by decide +kernel)
def c110 : Claim := (5, available 0x6c03c002e000d80580000003c000002c18 3 inputs)
def r110 : List RE := [(0x68038002c000d005000000038000002810,4,0)]
def d110 : List Entry := [([],[0],[])]
def e110 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g110 : GoodC c110 := claim_sound [c108] (gcons g108 gnil) r110 d110 e110 c110 (by decide +kernel)
def c111 : Claim := (6, available 0xc00009ce6eef0000139cddde000000000000ccff 0 inputs)
def r111 : List RE := [(0xc00000002ee7000000005dce000000000000007b,0,0)]
def d111 : List Entry := [([],[0],[])]
def e111 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g111 : GoodC c111 := claim_sound [c92] (gcons g92 gnil) r111 d111 e111 c111 (by decide +kernel)
def c112 : Claim := (5, available 0x3fff00000000 32 inputs)
def r112 : List RE := [(0x2eee00000000,33,0)]
def d112 : List Entry := [([],[0],[])]
def e112 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g112 : GoodC c112 := claim_sound [c101] (gcons g101 gnil) r112 d112 e112 c112 (by decide +kernel)
def c113 : Claim := (3, available 0xc00000000000000000000000000000000000007b 0 inputs)
def r113 : List RE := []
def d113 : List Entry := [([],[],[])]
def e113 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g113 : GoodC c113 := claim_sound [] gnil r113 d113 e113 c113 (by decide +kernel)
def c114 : Claim := (4, available 0x1ddd00000000 32 inputs)
def r114 : List RE := [(0xccc00000000,34,0)]
def d114 : List Entry := [([],[0],[])]
def e114 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g114 : GoodC c114 := claim_sound [c100] (gcons g100 gnil) r114 d114 e114 c114 (by decide +kernel)
def c115 : Claim := (6, available 0xc0000000000000000000000000001ddd0002eeff 0 inputs)
def r115 : List RE := [(0x80000000000000000000000000001419000242a6,1,0),(0x400000000000000000000000000001550000268d,0,1),(0xc00000000000000000000000000000000000007b,0,2),(0x1ddd00000000,32,3)]
def d115 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e115 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g115 : GoodC c115 := claim_sound [c51,c76,c113,c114] (gcons g51 (gcons g76 (gcons g113 (gcons g114 gnil)))) r115 d115 e115 c115 (by decide +kernel)
def c116 : Claim := (7, available 0xc00005ad5dde80000000000000003fff0002eeff 0 inputs)
def r116 : List RE := [(0x80000481541c8000000000000000343b000242a6,1,0),(0xc0000000000000000000000000001ddd0002eeff,0,1)]
def d116 : List Entry := [([],[0,1],[])]
def e116 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g116 : GoodC c116 := claim_sound [c40,c115] (gcons g40 (gcons g115 gnil)) r116 d116 e116 c116 (by decide +kernel)
def c117 : Claim := (3, available 0x1406290288180000000000000000 67 inputs)
def r117 : List RE := []
def d117 : List Entry := [([],[],[])]
def e117 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g117 : GoodC c117 := claim_sound [] gnil r117 d117 e117 c117 (by decide +kernel)
def c118 : Claim := (3, available 0xa5204a80940000000000000000 66 inputs)
def r118 : List RE := []
def d118 : List Entry := [([],[],[])]
def e118 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g118 : GoodC c118 := claim_sound [] gnil r118 d118 e118 c118 (by decide +kernel)
def c119 : Claim := (3, available 0xc63000000000000000000000000 96 inputs)
def r119 : List RE := []
def d119 : List Entry := [([],[],[])]
def e119 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g119 : GoodC c119 := claim_sound [] gnil r119 d119 e119 c119 (by decide +kernel)
def c120 : Claim := (4, available 0x1ce7200000000000000000000000 93 inputs)
def r120 : List RE := [(0xc63000000000000000000000000,96,0)]
def d120 : List Entry := [([],[0],[])]
def e120 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g120 : GoodC c120 := claim_sound [c119] (gcons g119 gnil) r120 d120 e120 c120 (by decide +kernel)
def c121 : Claim := (6, available 0x1ce72b5a999c0000000000000000 66 inputs)
def r121 : List RE := [(0x1406290288180000000000000000,67,0),(0xa5204a80940000000000000000,66,1),(0x198c0000000000000000,66,2),(0x1ce7200000000000000000000000,93,3)]
def d121 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e121 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g121 : GoodC c121 := claim_sound [c117,c118,c90,c120] (gcons g117 (gcons g118 (gcons g90 (gcons g120 gnil)))) r121 d121 e121 c121 (by decide +kernel)
def c122 : Claim := (7, available 0x5ef7bbdeddde0000000000000000 65 inputs)
def r122 : List RE := [(0x5416b906c85a0000000000000000,65,0),(0x1ce72b5a999c0000000000000000,66,1)]
def d122 : List Entry := [([],[0,1],[])]
def e122 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g122 : GoodC c122 := claim_sound [c41,c121] (gcons g41 (gcons g121 gnil)) r122 d122 e122 c122 (by decide +kernel)
def c123 : Claim := (3, available 0x80000000000014062902881800001419000242a6 1 inputs)
def r123 : List RE := []
def d123 : List Entry := [([4100],[],[]),([],[],[])]
def e123 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g123 : GoodC c123 := claim_sound [] gnil r123 d123 e123 c123 (by decide +kernel)
def c124 : Claim := (6, available 0xc000000000001ce72b5a999c00001ddd0002eeff 0 inputs)
def r124 : List RE := [(0x80000000000014062902881800001419000242a6,1,0),(0xc0000000000000000000000000001ddd0002eeff,0,1)]
def d124 : List Entry := [([4101],[0,1],[]),([],[1],[])]
def e124 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g124 : GoodC c124 := claim_sound [c123,c115] (gcons g123 (gcons g115 gnil)) r124 d124 e124 c124 (by decide +kernel)
def c125 : Claim := (3, available 0xcc60000000000000000000000000000 113 inputs)
def r125 : List RE := []
def d125 : List Entry := [([],[],[])]
def e125 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g125 : GoodC c125 := claim_sound [] gnil r125 d125 e125 c125 (by decide +kernel)
def c126 : Claim := (4, available 0x2ee70000000000000000000000000000 112 inputs)
def r126 : List RE := [(0xcc60000000000000000000000000000,113,0)]
def d126 : List Entry := [([],[0],[])]
def e126 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g126 : GoodC c126 := claim_sound [c125] (gcons g125 gnil) r126 d126 e126 c126 (by decide +kernel)
def c127 : Claim := (5, available 0x3ff78000000000000000000000000000 111 inputs)
def r127 : List RE := [(0x2ee70000000000000000000000000000,112,0)]
def d127 : List Entry := [([],[0],[])]
def e127 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g127 : GoodC c127 := claim_sound [c126] (gcons g126 gnil) r127 d127 e127 c127 (by decide +kernel)
def c128 : Claim := (6, available 0xdef7fff8000000000000000000000000000 111 inputs)
def r128 : List RE := [(0x3ff78000000000000000000000000000,111,0)]
def d128 : List Entry := [([],[0],[])]
def e128 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g128 : GoodC c128 := claim_sound [c127] (gcons g127 gnil) r128 d128 e128 c128 (by decide +kernel)
def c129 : Claim := (9, available 0xc0000def7fffdef7bbdeddde00003fff0002eeff 0 inputs)
def r129 : List RE := [(0xd6b3b81dac0bad6550200003b830002aa50,4,0),(0x68038002c000d005000000038000002810,4,1),(0xd00380058001a0050000000380000028040,6,2),(0x80000c83743dd416b906c85a0000343b000242a6,1,3),(0x340398014a00680520000003300000284,2,4),(0xc8034005400190048000000340000024020,5,5),(0x6c03c002e000d80580000003c000002c18,3,6),(0x40000067437b82b5a0ce84d6000003770000268d,0,7),(0xc00000003ff7ce7380005dce00002eee0000007b,0,8),(0xc00009ce6eef0000139cddde000000000000ccff,0,9),(0x3fff00000000,32,10),(0xc00005ad5dde80000000000000003fff0002eeff,0,11),(0x5ef7bbdeddde0000000000000000,65,12),(0xc000000000001ce72b5a999c00001ddd0002eeff,0,13),(0xdef7fff8000000000000000000000000000,111,14)]
def d129 : List Entry := [([],[3,7,8,9,10,11,13,14,12],[0,1,2,3,4,5,6,7,8])]
def e129 : List (List Entry) := [[([23],[3,0,6,7,2,8,9,10,11,13,14,5,12],[0,1,2]),([31],[3,0,7,2,8,9,10,11,13,14,12],[3]),([39],[7,0,3,2,5,8,9,10,11,13,14,12],[4,5,6]),([47],[7,0,3,6,8,9,10,11,13,14,12],[7]),([55],[8,0,3,1,7,2,9,10,11,13,14,12],[]),([63],[8,0,3,1,7,2,9,10,11,13,14,12],[]),([303],[3,6,1,8,4,11,12],[]),([319],[3,6,1,7,5,9,10,11,13,14,12],[]),([575],[7,8,2,3,5,9,10,11,13,14,12],[])],[([23,56],[3,6,7,11,12],[]),([23,60],[11,12],[]),([23,78],[3],[]),([31,70],[0],[]),([39,56],[3,0,7,2,11,12],[]),([39,60],[11,12],[]),([39,78],[7],[]),([47,70],[0],[])]]
set_option maxRecDepth 100000 in
theorem g129 : GoodC c129 := claim_sound [c107,c108,c109,c42,c38,c39,c110,c67,c93,c111,c112,c116,c122,c124,c128] (gcons g107 (gcons g108 (gcons g109 (gcons g42 (gcons g38 (gcons g39 (gcons g110 (gcons g67 (gcons g93 (gcons g111 (gcons g112 (gcons g116 (gcons g122 (gcons g124 (gcons g128 gnil))))))))))))))) r129 d129 e129 c129 (by decide +kernel)
def c130 : Claim := (6, available 0xffffc00000000000 46 inputs)
def r130 : List RE := [(0xdef7800000000000,47,0)]
def d130 : List Entry := [([],[0],[])]
def e130 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g130 : GoodC c130 := claim_sound [c96] (gcons g96 gnil) r130 d130 e130 c130 (by decide +kernel)
def c131 : Claim := (3, available 0x631800000000000000000000000000000000000 143 inputs)
def r131 : List RE := []
def d131 : List Entry := [([],[],[])]
def e131 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g131 : GoodC c131 := claim_sound [] gnil r131 d131 e131 c131 (by decide +kernel)
def c132 : Claim := (4, available 0x2739c00000000000000000000000000000000000 142 inputs)
def r132 : List RE := [(0x631800000000000000000000000000000000000,143,0)]
def d132 : List Entry := [([],[0],[])]
def e132 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g132 : GoodC c132 := claim_sound [c131] (gcons g131 gnil) r132 d132 e132 c132 (by decide +kernel)
def c133 : Claim := (5, available 0x37bde00000000000000000000000000000000000 141 inputs)
def r133 : List RE := [(0x2739c00000000000000000000000000000000000,142,0)]
def d133 : List Entry := [([],[0],[])]
def e133 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g133 : GoodC c133 := claim_sound [c132] (gcons g132 gnil) r133 d133 e133 c133 (by decide +kernel)
def c134 : Claim := (6, available 0x3ffff00000000000000000000000000000000000 140 inputs)
def r134 : List RE := [(0x37bde00000000000000000000000000000000000,141,0)]
def d134 : List Entry := [([],[0],[])]
def e134 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g134 : GoodC c134 := claim_sound [c133] (gcons g133 gnil) r134 d134 e134 c134 (by decide +kernel)
def c135 : Claim := (5, available 0x2d605b5aaa81000016b5770300000000ee0d9950 4 inputs)
def r135 : List RE := [(0x28005a02a00100001405600300000000c00d0100,8,0)]
def d135 : List Entry := [([],[0],[])]
def e135 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g135 : GoodC c135 := claim_sound [c43] (gcons g43 gnil) r135 d135 e135 c135 (by decide +kernel)
def c136 : Claim := (4, available 0x16000580280000000b00700000000000e001810 4 inputs)
def r136 : List RE := []
def d136 : List Entry := [([],[],[])]
def e136 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g136 : GoodC c136 := claim_sound [] gnil r136 d136 e136 c136 (by decide +kernel)
def c137 : Claim := (4, available 0x2c000b00280000001600700000000000e0018040 6 inputs)
def r137 : List RE := []
def d137 : List Entry := [([],[],[])]
def e137 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g137 : GoodC c137 := claim_sound [] gnil r137 d137 e137 c137 (by decide +kernel)
def c138 : Claim := (5, available 0x170005c02c0000000b80780000000000f001c18 3 inputs)
def r138 : List RE := [(0x16000580280000000b00700000000000e001810,4,0)]
def d138 : List Entry := [([],[0],[])]
def e138 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g138 : GoodC c138 := claim_sound [c136] (gcons g136 gnil) r138 d138 e138 c138 (by decide +kernel)
def c139 : Claim := (3, available 0x33300000 20 inputs)
def r139 : List RE := []
def d139 : List Entry := [([],[],[])]
def e139 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g139 : GoodC c139 := claim_sound [] gnil r139 d139 e139 c139 (by decide +kernel)
def c140 : Claim := (4, available 0xbbb80000 19 inputs)
def r140 : List RE := [(0x33300000,20,0)]
def d140 : List Entry := [([],[0],[])]
def e140 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g140 : GoodC c140 := claim_sound [c139] (gcons g139 gnil) r140 d140 e140 c140 (by decide +kernel)
def c141 : Claim := (5, available 0xfffc0000 18 inputs)
def r141 : List RE := [(0xbbb80000,19,0)]
def d141 : List Entry := [([],[0],[])]
def e141 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g141 : GoodC c141 := claim_sound [c140] (gcons g140 gnil) r141 d141 e141 c141 (by decide +kernel)
def c142 : Claim := (3, available 0x8a031280c40c00000000000000000000506541a6 1 inputs)
def r142 : List RE := []
def d142 : List Entry := [([4100],[],[]),([],[],[])]
def e142 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g142 : GoodC c142 := claim_sound [] gnil r142 d142 e142 c142 (by decide +kernel)
def c143 : Claim := (4, available 0x77740000 18 inputs)
def r143 : List RE := [(0x33300000,20,0)]
def d143 : List Entry := [([],[0],[])]
def e143 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g143 : GoodC c143 := claim_sound [c139] (gcons g139 gnil) r143 d143 e143 c143 (by decide +kernel)
def c144 : Claim := (6, available 0xc00000000000000000000000000000007775ddff 0 inputs)
def r144 : List RE := [(0x80000000000000000000000000000000506541a6,1,0),(0x400000000000000000000000000000000554158d,0,1),(0xc00000000000000000000000000000000000007b,0,2),(0x77740000,18,3)]
def d144 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e144 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g144 : GoodC c144 := claim_sound [c50,c75,c113,c143] (gcons g50 (gcons g75 (gcons g113 (gcons g143 gnil)))) r144 d144 e144 c144 (by decide +kernel)
def c145 : Claim := (6, available 0xce73939cccce000000000000000000007775ddff 0 inputs)
def r145 : List RE := [(0x8a031280c40c00000000000000000000506541a6,1,0),(0xc00000000000000000000000000000007775ddff,0,1)]
def d145 : List Entry := [([4101],[0,1],[]),([],[1],[])]
def e145 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g145 : GoodC c145 := claim_sound [c142,c144] (gcons g142 (gcons g144 gnil)) r145 d145 e145 c145 (by decide +kernel)
def c146 : Claim := (5, available 0x7fef0000000000000000 64 inputs)
def r146 : List RE := [(0x5dce0000000000000000,65,0)]
def d146 : List Entry := [([],[0],[])]
def e146 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g146 : GoodC c146 := claim_sound [c91] (gcons g91 gnil) r146 d146 e146 c146 (by decide +kernel)
def c147 : Claim := (6, available 0x17bdffff0000000000000000 64 inputs)
def r147 : List RE := [(0x7fef0000000000000000,64,0)]
def d147 : List Entry := [([],[0],[])]
def e147 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g147 : GoodC c147 := claim_sound [c146] (gcons g146 gnil) r147 d147 e147 c147 (by decide +kernel)
def c148 : Claim := (7, available 0xc0000000000000000739bbbd00000000fffdddff 0 inputs)
def r148 : List RE := [(0x80000000000000000501a83900000000d0ed41a6,1,0),(0xc00000000000000000000000000000007775ddff,0,1)]
def d148 : List Entry := [([],[0,1],[])]
def e148 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g148 : GoodC c148 := claim_sound [c46,c144] (gcons g46 (gcons g144 gnil)) r148 d148 e148 c148 (by decide +kernel)
def c149 : Claim := (3, available 0xa031280c40c0000000000000000000000000000 114 inputs)
def r149 : List RE := []
def d149 : List Entry := [([],[],[])]
def e149 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g149 : GoodC c149 := claim_sound [] gnil r149 d149 e149 c149 (by decide +kernel)
def c150 : Claim := (3, available 0x529014c04a0000000000000000000000000000 113 inputs)
def r150 : List RE := []
def d150 : List Entry := [([],[],[])]
def e150 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g150 : GoodC c150 := claim_sound [] gnil r150 d150 e150 c150 (by decide +kernel)
def c151 : Claim := (4, available 0xe73900000000000000000000000000000000000 140 inputs)
def r151 : List RE := [(0x631800000000000000000000000000000000000,143,0)]
def d151 : List Entry := [([],[0],[])]
def e151 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g151 : GoodC c151 := claim_sound [c131] (gcons g131 gnil) r151 d151 e151 c151 (by decide +kernel)
def c152 : Claim := (6, available 0xe73939cccce0000000000000000000000000000 113 inputs)
def r152 : List RE := [(0xa031280c40c0000000000000000000000000000,114,0),(0x529014c04a0000000000000000000000000000,113,1),(0xcc60000000000000000000000000000,113,2),(0xe73900000000000000000000000000000000000,140,3)]
def d152 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e152 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g152 : GoodC c152 := claim_sound [c149,c150,c125,c151] (gcons g149 (gcons g150 (gcons g125 (gcons g151 gnil)))) r152 d152 e152 c152 (by decide +kernel)
def c153 : Claim := (7, available 0x2f7bdbdeeeef0000000000000000000000000000 112 inputs)
def r153 : List RE := [(0x2a0b5a82e42d0000000000000000000000000000,112,0),(0xe73939cccce0000000000000000000000000000,113,1)]
def d153 : List Entry := [([],[0,1],[])]
def e153 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g153 : GoodC c153 := claim_sound [c47,c152] (gcons g47 (gcons g152 gnil)) r153 d153 e153 c153 (by decide +kernel)
def c154 : Claim := (9, available 0xef7bdbdeeeef000017bdffff00000000fffdddff 0 inputs)
def r154 : List RE := [(0x2d605b5aaa81000016b5770300000000ee0d9950,4,0),(0x16000580280000000b00700000000000e001810,4,1),(0x2c000b00280000001600700000000000e0018040,6,2),(0xaa0b5a82e42d00001505e87b00000000d0ed41a6,1,3),(0xa5002c0290000000580730000000000cc0184,2,4),(0x2a000a80240000001500680000000000d0014020,5,5),(0x170005c02c0000000b80780000000000f001c18,3,6),(0x415ad056c26b000000ad86f7000000000ddc158d,0,7),(0xe739c0002ee7000000007fef00000000bbb8007b,0,8),(0xc00009ce6eef0000139cddde000000000000ccff,0,9),(0xfffc0000,18,10),(0xce73939cccce000000000000000000007775ddff,0,11),(0x17bdffff0000000000000000,64,12),(0xc0000000000000000739bbbd00000000fffdddff,0,13),(0x2f7bdbdeeeef0000000000000000000000000000,112,14)]
def d154 : List Entry := [([],[3,7,8,9,10,11,12,13,14],[0,1,2,3,4,5,6,7,8])]
def e154 : List (List Entry) := [[([23],[3,0,6,7,2,8,9,10,11,12,13,5,14],[0,1,2]),([31],[3,0,7,2,8,9,10,11,12,13,14],[3]),([39],[7,0,3,2,5,8,9,10,11,12,13,14],[4,5,6]),([47],[7,0,3,6,8,9,10,11,12,13,14],[7]),([55],[8,0,3,1,7,2,9,10,11,12,13,14],[]),([63],[8,0,3,1,7,2,9,10,11,12,13,14],[]),([303],[3,6,1,8,4,13,14],[]),([319],[3,6,1,7,5,9,10,11,12,13,14],[]),([575],[7,8,2,3,5,9,10,11,12,13,14],[])],[([23,56],[3,6,7,13,14],[]),([23,60],[13,14],[]),([23,78],[3],[]),([31,70],[0],[]),([39,56],[3,0,7,2,13,14],[]),([39,60],[13,14],[]),([39,78],[7],[]),([47,70],[0],[])]]
set_option maxRecDepth 100000 in
theorem g154 : GoodC c154 := claim_sound [c135,c136,c137,c48,c44,c45,c138,c72,c98,c111,c141,c145,c147,c148,c153] (gcons g135 (gcons g136 (gcons g137 (gcons g48 (gcons g44 (gcons g45 (gcons g138 (gcons g72 (gcons g98 (gcons g111 (gcons g141 (gcons g145 (gcons g147 (gcons g148 (gcons g153 gnil))))))))))))))) r154 d154 e154 c154 (by decide +kernel)
def c155 : Claim := (4, available 0x4e73800000000000000000000000 95 inputs)
def r155 : List RE := [(0xc63000000000000000000000000,96,0)]
def d155 : List Entry := [([],[0],[])]
def e155 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g155 : GoodC c155 := claim_sound [c119] (gcons g119 gnil) r155 d155 e155 c155 (by decide +kernel)
def c156 : Claim := (5, available 0x6f7bc00000000000000000000000 94 inputs)
def r156 : List RE := [(0x4e73800000000000000000000000,95,0)]
def d156 : List Entry := [([],[0],[])]
def e156 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g156 : GoodC c156 := claim_sound [c155] (gcons g155 gnil) r156 d156 e156 c156 (by decide +kernel)
def c157 : Claim := (6, available 0x7fffe00000000000000000000000 93 inputs)
def r157 : List RE := [(0x6f7bc00000000000000000000000,94,0)]
def d157 : List Entry := [([],[0],[])]
def e157 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g157 : GoodC c157 := claim_sound [c156] (gcons g156 gnil) r157 d157 e157 c157 (by decide +kernel)
def c158 : Claim := (4, available 0xe0003801800000000000000580038006003810 4 inputs)
def r158 : List RE := []
def d158 : List Entry := [([],[],[])]
def e158 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g158 : GoodC c158 := claim_sound [] gnil r158 d158 e158 c158 (by decide +kernel)
def c159 : Claim := (4, available 0x1c0007001800000000000000b000380060038040 6 inputs)
def r159 : List RE := []
def d159 : List Entry := [([],[],[])]
def e159 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g159 : GoodC c159 := claim_sound [] gnil r159 d159 e159 c159 (by decide +kernel)
def c160 : Claim := (4, available 0x63001c0188000000000000029403300440384 2 inputs)
def r160 : List RE := [(0x300180008000000000000001400300040300,8,0)]
def d160 : List Entry := [([],[0],[])]
def e160 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g160 : GoodC c160 := claim_sound [c11] (gcons g11 gnil) r160 d160 e160 c160 (by decide +kernel)
def c161 : Claim := (5, available 0xf0003c01c000000000000005c003c007003c18 3 inputs)
def r161 : List RE := [(0xe0003801800000000000000580038006003810,4,0)]
def d161 : List Entry := [([],[0],[])]
def e161 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g161 : GoodC c161 := claim_sound [c158] (gcons g158 gnil) r161 d161 e161 c161 (by decide +kernel)
def c162 : Claim := (3, available 0x631800000000000000000000000000033300000 20 inputs)
def r162 : List RE := []
def d162 : List Entry := [([4099],[],[]),([],[],[])]
def e162 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g162 : GoodC c162 := claim_sound [] gnil r162 d162 e162 c162 (by decide +kernel)
def c163 : Claim := (5, available 0x16b5a00000000000000000009ce7000033300000 20 inputs)
def r163 : List RE := [(0x631800000000000000000000000000033300000,20,0),(0x9ce7000000000000,48,1)]
def d163 : List Entry := [([],[0,1],[])]
def e163 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g163 : GoodC c163 := claim_sound [c162,c95] (gcons g162 (gcons g95 gnil)) r163 d163 e163 c163 (by decide +kernel)
def c164 : Claim := (7, available 0xc0000000000000000000000039ce5ddd7777ffff 0 inputs)
def r164 : List RE := [(0x800000000000000000000000280c5419506743a6,1,0),(0xc0000000000000000000000000001ddd0002eeff,0,1)]
def d164 : List Entry := [([],[0,1],[])]
def e164 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g164 : GoodC c164 := claim_sound [c52,c115] (gcons g52 (gcons g115 gnil)) r164 d164 e164 c164 (by decide +kernel)
def c165 : Claim := (7, available 0x1ef7b7bdddde8000000000000000000000000000 111 inputs)
def r165 : List RE := [(0x1a073681d41c8000000000000000000000000000,111,0),(0xe73939cccce0000000000000000000000000000,113,1)]
def d165 : List Entry := [([],[0,1],[])]
def e165 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g165 : GoodC c165 := claim_sound [c53,c152] (gcons g53 (gcons g152 gnil)) r165 d165 e165 c165 (by decide +kernel)
def c166 : Claim := (9, available 0xdef7b7bdddde800000000000bdef7fff7777ffff 0 inputs)
def r166 : List RE := [(0x1ce037399980800000000000b5817b836607bb50,4,0),(0x180036019000800000000000a001700340070300,8,1),(0xe0003801800000000000000580038006003810,4,2),(0x1c0007001800000000000000b000380060038040,6,3),(0x9a073681d41c800000000000a82d743b506743a6,1,4),(0x63001c0188000000000000029403300440384,2,5),(0x1a0006801400000000000000a800340050034020,5,6),(0xf0003c01c000000000000005c003c007003c18,3,7),(0x40d6b035c15a800000000000056b43770554378d,0,8),(0xc00000001dd680000000000000002eee0000007b,0,9),(0x16b5a00000000000000000009ce7000033300000,20,10),(0xc00005ad5dde80000000000000003fff0002eeff,0,11),(0xc00000000000000000000000000000007775ddff,0,12),(0xc0000000000000000000000039ce5ddd7777ffff,0,13),(0x1ef7b7bdddde8000000000000000000000000000,111,14)]
def d166 : List Entry := [([],[4,8,9,11,12,14],[0,1,2,3,4,5,6,7,8,9,10])]
def e166 : List (List Entry) := [[([23],[4,0,7,8,3,9,11,12,6,2,14],[0,1,2,3]),([31],[4,0,8,3,9,11,12,14],[4,5,6]),([39],[8,0,4,2,3,9,11,12,6,14],[7,8,9,10]),([47],[8,0,4,7,9,11,12,14],[11,12,13]),([55],[11,9,0,4,2,8,3,10,12],[]),([63],[11,0,9,4,2,8,3,10,12],[]),([69],[11,4,2,8,3,9,10,12],[]),([303],[4,7,2,9,5,11,13,14,12],[14]),([319],[4,7,2,8,6,11,10,12],[]),([575],[8,3,4,6,11,10,12],[]),([837],[11,9,12,4,8],[15,3,6,10,13,14])],[([23,56],[4,7,8,11,1,13,14,12],[0]),([23,60],[11,1,13,14,12],[1]),([23,78],[4,11,10],[]),([23,1109],[4],[0,1]),([31,70],[0,11,10],[]),([31,84],[0,9,10,12],[]),([31,1109],[9,4],[2]),([39,56],[4,0,11,3,8,13,14,12],[3]),([39,60],[11,2,13,14,12],[4]),([39,78],[8,11,10],[]),([39,1109],[8],[3,4]),([47,70],[0,11,10],[]),([47,84],[0,9,10,12],[]),([47,1109],[9,8],[5]),([303,1109],[4],[]),([837,42],[11,9,12],[])],[([23,56,837],[],[]),([23,60,837],[],[]),([31,1109,40],[],[]),([39,56,837],[],[]),([39,60,837],[],[]),([47,1109,40],[],[])]]
set_option maxRecDepth 100000 in
theorem g166 : GoodC c166 := claim_sound [c26,c25,c158,c159,c54,c160,c49,c161,c79,c102,c163,c116,c144,c164,c165] (gcons g26 (gcons g25 (gcons g158 (gcons g159 (gcons g54 (gcons g160 (gcons g49 (gcons g161 (gcons g79 (gcons g102 (gcons g163 (gcons g116 (gcons g144 (gcons g164 (gcons g165 gnil))))))))))))))) r166 d166 e166 c166 (by decide +kernel)
def c167 : Claim := (7, available 0x3def6f7bbbbd0000000000000000 64 inputs)
def r167 : List RE := [(0x340e6d03a8390000000000000000,64,0),(0x1ce72b5a999c0000000000000000,66,1)]
def d167 : List Entry := [([],[0,1],[])]
def e167 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g167 : GoodC c167 := claim_sound [c56,c121] (gcons g56 (gcons g121 gnil)) r167 d167 e167 c167 (by decide +kernel)
def c168 : Claim := (4, available 0x1c000700300038001800e003810 4 inputs)
def r168 : List RE := []
def d168 : List Entry := [([],[],[])]
def e168 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g168 : GoodC c168 := claim_sound [] gnil r168 d168 e168 c168 (by decide +kernel)
def c169 : Claim := (4, available 0x38000e00300070001800e0038040 6 inputs)
def r169 : List RE := []
def d169 : List Entry := [([],[],[])]
def e169 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g169 : GoodC c169 := claim_sound [] gnil r169 d169 e169 c169 (by decide +kernel)
def c170 : Claim := (4, available 0xc600380310018c01100cc0384 2 inputs)
def r170 : List RE := [(0x600300010000c001000c0300,8,0)]
def d170 : List Entry := [([],[0],[])]
def e170 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g170 : GoodC c170 := claim_sound [c12] (gcons g12 gnil) r170 d170 e170 c170 (by decide +kernel)
def c171 : Claim := (5, available 0x1e00078038003c001c00f003c18 3 inputs)
def r171 : List RE := [(0x1c000700300038001800e003810,4,0)]
def d171 : List Entry := [([],[0],[])]
def e171 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g171 : GoodC c171 := claim_sound [c168] (gcons g168 gnil) r171 d171 e171 c171 (by decide +kernel)
def c172 : Claim := (3, available 0xc0000000000000000000198c000000000000007b 0 inputs)
def r172 : List RE := []
def d172 : List Entry := [([4099],[],[]),([],[],[])]
def e172 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g172 : GoodC c172 := claim_sound [] gnil r172 d172 e172 c172 (by decide +kernel)
def c173 : Claim := (5, available 0xc00000000000000000003bad00000000bbb8007b 0 inputs)
def r173 : List RE := [(0xc0000000000000000000198c000000000000007b,0,0),(0xbbb80000,19,1)]
def d173 : List Entry := [([],[0,1],[])]
def e173 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g173 : GoodC c173 := claim_sound [c172,c140] (gcons g172 (gcons g140 gnil)) r173 d173 e173 c173 (by decide +kernel)
def c174 : Claim := (3, available 0xc630000000000000ccc00000000 34 inputs)
def r174 : List RE := []
def d174 : List Entry := [([4099],[],[]),([],[],[])]
def e174 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g174 : GoodC c174 := claim_sound [] gnil r174 d174 e174 c174 (by decide +kernel)
def c175 : Claim := (4, available 0x5ad6800000000000 47 inputs)
def r175 : List RE := [(0x18c6000000000000,49,0)]
def d175 : List Entry := [([],[0],[])]
def e175 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g175 : GoodC c175 := claim_sound [c94] (gcons g94 gnil) r175 d175 e175 c175 (by decide +kernel)
def c176 : Claim := (5, available 0x2d6b400000005ad68ccc00000000 34 inputs)
def r176 : List RE := [(0xc630000000000000ccc00000000,34,0),(0x5ad6800000000000,47,1)]
def d176 : List Entry := [([],[0,1],[])]
def e176 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g176 : GoodC c176 := claim_sound [c174,c175] (gcons g174 (gcons g175 gnil)) r176 d176 e176 c176 (by decide +kernel)
def c177 : Claim := (9, available 0xc000000000003def6f7bbbbd7bdeddddffffffff 0 inputs)
def r177 : List RE := [(0x39c06e7333017380d981ee0fbb50,4,0),(0x30006c0320016000d001c00f0300,8,1),(0x1c000700300038001800e003810,4,2),(0x38000e00300070001800e0038040,6,3),(0x800000000000340e6d03a839681cd419d0ef43a6,1,4),(0xc600380310018c01100cc0384,2,5),(0x34000d00280068001400d0034020,5,6),(0x1e00078038003c001c00f003c18,3,7),(0x40000000000001ad606b82b5035ac1550ddc378d,0,8),(0xc00000000000000000003bad00000000bbb8007b,0,9),(0x2d6b400000005ad68ccc00000000,34,10),(0xc0000000000000000000000000001ddd0002eeff,0,11),(0xc0000000000000000739bbbd00000000fffdddff,0,12),(0xc0000000000000000000000039ce5ddd7777ffff,0,13),(0x3def6f7bbbbd0000000000000000,64,14)]
def d177 : List Entry := [([],[4,8,9,11,12,14],[0,1,2,3,4,5,6,7,8,9,10])]
def e177 : List (List Entry) := [[([23],[4,0,7,8,3,9,11,12,6,2,14],[0,1,2,3]),([31],[4,0,8,3,9,11,12,14],[4,5,6]),([39],[8,0,4,2,3,9,11,12,6,14],[7,8,9,10]),([47],[8,0,4,7,9,11,12,14],[11,12,13]),([55],[12,9,0,4,2,8,3,11,10],[]),([63],[12,0,9,4,2,8,3,11,10],[]),([85],[12,4,2,8,3,9,10,11],[]),([303],[4,7,2,9,5,12,13,14,11],[14]),([319],[4,7,2,8,6,11,12,10],[]),([575],[8,3,4,6,11,12,10],[]),([853],[12,9,11,4,8],[15,3,6,10,13,14])],[([23,56],[4,7,8,12,1,13,14,11],[0]),([23,60],[12,1,13,14,11],[1]),([23,78],[4,12,10],[]),([23,1125],[4],[0,1]),([31,70],[0,12,10],[]),([31,100],[0,9,10,11],[]),([31,1125],[9,4],[2]),([39,56],[4,0,12,3,8,13,14,11],[3]),([39,60],[12,2,13,14,11],[4]),([39,78],[8,12,10],[]),([39,1125],[8],[3,4]),([47,70],[0,12,10],[]),([47,100],[0,9,10,11],[]),([47,1125],[9,8],[5]),([303,1125],[4],[]),([853,42],[12,9,11],[])],[([23,56,853],[],[]),([23,60,853],[],[]),([31,1125,40],[],[]),([39,56,853],[],[]),([39,60,853],[],[]),([47,1125,40],[],[])]]
set_option maxRecDepth 100000 in
theorem g177 : GoodC c177 := claim_sound [c28,c27,c168,c169,c57,c170,c55,c171,c83,c173,c176,c115,c148,c164,c167] (gcons g28 (gcons g27 (gcons g168 (gcons g169 (gcons g57 (gcons g170 (gcons g55 (gcons g171 (gcons g83 (gcons g173 (gcons g176 (gcons g115 (gcons g148 (gcons g164 (gcons g167 gnil))))))))))))))) r177 d177 e177 c177 (by decide +kernel)
def c178 : Claim := (12, inputs)
def r178 : List RE := [(0x3de07f7bbb81fbc0fef77703f781fb83ee0fbb50,4,0),(0x38007e03b001f000fc076003e001f003c00f0300,8,1),(0x1e00078038003c000f00700078003800e003810,4,2),(0x1c0707383018380e0e706030701c3030c0c3300,8,3),(0x3c000f00380078001e007000f0003800e0038040,6,4),(0x35a060003b81eb40c0007703d681aa82aa080050,4,5),(0x1ce037399980800000000000b5817b836607bb50,4,6),(0x39c06e7333017380d981ee0fbb50,4,7),(0x800f0000003c001e00000078003c003800e00006,1,8),(0x400e8000003a001d00000074003a003400d00005,0,9),(0xc00d80000036001b0000006c0036002c00b00003,0,10),(0xba0f7e83f43df41efd07e87be83df43bd0ef43a6,1,11),(0xe7003c039801ce00780730039c03300cc0384,2,12),(0x3a000e80340074001d006800e8003400d0034020,5,13),(0x1f0007c03c003e000f8078007c003c00f003c18,3,14),(0x1d00074034003a000e80680074003400d003408,3,15),(0x41def077c37b83bde0ef86f7077bc3770ddc378d,0,16),(0xf7bde0003ff7ef7bc0007fefdef7aeeebbb8007b,0,17),(0xc00000003ff7ce7380005dce00002eee0000007b,0,18),(0x37bde0000000000000000000def78000bbb80000,19,19),(0xe739c0002ee7000000007fef00000000bbb8007b,0,20),(0x6f7bc0000000def7aeee00000000,33,21),(0xc0000def7fffdef7bbdeddde00003fff0002eeff,0,22),(0xc00009ce6eef0000139cddde000000000000ccff,0,23),(0xc00005ad5dde80000000000000003fff0002eeff,0,24),(0x5ef7bbdeddde0000000000000000,65,25),(0xc000000000001ce72b5a999c00001ddd0002eeff,0,26),(0xdef7fff8000000000000000000000000000,111,27),(0xffffc00000000000,46,28),(0x3ffff00000000000000000000000000000000000,140,29),(0xef7bdbdeeeef000017bdffff00000000fffdddff,0,30),(0xce73939cccce000000000000000000007775ddff,0,31),(0x17bdffff0000000000000000,64,32),(0xc0000000000000000739bbbd00000000fffdddff,0,33),(0x2f7bdbdeeeef0000000000000000000000000000,112,34),(0x7fffe00000000000000000000000,93,35),(0xdef7b7bdddde800000000000bdef7fff7777ffff,0,36),(0xc0000000000000000000000039ce5ddd7777ffff,0,37),(0x1ef7b7bdddde8000000000000000000000000000,111,38),(0x3def6f7bbbbd0000000000000000,64,39),(0xc000000000003def6f7bbbbd7bdeddddffffffff,0,40)]
def d178 : List Entry := [([],[11,16,22,30,36,40],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42])]
def e178 : List (List Entry) := [[([23],[11,0,14,16,4,22,30,36,40,13,2],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]),([31],[11,0,16,4,22,30,36,40],[22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41]),([39],[16,0,11,2,4,22,30,36,40,13],[42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]),([47],[16,0,11,14,22,30,36,40],[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83]),([51],[17,11,2,16,4,22,30,36,40,19,21],[84,85,86,87,88,89,90,91,92,93]),([55],[0,17,11,2,16,4,22,30,36,40],[84,85,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128]),([59],[0,17,11,2,16,4,22,30,36,40,19,21],[85,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,110,145]),([63],[0,11,2,16,4,22,30,36,40,17],[85,84,146,147,148,149,90,150,151,152,153,154,155,156,157,158,159,160,161]),([71],[22,0,11,2,16,4,19,30,28,36,25,40,29],[162,94,163,164,165,166,167,168,111,112,150,169,170]),([79],[22,0,11,2,16,4,30,36,25,40,19,28,29],[171,172,173,174,113]),([87],[30,0,11,2,16,4,21,22,28,36,35,40,34],[175,98,176,177,165,178,179,180,114,115,151,181,182]),([95],[30,0,11,2,16,4,22,36,40,34,21,28,35],[183,184,185,186,116]),([103],[36,0,11,2,16,4,25,30,40,38,35],[187,188,189,91,117]),([111],[36,0,11,2,16,4,22,25,30,40,38,35],[190,191,192,193,194]),([119],[40,0,11,2,16,4,34,22,36,38,29],[195,196,197,92,118]),([127],[40,0,11,2,16,4,22,30,34,36,38,29],[198,199,200,201,202]),([303],[11,14,2,12,22,30,36,40],[203,204,205,206,207,208,209,210,211,212,213,214,215,216]),([315],[11,14,2,16,13,22,30,36,40,17,19,21],[217,218,219,220,221,222,223]),([319],[11,14,2,16,13,22,30,36,40,17],[224,225,226,227,228,229,230,231,232,233,234,235,236,237]),([335],[11,14,2,16,13,30,36,25,40,22,19,28,29],[238,239,240,241]),([351],[11,14,2,16,13,22,36,40,34,30,21,28,35],[242,243,244,245]),([367],[11,14,2,16,13,22,25,30,40,38,35],[246,247,248]),([383],[11,14,2,16,13,22,30,34,36,38,29],[249,250,251]),([571],[11,16,17,4,13,22,30,36,40,19,21],[252,253,254,255,256,257,258]),([575],[16,17,4,11,13,22,30,36,40],[259,260,261,262,263,264,265,266,267,268,269,270,271,272]),([591],[16,22,4,11,13,30,36,25,40,19,28,29],[273,274,275,276]),([607],[16,30,4,11,13,22,36,40,34,21,28,35],[277,278,279,280]),([623],[16,36,4,11,13,22,25,30,40,38,35],[281,282,283]),([639],[16,40,4,11,13,22,30,34,36,38,29],[284,285,286]),([839],[17,22,11,16,30,36,25,40,21,29],[287,288,289,290,291,292,293,8,28,50,70,203]),([847],[22,17,18,19,11,16,30,36,25,40,28,29],[294,295,94,296,297,298,299,300,301,302,303,304,119,152,228,263,169,305,9,29,51,71,204]),([855],[17,30,11,16,22,36,40,34,19,35],[306,307,308,309,310,311,312,10,30,52,72,205]),([863],[30,17,20,21,11,16,22,36,40,34,28,35],[313,314,98,315,316,317,318,319,320,302,321,322,120,153,229,264,181,323,11,31,53,73,206]),([871],[17,36,11,16,22,25,30,40,38,21],[324,325,326,327,328,329,330,12,32,54,74,207]),([879],[36,17,25,11,16,30,40,38,35],[331,332,333,334,335,336,337,121,154,230,265,13,33,55,75,208]),([887],[17,40,11,16,22,30,34,36,38,19],[338,339,340,341,342,343,344,14,34,56,76,209]),([895],[40,17,34,11,16,22,36,38,29],[345,346,347,348,349,350,351,122,155,231,266,15,35,57,77,210]),([1119],[22,30,23,19,11,16,36,25,40,34],[352,353,165,354,355,356,357,358,359,360,361,302,305,323,16,36,58,78,123,156,211,232,267]),([1135],[22,36,24,25,38,11,16,19,30,28,40],[17,37,59,79,124,157,212,233,268]),([1151],[22,40,26,34,11,16,36,25,38,19],[362,363,364,365,366,367,368,369,170,293,18,38,60,80,125,158,213,234,269]),([1391],[30,36,25,11,16,40,34,38,21],[370,371,372,373,374,375,376,377,182,312,19,39,61,81,126,159,214,235,270]),([1407],[30,40,33,34,38,11,16,21,22,28],[20,40,62,82,127,160,215,236,271]),([1663],[36,40,37,25,11,16,30,34],[21,41,63,83,93,128,145,161,216,223,237,258,272])],[([23,56],[11,14,16,1,22,30,36,40],[0,1,2,3,4,5,6,7,8,9,10,11,12,13]),([23,60],[11,0,1,22,30,36,40],[14,15,16,17,18,19,20,21,22,23,24,25,26,27]),([23,74],[11,14,0,16,17,4,22,30,36,40,1,19,21],[28,29,30,31,32]),([23,78],[11,14,0,16,4,22,1,30,36,40,17],[33,34,35,36,37,38,39,40,41,42,43,44,45,46]),([23,94],[11,14,0,16,4,1,30,36,25,40,22,19,28,29],[47,48,49,50]),([23,110],[11,14,0,16,4,1,22,36,40,34,30,21,28,35],[51,52,53,54]),([23,126],[11,14,0,16,4,1,22,25,30,40,38,35],[55,56,57]),([23,142],[11,14,0,16,4,1,22,30,34,36,38,29],[58,59,60]),([23,1111],[11,17,22,14,2,16,4,30,36,25,40,21,29,13],[61,62,63,64,0,14]),([23,1119],[11,22,17,14,18,19,2,16,4,30,36,25,40,28,29,13],[65,66,67,68,69,70,37,71,1,15]),([23,1127],[11,17,30,14,2,16,4,22,36,40,34,19,35,13],[72,73,74,75,2,16]),([23,1135],[11,30,17,14,20,21,2,16,4,22,36,40,34,28,35,13],[76,77,78,68,79,80,38,81,3,17]),([23,1143],[11,17,36,14,2,16,4,22,25,30,40,38,21,13],[82,83,84,85,4,18]),([23,1151],[11,36,17,14,25,2,16,4,30,40,38,35,13],[86,87,88,89,39,5,19]),([23,1159],[11,17,40,14,2,16,4,22,30,34,36,38,19,13],[90,91,92,93,6,20]),([23,1167],[11,40,17,14,34,2,16,4,22,36,38,29,13],[94,95,96,97,40,7,21]),([23,1391],[11,30,22,14,23,19,2,16,4,36,25,40,34,13],[98,99,100,101,102,68,71,81,8,22,41]),([23,1407],[11,36,22,14,24,25,38,16,4,19,30,28,40,13],[9,23,42]),([23,1423],[11,40,22,14,34,2,16,4,36,25,38,19,13],[103,104,105,106,107,64,10,24,43]),([23,1663],[11,36,30,14,25,2,16,4,40,34,38,21,13],[108,109,110,111,112,75,11,25,44]),([23,1679],[11,40,30,14,33,34,38,16,4,21,22,28,13],[12,26,45]),([23,1935],[11,40,36,14,37,25,16,4,30,34,13],[13,27,32,46]),([31,66],[0,11,16,17,4,22,30,36,40,19,21],[113,114,115,116,117]),([31,70],[0,11,16,4,22,8,5,30,36,40],[118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135]),([31,86],[0,11,16,4,8,19,30,28,36,25,40,29,22],[136,118,137,138,139,140,141,142,143,144]),([31,102],[0,11,16,4,8,21,22,28,36,35,40,34,30],[145,120,146,147,139,148,149,150,151,152]),([31,118],[0,11,16,4,25,30,40,38,36,35],[153,154,155]),([31,134],[0,11,16,4,34,22,36,38,40,29],[156,157,158]),([31,1111],[0,17,22,11,16,4,30,36,25,40,21,29],[159,160,161,162]),([31,1119],[0,22,17,18,19,11,16,4,30,36,25,40,28,29],[163,118,164,165,166,167,126,143,168]),([31,1127],[0,17,30,11,16,4,22,36,40,34,19,35],[169,170,171,172]),([31,1135],[0,30,17,20,21,11,16,4,22,36,40,34,28,35],[173,120,174,165,175,176,127,151,177]),([31,1143],[0,17,36,11,16,4,22,25,30,40,38,21],[178,179,180,181]),([31,1151],[0,36,17,25,11,16,4,30,40,38,35],[182,183,184,185,128]),([31,1159],[0,17,40,11,16,4,22,30,34,36,38,19],[186,187,188,189]),([31,1167],[0,40,17,34,11,16,4,22,36,38,29],[190,191,192,193,129]),([31,1391],[0,30,22,23,19,11,16,4,36,25,40,34],[194,139,195,196,197,165,168,177,130]),([31,1407],[0,36,22,24,25,38,11,16,4,19,30,28,40],[131]),([31,1423],[0,40,22,26,34,11,16,4,36,25,38,19],[198,199,200,201,202,144,162,132]),([31,1663],[0,36,30,25,11,16,4,40,34,38,21],[203,204,205,206,207,152,172,133]),([31,1679],[0,40,30,33,34,38,11,16,4,21,22,28],[134]),([31,1935],[0,40,36,37,25,11,16,4,30,34],[117,135]),([39,56],[11,16,0,4,22,30,36,40],[208,209,210,211,212,213,214,215,216,217,218,219,220,221]),([39,60],[16,0,2,22,30,36,40],[222,223,224,225,226,227,228,229,230,231,232,233,234,235]),([39,74],[16,17,0,4,11,2,22,30,36,40,19,21],[236,237,238,239,240]),([39,78],[16,4,11,2,22,3,30,36,40,17],[241,242,243,244,245,246,247,248,249,250,251,252,253,254]),([39,94],[16,3,22,11,2,30,36,25,40,4,19,28,29],[255,256,257,258]),([39,110],[16,3,30,11,2,22,36,40,34,4,21,28,35],[259,260,261,262]),([39,126],[16,3,36,11,2,22,25,30,40,38,35],[263,264,265]),([39,142],[16,3,40,11,2,22,30,34,36,38,29],[266,267,268]),([39,1111],[16,17,22,4,11,2,30,36,25,40,21,29,13],[269,270,271,272,208,222]),([39,1119],[16,22,17,4,18,19,11,2,30,36,25,40,28,29,13],[273,274,275,276,277,278,245,279,209,223]),([39,1127],[16,17,30,4,11,2,22,36,40,34,19,35,13],[280,281,282,283,210,224]),([39,1135],[16,30,17,4,20,21,11,2,22,36,40,34,28,35,13],[284,285,286,276,287,288,246,289,211,225]),([39,1143],[16,17,36,4,11,2,22,25,30,40,38,21,13],[290,291,292,293,212,226]),([39,1151],[16,36,17,4,25,11,2,30,40,38,35,13],[294,295,296,297,247,213,227]),([39,1159],[16,17,40,4,11,2,22,30,34,36,38,19,13],[298,299,300,301,214,228]),([39,1167],[16,40,17,4,34,11,2,22,36,38,29,13],[302,303,304,305,248,215,229]),([39,1391],[16,30,22,4,23,19,11,2,36,25,40,34,13],[306,307,308,309,310,276,279,289,216,230,249]),([39,1407],[16,36,22,4,24,25,38,11,2,19,30,28,40,13],[217,231,250]),([39,1423],[16,40,22,4,26,34,11,2,36,25,38,19,13],[311,312,313,314,315,272,218,232,251]),([39,1663],[16,36,30,4,25,11,2,40,34,38,21,13],[316,317,318,319,320,283,219,233,252]),([39,1679],[16,40,30,4,33,34,38,11,2,21,22,28,13],[220,234,253]),([39,1935],[16,40,36,4,37,25,11,2,30,34,13],[221,235,240,254]),([47,66],[0,16,11,14,17,22,30,36,40,19,21],[321,322,323,324,325]),([47,70],[0,16,11,14,22,9,5,30,36,40],[326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343]),([47,86],[0,16,11,14,9,19,30,28,36,25,40,29,22],[344,326,345,346,347,348,349,350,351,352]),([47,102],[0,16,11,14,9,21,22,28,36,35,40,34,30],[353,328,354,355,347,356,357,358,359,360]),([47,118],[0,16,11,14,25,30,40,38,36,35],[361,362,363]),([47,134],[0,16,11,14,34,22,36,38,40,29],[364,365,366]),([47,1111],[0,17,22,16,11,14,30,36,25,40,21,29],[367,368,369,370]),([47,1119],[0,22,17,18,19,16,11,14,30,36,25,40,28,29],[371,326,372,373,374,375,334,351,376]),([47,1127],[0,17,30,16,11,14,22,36,40,34,19,35],[377,378,379,380]),([47,1135],[0,30,17,20,21,16,11,14,22,36,40,34,28,35],[381,328,382,373,383,384,335,359,385]),([47,1143],[0,17,36,16,11,14,22,25,30,40,38,21],[386,387,388,389]),([47,1151],[0,36,17,25,16,11,14,30,40,38,35],[390,391,392,393,336]),([47,1159],[0,17,40,16,11,14,22,30,34,36,38,19],[394,395,396,397]),([47,1167],[0,40,17,34,16,11,14,22,36,38,29],[398,399,400,401,337]),([47,1391],[0,30,22,23,19,16,11,14,36,25,40,34],[402,347,403,404,405,373,376,385,338]),([47,1407],[0,36,22,24,25,38,16,11,14,19,30,28,40],[339]),([47,1423],[0,40,22,26,34,16,11,14,36,25,38,19],[406,407,408,409,410,352,370,340]),([47,1663],[0,36,30,25,16,11,14,40,34,38,21],[411,412,413,414,415,360,380,341]),([47,1679],[0,40,30,33,34,38,16,11,14,21,22,28],[342]),([47,1935],[0,40,36,37,25,16,11,14,30,34],[325,343]),([51,26],[0,17,11,2,16,4,22,19,30,21,36,8,5,40],[416,417,418,419,420]),([51,28],[0,11,16,17,22,30,36],[]),([51,94],[17,22,19,11,2,16,4,30,18,21,36,25,40,29],[]),([51,110],[17,30,21,11,2,16,4,22,19,36,20,35,40,34],[]),([51,126],[17,36,25,11,2,16,4,30,21,40,38],[421,422]),([51,142],[17,40,34,11,2,16,4,22,19,36,38],[423,424]),([51,300],[0,17,11,16,2,22,4,30,19,36,21,40],[425,426]),([51,375],[0,36,25,17,11,2,16,4,30,21,40,38,35],[427]),([51,391],[0,40,34,17,11,2,16,4,22,19,36,38,29],[428]),([51,1935],[17,40,36,37,25,11,2,16,4,30,34],[420,426]),([55,86],[0,22,19,18,11,2,16,4,30,36,25,40,8,28],[429,430]),([55,87],[22,5,18,8,19,16,4,30,36,25,40,28,29],[431,432,433]),([55,94],[22,19,11,2,16,4,30,36,25,40,28,29],[434,435]),([55,95],[22,5,17,11,2,16,4,30,36,25,40,19,28,29],[436,437]),([55,102],[0,30,21,20,11,2,16,4,22,36,40,34,8,28],[438,439]),([55,103],[30,5,20,8,21,16,4,22,36,40,34,28,35],[440,441,442]),([55,110],[30,21,11,2,16,4,22,36,40,34,28,35],[443,444]),([55,111],[30,5,17,11,2,16,4,22,36,40,34,21,28,35],[445,446]),([55,118],[0,36,25,11,2,16,4,30,40,38,17,8,35],[447,448,449,450,451]),([55,119],[36,5,8,10,16,4,22,25,30,40,38,35],[452,453,454,455,456,457]),([55,126],[36,25,11,2,16,4,30,40,38,17,5,35],[458]),([55,127],[36,5,11,2,16,4,22,25,30,40,38,35],[459,460]),([55,134],[0,40,34,11,2,16,4,22,36,38,17,8,29],[461,462,463,464,465]),([55,135],[40,5,8,10,16,4,22,30,34,36,38,29],[466,467,468,469,470,471]),([55,142],[40,34,11,2,16,4,22,36,38,17,5,29],[472]),([55,143],[40,5,11,2,16,4,22,30,34,36,38,29],[473,474]),([55,296],[0,11,2,16,4,22,19,30,21,36,40],[425,475,457,460,471,474,476]),([55,342],[0,22,17,8,19,16,4,30,28,25,36,40,29,2],[477,478]),([55,343],[22,0,17,8,10,16,4,30,36,25,40,19,28,29],[479,431,480,481]),([55,350],[0,22,18,11,2,16,4,30,28,36,25,40,29],[482]),([55,358],[0,30,17,8,21,16,4,22,28,36,35,34,40,2],[483,484]),([55,359],[30,0,17,8,10,16,4,22,36,40,34,21,28,35],[485,440,486,487]),([55,366],[0,30,20,11,2,16,4,22,28,36,35,40,34],[488]),([55,375],[0,36,17,8,10,16,4,22,25,30,40,38,35],[489,453,490]),([55,391],[0,40,17,8,10,16,4,22,30,34,36,38,29],[491,467,492]),([55,607],[17,22,0,18,10,11,2,16,4,30,19,25,21,36,40,29],[]),([55,623],[17,30,0,20,10,11,2,16,4,22,19,36,21,34,35,40],[]),([55,639],[17,36,0,25,10,11,2,16,4,30,21,40,38],[452,493,494,495]),([55,655],[17,40,0,34,10,11,2,16,4,22,19,36,38],[466,496,497,498]),([55,1391],[22,30,19,0,11,2,16,4,36,25,40,34],[499,500,501,502,503]),([55,1407],[22,36,24,19,0,11,2,16,4,30,28,40,29],[]),([55,1423],[22,40,19,0,11,2,16,4,30,34,36,25],[504,505,506,507,508,509,510]),([55,1663],[30,36,21,0,11,2,16,4,22,25,40,34],[511,512,513,514,515,516,517]),([55,1679],[30,40,33,21,0,11,2,16,4,22,28,36,35],[]),([55,1935],[36,40,37,25,17,0,11,2,16,4,30,34],[476]),([59,56],[0,11,16,17,22,4,30,19,36,21,40],[518]),([59,60],[0,17,16,1,14,22,4,30,19,36,21,40],[519]),([59,72],[0,16,11,14,17,22,30,19,36,21,40],[520]),([59,76],[0,17,11,2,22,3,4,30,19,36,21,40],[521]),([59,88],[0,17,11,14,16,22,30,4,36,21,40,25],[]),([59,92],[0,17,11,2,16,4,30,18,19,36,21,40],[522]),([59,94],[0,17,11,2,16,4,30,18,19,36,21,40,25],[]),([59,104],[0,17,11,14,16,30,22,4,36,19,40,34],[]),([59,108],[0,17,11,2,16,4,22,19,36,20,21,40],[523]),([59,110],[0,17,11,2,16,4,22,19,36,20,21,40,34],[]),([59,120],[0,17,11,36,16,2,22,4,30,19,40,21],[]),([59,124],[0,17,11,2,16,4,22,19,30,21,40,39],[]),([59,126],[0,17,11,2,16,4,22,19,30,21,40,38,36,25],[]),([59,136],[0,17,11,40,16,2,22,4,30,19,36,21],[]),([59,140],[0,17,11,2,16,4,22,19,30,21,36,38],[]),([59,142],[0,17,11,2,16,4,22,19,30,21,36,38],[]),([59,1935],[0,40,36,37,25,34,17,11,2,16,4],[518,519,520,521,522,523,476]),([63,86],[0,17,19,11,2,16,4,30,36,25,40,22,28],[524,525]),([63,102],[0,17,21,11,2,16,4,22,36,40,34,30,28],[526,527]),([63,118],[0,17,25,36,11,2,16,4,30,40,38,35],[528]),([63,134],[0,17,34,40,11,2,16,4,22,36,38,29],[529]),([63,342],[0,18,10,11,2,16,4,19,22,25,30,36,40,28],[530]),([63,358],[0,20,10,11,2,16,4,21,30,34,22,36,28,40],[531]),([63,607],[0,22,17,19,18,25,11,2,16,4,30,21,36,40,29],[]),([63,623],[0,30,17,21,20,34,11,2,16,4,22,19,36,35,40],[]),([63,639],[0,36,17,25,11,2,16,4,30,21,40,38],[532,533,534]),([63,655],[0,40,17,34,11,2,16,4,22,19,36,38],[535,536,537]),([63,1391],[0,30,22,19,11,2,16,4,36,25,40,34],[538,539,540]),([63,1407],[0,36,22,24,19,11,2,16,4,30,28,40,29],[]),([63,1423],[0,40,22,19,11,2,16,4,30,34,36,25],[541,542,543]),([63,1663],[0,36,30,21,11,2,16,4,22,25,40,34],[544,545,546]),([63,1679],[0,40,30,33,21,11,2,16,4,22,28,36,35],[]),([63,1935],[0,40,36,37,25,11,2,16,4,30,34,17],[420,426]),([71,82],[17,22,11,2,16,4,30,28,36,25,40,29],[547]),([71,90],[17,22,0,11,2,16,4,30,28,36,25,40,29,19],[548,549,550,551,552,553,554,555,556,557,558,477,479,559]),([71,94],[22,19,11,2,16,4,30,28,36,25,40,29],[431]),([71,102],[0,22,19,30,23,11,2,16,4,36,25,40,29],[560,561]),([71,110],[22,19,0,11,2,16,4,21,28,36,25,40,29,30],[562,478,480,530]),([71,134],[0,22,19,40,26,11,2,16,4,30,28,36,25],[563,564]),([71,142],[22,19,0,11,2,16,4,27,30,28,25,40,36],[565,566,567,481]),([71,606],[22,17,18,19,0,2,4,36,29,25,28,11],[548,568,559]),([71,654],[22,40,0,19,2,4,36,30,25,28,11],[569,570]),([79,82],[0,17,22,11,2,16,4,30,28,36,25,40,29],[]),([79,86],[0,22,11,2,16,4,30,28,36,25,40,29],[]),([79,102],[0,22,11,2,16,4,19,28,36,25,40,29,30],[571,482]),([79,134],[0,22,11,2,16,4,19,27,30,28,25,40,36],[572]),([87,82],[17,30,11,2,16,4,22,28,36,35,40,34],[573]),([87,90],[17,30,0,11,2,16,4,22,28,36,35,40,34,21],[574,575,576,577,578,579,580,581,582,583,584,483,485,585]),([87,94],[30,21,11,2,16,4,22,28,36,35,40,34],[440]),([87,110],[22,21,30,11,2,16,4,19,28,36,25,40,34],[586,484,486,531]),([87,118],[0,30,21,36,31,11,2,16,4,22,25,40,34],[587,588]),([87,126],[30,21,0,11,2,16,4,25,40,34,36],[589,590,591,487]),([87,606],[30,17,20,21,0,2,4,35,40,34,28,11],[574,592,585]),([87,638],[30,36,0,21,2,4,40,22,25,34,11],[593,594]),([95,82],[0,17,30,11,2,16,4,22,28,36,35,40,34],[]),([95,86],[0,30,11,2,16,4,22,28,36,35,40,34],[]),([95,102],[0,22,30,11,2,16,4,21,28,36,25,40,34],[595,488]),([95,118],[0,30,11,2,16,4,21,25,40,34,36],[596]),([103,90],[17,36,0,25,11,2,16,4,30,35,40,38],[489]),([103,94],[36,25,0,11,2,16,4,30,35,38,40,17,10],[427,453]),([103,126],[30,25,36,11,2,16,4,32,35,21,40,34],[490]),([111,82],[0,17,36,11,2,16,4,22,25,30,35,40,38],[]),([111,86],[0,36,11,2,16,4,22,25,30,35,40,38],[]),([111,96],[0,22,11,36,16,2,4,30,35,38,40],[]),([111,100],[0,36,11,2,16,4,25,30,35,38,40],[]),([111,118],[0,30,36,11,2,16,4,35,32,34,25],[]),([119,90],[17,40,0,34,11,2,16,4,22,29,36,38],[491]),([119,94],[40,27,0,11,2,16,4,29,34,38,17,10],[428,467]),([119,110],[22,27,40,11,2,16,4,29,19,30,28,36,25],[492]),([127,82],[0,17,40,11,2,16,4,22,29,30,34,36,38],[]),([127,86],[0,40,11,2,16,4,22,29,30,34,36,38],[]),([127,102],[0,22,40,11,2,16,4,29,27,25,28],[]),([127,112],[0,30,11,40,16,2,4,22,29,38],[]),([127,116],[0,40,11,2,16,4,34,22,29,38],[]),([303,1111],[11,17,22,12,14,2,30,36,25,40],[597,598,599]),([303,1119],[11,22,17,12,14,2,30,36,25,40],[600,601,602,603,604]),([303,1127],[11,17,30,12,14,2,22,36,40,34],[605,606,607]),([303,1135],[11,30,17,12,14,2,22,36,40,34],[608,601,609,610,611]),([303,1143],[11,17,36,12,14,2,22,25,30,40,38],[612,613,614]),([303,1151],[11,36,17,12,14,2,25,30,40,38],[615,616,617]),([303,1159],[11,17,40,12,14,2,22,30,34,36,38],[618,619,620]),([303,1167],[11,40,17,12,14,2,22,34,36,38],[621,622,623]),([303,1391],[11,30,22,12,14,2,36,25,40,34],[624,625,626,601,604,611]),([303,1407],[11,36,22,12,14,2,24,25,38],[]),([303,1423],[11,40,22,12,14,2,34,36,25,38],[627,628,629,630,599]),([303,1663],[11,36,30,12,14,2,25,40,34,38],[631,632,633,634,607]),([303,1679],[11,40,30,12,14,2,33,34,38],[]),([303,1935],[11,40,36,12,14,2,37,25],[]),([315,72],[11,16,14,17,22,2,30,19,36,21,40],[635]),([315,76],[11,16,14,2,22,13,17,30,19,36,21,40],[636]),([315,94],[11,14,17,2,16,13,30,18,19,36,21,40,25],[]),([315,110],[11,14,17,2,16,13,22,19,36,20,21,40,34],[]),([315,126],[11,14,17,2,16,13,22,19,30,21,40,38],[]),([315,142],[11,14,17,2,16,13,22,19,30,21,36,38],[]),([315,1935],[11,40,36,14,37,25,2,16,13,30,34],[635,636]),([319,86],[11,14,17,2,16,13,30,19,36,25,40,22,28],[637,638]),([319,102],[11,14,17,2,16,13,22,21,36,40,34,30,28],[639,640]),([319,118],[11,14,17,2,16,13,22,25,30,40,38,36,35],[641]),([319,134],[11,14,17,2,16,13,22,34,36,38,40,29],[642]),([319,607],[11,22,17,14,2,16,13,30,18,19,25,21,36,40,29],[]),([319,623],[11,30,17,14,2,16,13,22,19,36,20,21,34,35,40],[]),([319,639],[11,36,17,14,2,16,13,25,30,21,40,38],[643,644]),([319,655],[11,40,17,14,2,16,13,22,19,34,36,38],[645,646]),([319,1391],[11,30,22,19,14,2,16,13,36,25,40,34],[647,648,649]),([319,1407],[11,36,22,24,19,2,16,13,30,28,40,29],[]),([319,1423],[11,40,22,19,14,2,16,13,30,34,36,25],[650,651,652]),([319,1663],[11,36,30,21,14,2,16,13,22,25,40,34],[653,654,655]),([319,1679],[11,40,30,33,21,2,16,13,22,28,36,35],[]),([319,1935],[11,40,36,37,25,14,2,16,13,30,34],[]),([335,82],[11,14,22,17,2,16,13,30,28,36,25,40,29],[]),([335,86],[11,14,17,2,16,13,30,28,36,25,40,29],[]),([335,102],[11,14,22,2,16,13,19,28,36,25,40,29],[656]),([335,134],[11,14,22,2,16,13,19,27,30,28,25,36],[657]),([351,82],[11,14,30,17,2,16,13,22,28,36,35,40,34],[]),([351,86],[11,14,17,2,16,13,22,28,36,35,40,34],[]),([351,102],[11,14,22,2,16,13,21,28,36,25,40,34],[658]),([351,118],[11,14,30,2,16,13,21,25,40,34],[659]),([367,82],[11,14,36,17,2,16,13,22,25,30,35,40,38],[]),([367,86],[11,14,17,2,16,13,22,25,30,35,40,38],[]),([367,118],[11,14,30,2,16,13,35,32,25,34],[]),([383,82],[11,14,40,17,2,16,13,22,29,30,34,36,38],[]),([383,86],[11,14,17,2,16,13,22,29,30,34,36,38],[]),([383,102],[11,14,22,2,16,13,29,27,28,25],[]),([571,72],[11,16,17,22,4,30,19,36,21,40],[660]),([571,76],[11,16,2,22,13,17,4,30,19,36,21,40],[661]),([571,94],[16,17,4,11,13,30,18,19,36,21,40,25],[]),([571,110],[16,17,4,11,13,22,19,36,20,21,40,34],[]),([571,126],[16,17,4,11,13,22,19,30,21,40,38],[]),([571,142],[16,17,4,11,13,22,19,30,21,36,38],[]),([571,1935],[16,40,36,17,37,25,4,11,13,30,34],[660,661]),([575,86],[11,16,4,17,13,30,19,36,25,40,22,28],[662,663]),([575,102],[11,16,4,17,13,22,21,36,40,34,30,28],[664,665]),([575,118],[11,16,4,17,13,22,25,30,40,38,36,35],[666]),([575,134],[11,16,4,17,13,22,34,36,38,40,29],[667]),([575,607],[16,22,17,4,11,13,30,18,19,25,21,36,40,29],[]),([575,623],[16,30,17,4,11,13,22,19,36,20,21,34,35,40],[]),([575,639],[16,36,17,4,11,13,25,30,21,40,38],[668,669]),([575,655],[16,40,17,4,11,13,22,19,34,36,38],[670,671]),([575,1391],[16,30,22,19,4,11,13,36,25,40,34],[672,673,674]),([575,1407],[16,36,22,24,19,4,11,13,30,28,40,29],[]),([575,1423],[16,40,22,19,4,11,13,30,34,36,25],[675,676,677]),([575,1663],[16,36,30,21,4,11,13,22,25,40,34],[678,679,680]),([575,1679],[16,40,30,33,21,4,11,13,22,28,36,35],[]),([575,1935],[16,40,36,37,25,17,4,11,13,30,34],[]),([591,82],[16,17,22,4,11,13,30,28,36,25,40,29],[]),([591,86],[11,16,4,17,13,30,28,36,25,40,29],[]),([591,102],[11,16,4,22,13,19,28,36,25,40,29],[681]),([591,134],[11,16,4,22,13,19,27,30,28,25,36],[682]),([607,82],[16,17,30,4,11,13,22,28,36,35,40,34],[]),([607,86],[11,16,4,17,13,22,28,36,35,40,34],[]),([607,102],[11,16,4,22,13,21,28,36,25,40,34],[683]),([607,118],[11,16,4,30,13,21,25,40,34],[684]),([623,82],[16,17,36,4,11,13,22,25,30,35,40,38],[]),([623,86],[11,16,4,17,13,22,25,30,35,40,38],[]),([623,118],[11,16,4,30,13,35,32,25,34],[]),([639,82],[16,17,40,4,11,13,22,29,30,34,36,38],[]),([639,86],[11,16,4,17,13,22,29,30,34,36,38],[]),([639,102],[11,16,4,22,13,29,27,28,25],[]),([839,58],[17,22,11,2,16,4,30,21,36,25,40,29],[685]),([839,62],[17,22,11,2,16,4,30,21,36,25,40,29],[]),([839,78],[11,14,2,16,13,30,21,36,25,40,29],[]),([839,94],[16,17,22,4,11,13,30,21,36,25,40,29],[]),([839,110],[17,22,20,21,36,28,11,16,25,40,29],[62,160,270,368,597]),([839,142],[17,22,27,11,16,30,21,36,25,40],[686,687,688,689,690,691,63,161,271,369,598]),([839,654],[17,22,40,19,36,30,25,28,11,16],[692,693,685,64,162,272,370,599]),([847,50],[22,18,19,11,2,16,4,30,28,36,25,40,29],[]),([847,54],[0,22,17,11,2,16,4,30,28,36,25,40,29,18],[548,568]),([847,62],[22,0,19,11,2,16,4,30,28,36,25,40,29],[]),([847,70],[11,14,2,16,13,30,28,36,25,40,29],[]),([847,78],[11,14,19,2,16,13,30,28,36,25,40,29],[]),([847,86],[11,16,4,13,30,28,36,25,40,29],[]),([847,94],[16,4,19,11,13,30,28,36,25,40,29],[]),([847,102],[11,22,18,30,16,36,25,40,29],[694,695,696,697,67,164,275,372,600]),([847,110],[22,18,19,11,16,36,25,40,29,30],[698,699,700,701,68,165,276,373,601]),([847,134],[11,22,18,40,16,30,28,25,29,36],[702,703,704,705,69,166,277,374,602]),([847,142],[22,18,19,11,16,30,28,36,25,40],[706,707,708,709,710,711,712,713,70,167,278,375,603]),([847,622],[22,30,17,19,21,36,29,25,11,16],[714,715,71,168,279,376,604]),([855,58],[17,30,11,2,16,4,22,19,36,35,40,34],[716]),([855,62],[17,30,11,2,16,4,22,19,36,35,40,34],[]),([855,78],[11,14,2,16,13,22,19,36,35,40,34],[]),([855,94],[16,17,30,4,11,13,22,19,36,35,40,34],[]),([855,110],[17,22,30,18,19,25,40,11,16,36,29],[73,170,281,378,605]),([855,126],[17,30,25,11,16,40,34,36],[717,718,719,720,721,722,74,171,282,379,606]),([855,638],[17,30,36,21,40,22,25,34,11,16],[723,724,716,75,172,283,380,607]),([863,50],[30,20,21,11,2,16,4,22,28,36,35,40,34],[]),([863,54],[0,30,17,11,2,16,4,22,28,36,35,40,34,20],[574,592]),([863,62],[30,0,21,11,2,16,4,22,28,36,35,40,34],[]),([863,70],[11,14,2,16,13,22,28,36,35,40,34],[]),([863,78],[11,14,21,2,16,13,22,28,36,35,40,34],[]),([863,86],[11,16,4,13,22,28,36,35,40,34],[]),([863,94],[16,4,21,11,13,22,28,36,35,40,34],[]),([863,102],[11,22,19,16,36,25,40,34,30],[725,726,727,728,78,174,286,382,608]),([863,118],[11,30,20,36,16,22,25,40,34,35],[729,730,731,732,79,175,287,383,609]),([863,126],[30,20,21,11,16,22,25,40,34],[733,734,735,736,737,738,739,740,80,176,288,384,610]),([863,622],[22,30,17,19,20,21,25,40,29,11,16,36],[741,742,81,177,289,385,611]),([871,58],[17,36,11,2,16,4,22,19,30,21,40,38],[]),([871,62],[17,36,11,2,16,4,22,19,30,21,40,38],[]),([871,78],[11,14,2,16,13,22,19,30,21,40,38,17],[]),([871,94],[16,17,36,4,11,13,22,19,30,21,40,38],[]),([871,126],[17,30,36,20,21,34,11,16,22,19,40],[83,179,291,387,612]),([871,136],[17,40,36,11,16,22,19,30,21],[84,180,292,388,613]),([871,140],[17,36,38,11,16,22,19,30,21],[85,181,293,389,614]),([879,50],[36,25,0,11,2,16,4,30,35,40,38,17,10],[452,532]),([879,54],[0,36,17,25,11,2,16,4,30,35,40,38],[743,744,493]),([879,70],[11,14,2,16,13,22,25,30,35,40,38],[]),([879,86],[11,16,4,13,22,25,30,35,40,38],[]),([879,96],[17,22,36,11,16,30,35,40,38,25],[494,533,643,668,87,183,295,391,615]),([879,100],[17,36,19,25,11,16,30,35,40,38],[495,534,644,669,88,184,296,392,616]),([879,118],[11,30,21,32,34,16,22,25,40],[89,185,297,393,617]),([887,58],[17,40,11,2,16,4,22,19,30,21,36,38],[]),([887,62],[17,40,11,2,16,4,22,19,30,21,36,38],[]),([887,78],[11,14,2,16,13,22,19,30,21,36,38],[]),([887,94],[16,17,40,4,11,13,22,19,30,21,36,38],[]),([887,110],[17,22,40,18,19,25,11,16,30,21,36],[91,187,299,395,618]),([887,136],[17,36,40,11,16,22,19,30,21],[92,188,300,396,619]),([887,140],[17,36,40,38,11,16,22,19,30,21],[93,189,301,397,620]),([895,50],[40,27,0,11,2,16,4,29,30,34,36,38,17,10],[466,535]),([895,54],[0,40,17,34,11,2,16,4,22,29,36,38],[745,746,496]),([895,70],[11,14,2,16,13,22,29,30,34,36,38],[]),([895,86],[11,16,4,13,22,29,30,34,36,38],[]),([895,102],[11,22,19,27,25,16,30,28,36],[95,191,303,399,621]),([895,112],[17,30,40,11,16,22,29,36,38],[497,536,645,670,96,192,304,400,622]),([895,116],[17,40,21,34,11,16,22,29,36,38],[498,537,646,671,97,193,305,401,623]),([1119,50],[22,19,0,11,2,16,4,23,36,25,40,29,34],[747,503,715,742]),([1119,54],[0,22,30,11,2,16,4,19,36,25,40,29],[748]),([1119,62],[22,0,30,11,2,16,4,19,36,25,40,29],[]),([1119,70],[11,14,2,16,13,19,36,25,40,29,30],[749]),([1119,78],[11,14,22,30,2,16,13,19,36,25,40,29],[]),([1119,86],[11,16,4,13,19,36,25,40,29,30],[750]),([1119,94],[16,4,22,30,11,13,19,36,25,40,29],[]),([1119,98],[17,22,30,11,16,36,25,40,29,19],[751,752,753,754,755,756,757,758,759,760,761,762,763,764,714,741,539,648,673,100,195,308,403,624]),([1119,102],[11,22,19,23,16,36,25,40,29],[540,649,674,101,196,309,404,625]),([1119,106],[17,22,30,11,16,36,25,40,29],[765,766,767,768,102,197,310,405,626]),([1151,50],[22,19,0,11,2,16,4,26,30,28,36,25,34],[769,508]),([1151,54],[0,22,40,11,2,16,4,19,30,28,36,25],[770,569]),([1151,70],[11,14,2,16,13,19,30,28,36,25,40],[771]),([1151,86],[11,16,4,13,19,30,28,36,25,40],[772]),([1151,98],[17,22,40,11,16,30,28,36,25,34],[773,774,775,776,104,199,312,407,627]),([1151,102],[11,22,19,40,26,16,30,28,36,25],[692,105,200,313,408,628]),([1151,128],[22,36,34,40,11,16,19],[570,693,106,201,314,409,509,542,629,651,676]),([1151,132],[22,36,25,40,11,16,19,30,28],[107,202,315,410,510,543,630,652,677]),([1391,50],[30,21,0,11,2,16,4,31,22,25,40,34],[777,515]),([1391,54],[0,30,36,11,2,16,4,21,22,25,40,34],[778,593]),([1391,70],[11,14,2,16,13,21,22,25,40,34],[779]),([1391,86],[11,16,4,13,21,22,25,40,34],[780]),([1391,98],[17,30,36,11,16,22,25,40,34],[781,782,783,784,109,204,317,412,631]),([1391,102],[11,30,21,36,31,16,22,25,40,34],[723,110,205,318,413,632]),([1391,128],[30,36,40,25,11,16,21],[594,724,111,206,319,414,516,545,633,654,679]),([1391,132],[30,36,31,11,16,21,22,25],[112,207,320,415,517,546,634,655,680])],[([23,56,839],[11,22,17,16,1,14,30,36,25,40],[0,1,2]),([23,56,847],[11,22,17,16,1,30,36,25,40,14],[3,4,5,6,7]),([23,56,855],[11,17,30,16,1,14,22,36,40,34],[8,9,10]),([23,56,863],[11,30,17,16,1,22,36,40,34,14],[11,4,12,13,14]),([23,56,871],[11,17,36,16,1,14,22,25,30,40,38],[15,16,17]),([23,56,879],[11,36,17,16,1,25,30,40,38,14],[18,19,20]),([23,56,887],[11,17,40,16,1,14,22,30,34,36,38],[21,22,23]),([23,56,895],[11,40,17,16,1,22,34,36,38,14],[24,25,26]),([23,56,1119],[11,30,22,16,1,36,25,40,34,14],[27,28,29,4,7,14]),([23,56,1135],[11,36,22,16,1,24,25,38,14],[]),([23,56,1151],[11,40,22,16,1,34,36,25,38,14],[30,31,32,33,2]),([23,56,1391],[11,36,30,16,1,25,40,34,38,14],[34,35,36,37,10]),([23,56,1407],[11,40,30,16,1,33,34,38,14],[]),([23,56,1663],[11,40,36,16,1,37,25,14],[]),([23,60,839],[11,17,22,1,30,36,25,40],[38,39,40]),([23,60,847],[11,22,17,1,30,36,25,40],[41,42,43,44,45]),([23,60,855],[11,17,30,1,22,36,40,34],[46,47,48]),([23,60,863],[11,30,17,1,22,36,40,34],[49,42,50,51,52]),([23,60,871],[11,17,36,1,22,25,30,40,38],[53,54,55]),([23,60,879],[11,36,17,1,25,30,40,38],[56,57,58]),([23,60,887],[11,17,40,1,22,30,34,36,38],[59,60,61]),([23,60,895],[11,40,17,1,22,34,36,38],[62,63,64]),([23,60,1119],[11,30,22,1,36,25,40,34],[65,66,67,42,45,52]),([23,60,1135],[11,36,22,1,24,25,38],[]),([23,60,1151],[11,40,22,1,34,36,25,38],[68,69,70,71,40]),([23,60,1391],[11,36,30,1,25,40,34,38],[72,73,74,75,48]),([23,60,1407],[11,40,30,1,33,34,38],[]),([23,60,1663],[11,40,36,1,37,25],[]),([23,74,94],[11,17,1,16,4,30,18,19],[]),([23,74,110],[11,17,1,16,4,22,19,36,20,21],[]),([23,74,126],[11,17,1,16,4,22,19,30,21,40,38],[]),([23,74,142],[11,17,1,16,4,22,19,30,21,36,38],[]),([23,74,1935],[11,17,37,25,36,14],[]),([23,78,86],[0,11,1,14,17,16,4,30,19,36,25,40,22],[76,77]),([23,78,102],[0,11,1,14,17,16,4,22,21,36,40,34,30],[78,79]),([23,78,118],[0,11,1,14,17,16,4,22,25,30,40,38,36],[80]),([23,78,134],[0,11,1,14,17,16,4,22,34,36,38,40],[81]),([23,78,351],[11,14,22,19],[]),([23,78,367],[11,14,30,21],[]),([23,78,383],[11,14,36,25],[82,83]),([23,78,399],[11,14,40,34],[84,85]),([23,78,1391],[11,1,19,22],[86,87,88]),([23,78,1407],[11,24,19,22],[]),([23,78,1423],[11,1,19,22],[89,90,91]),([23,78,1663],[11,1,21,30],[92,93,94]),([23,78,1679],[11,33,21,30],[]),([23,78,1935],[11,37,25,36],[]),([23,94,82],[11,17,22,1,14,4,30,28,36,25,40,29],[95]),([23,94,86],[0,11,1,14,17,16,4,30,28,36,25,40,29],[]),([23,94,102],[0,11,1,14,22,16,4,19,28,36,25,40,29],[96]),([23,94,134],[0,11,1,14,22,16,4,19,29,30,28,25],[97]),([23,110,82],[11,17,30,1,14,4,22,28,36,35,40,34],[98]),([23,110,86],[0,11,1,14,17,16,4,22,28,36,35,40,34],[]),([23,110,102],[0,11,1,14,22,16,4,21,28,36,25,40,34],[99]),([23,110,118],[0,11,1,14,30,16,4,21,25,40,34],[100]),([23,126,82],[11,17,36,1,16,4,22,25,30,35,40,38],[]),([23,126,86],[0,11,1,14,17,16,4,22,25,30,35,40,38],[]),([23,126,118],[0,11,1,14,30,16,4,35,32],[]),([23,142,82],[11,17,40,1,16,4,22,29,30,34,36,38],[]),([23,142,86],[0,11,1,14,17,16,4,22,29,30,34,36,38],[]),([23,142,102],[0,11,1,14,22,16,4,29,27],[]),([23,1111,60],[14,17,22,11,16,4,30,21,36,25,40,29],[]),([23,1111,126],[11,14,20,21],[0,38]),([23,1111,158],[11,14,27],[101,102,103,1,39]),([23,1111,670],[40,11],[104,105,2,40]),([23,1119,52],[14,22,11,0,16,1,4,30,28,36,25,40,29],[]),([23,1119,60],[11,1,19,16,4,30,28,36,25,40,29],[]),([23,1119,118],[11,14,18],[106,3,41]),([23,1119,126],[11,14,19],[107,4,42]),([23,1119,150],[11,14,18],[108,5,43]),([23,1119,158],[11,14,19],[109,110,111,112,113,6,44]),([23,1119,638],[30,11],[114,7,45]),([23,1127,60],[14,17,30,11,16,4,22,19,36,35,40,34],[]),([23,1127,126],[11,14,18,19],[8,46]),([23,1127,142],[11,14,25],[115,116,117,9,47]),([23,1127,654],[36,11],[118,119,10,48]),([23,1135,52],[14,30,11,0,16,1,4,22,28,36,35,40,34],[]),([23,1135,60],[11,1,21,16,4,22,28,36,35,40,34],[]),([23,1135,118],[11,14,19],[120,11,49]),([23,1135,134],[11,14,20],[121,12,50]),([23,1135,142],[11,14,21],[122,123,124,125,126,13,51]),([23,1135,638],[22,11],[127,14,52]),([23,1143,60],[14,17,36,11,16,4,22,19,30,21,40,38],[]),([23,1143,142],[11,14,20,21],[15,53]),([23,1143,152],[17,40,14,36,11,16,4,22,19,30,21,13],[16,54]),([23,1143,156],[14,38,17,11,16,4,22,19,30,21,13],[17,55]),([23,1151,52],[14,36,11,0,16,1,4,22,25,30,35,40,38],[]),([23,1151,112],[22,14,17,11,36,25,16,4,30,35,40,38,13],[82,18,56]),([23,1151,116],[14,19,25,11,16,4,30,35,40,38,13],[83,19,57]),([23,1151,134],[11,14,21,32],[20,58]),([23,1159,60],[14,17,40,11,16,4,22,19,30,21,36,38],[]),([23,1159,126],[11,14,18,19],[21,59]),([23,1159,152],[17,36,14,40,11,16,4,22,19,30,21,13],[22,60]),([23,1159,156],[14,38,17,11,16,4,22,19,30,21,13],[23,61]),([23,1167,52],[14,40,11,0,16,1,4,22,29,30,34,36,38],[]),([23,1167,118],[11,14,19,27],[24,62]),([23,1167,128],[30,14,17,11,40,34,16,4,22,29,36,38,13],[84,25,63]),([23,1167,132],[14,21,34,11,16,4,22,29,36,38,13],[85,26,64]),([23,1391,52],[14,22,11,0,16,1,4,19,36,25,40,29],[128]),([23,1391,60],[11,1,22,30,16,4,19,36,25,40,29],[]),([23,1391,114],[11,30,22,14,17],[129,130,131,132,133,134,135,114,127,87,27,65]),([23,1391,118],[11,14,23,19],[88,28,66]),([23,1391,122],[11,14,17],[136,29,67]),([23,1423,52],[14,22,11,0,16,1,4,19,30,28,36,25],[137]),([23,1423,114],[11,22,14,17,34],[138,30,68]),([23,1423,118],[11,40,14,26,19],[104,31,69]),([23,1423,144],[22,36,2,34,40,16,4,19,11,13],[105,32,70,90]),([23,1423,148],[14,25,40,11,16,4,19,30,28,13],[33,71,91]),([23,1663,52],[14,30,11,0,16,1,4,21,22,25,40,34],[139]),([23,1663,114],[11,30,14,17,25],[140,34,72]),([23,1663,118],[11,36,14,31,21],[118,35,73]),([23,1663,144],[30,36,14,40,2,25,16,4,21,11,13],[119,36,74,93]),([23,1663,148],[14,31,11,16,4,21,22,25,13],[37,75,94]),([31,66,94],[0,17,11,16,4,30,18,19],[]),([31,66,110],[0,17,11,16,4,22,19,36,20,21],[]),([31,66,126],[0,17,11,16,4,25,30,21,40,38],[141,142]),([31,66,142],[0,17,11,16,4,22,19,34,36,38],[143,144]),([31,66,1935],[0,17,37,25,36],[]),([31,70,86],[0,19,11,16,4,30,36,25,40],[145,146]),([31,70,94],[0,8,17,11,16,4,30,19,36,25,40,22],[147,148]),([31,70,102],[0,5,8,21,16,4,22,36,40,34],[149,150]),([31,70,110],[0,5,30,11,16,4,22,36,40,34,21],[151,152]),([31,70,118],[0,5,8,6,16,4,22,25,30,40,38],[153,154,155]),([31,70,126],[0,5,36,11,16,4,22,25,30,40,38],[156]),([31,70,134],[0,5,8,7,16,4,22,30,34,36,38],[157,158,159]),([31,70,142],[0,5,40,11,16,4,22,30,34,36,38],[160]),([31,70,351],[0,22,5],[]),([31,70,367],[0,30,5],[]),([31,70,383],[0,36,5],[161,162]),([31,70,399],[0,40,5],[163,164]),([31,70,1391],[0,19,22],[165,166]),([31,70,1407],[0,24,19,22],[]),([31,70,1423],[0,19,22],[167,168,169,170]),([31,70,1663],[0,21,30],[171,172,173,174]),([31,70,1679],[0,33,21,30],[]),([31,70,1935],[0,37,25,36],[]),([31,86,82],[0,17,22,11,16,4,30,28,36,25,40,29],[]),([31,86,90],[0,17,22,14,4,30,28,36,25,40,29,19],[175,176,177,178,179,180,181]),([31,86,94],[0,8,17,11,4,30,19,28,36,25,40,29],[]),([31,86,102],[0,8,30,22,16,4,19,36,25,40,29],[182,183]),([31,86,110],[0,8,22,11,16,4,19,28,36,25,40,29],[184]),([31,86,134],[0,8,40,22,16,4,19,30,28,36,25],[185,186]),([31,86,142],[0,8,22,11,16,4,19,27,30,28,25],[187,188,189]),([31,86,350],[0,22,17,11,4,36,29,25,28],[181]),([31,86,398],[0,22,40,11,4,19,36,30,25,28],[190]),([31,102,82],[0,17,30,11,16,4,22,28,36,35,40,34],[]),([31,102,90],[0,17,30,14,4,22,28,36,35,40,34,21],[191,192,193,194,195,196,197]),([31,102,94],[0,8,17,11,4,22,21,28,36,35,40,34],[]),([31,102,110],[0,8,22,11,16,4,21,28,36,25,40,34,30],[198]),([31,102,118],[0,8,36,30,16,4,21,22,25,40,34],[199,200]),([31,102,126],[0,8,30,11,16,4,21,25,40,34],[201,202,203]),([31,102,350],[0,30,17,11,4,35,40,34,28],[197]),([31,102,382],[0,30,36,11,4,21,40,22,25,34],[204]),([31,118,90],[0,17,36,11,16,4,22,25,30,35,40,38],[]),([31,118,94],[0,6,8,11,4,22,25,30,35,38],[]),([31,118,126],[0,6,30,11,16,4,32],[]),([31,134,90],[0,17,40,11,16,4,22,29,30,34,36,38],[]),([31,134,94],[0,7,8,11,4,22,29,34,38],[]),([31,134,110],[0,7,22,11,16,4,27],[]),([31,1111,56],[17,0,22,11,16,4,30,21,36,25,40,29],[205]),([31,1111,126],[0,20,21,11],[]),([31,1111,158],[0,27,40,11],[206,207,208]),([31,1111,670],[40,17,11],[209,210,205]),([31,1119,48],[0,22,11,16,4,30,18,28,36,25,40,29],[]),([31,1119,118],[0,18,11],[211]),([31,1119,126],[0,19,11],[212]),([31,1119,150],[0,18,29,11],[213]),([31,1119,158],[0,19,22,11],[214,215,216,217,218]),([31,1119,638],[30,19,11],[219,220]),([31,1127,56],[17,0,30,11,16,4,22,19,36,35,40,34],[221]),([31,1127,126],[0,18,19,11],[]),([31,1127,142],[0,25,36,11],[222,223,224]),([31,1127,654],[36,17,11],[225,226,221]),([31,1135,48],[0,30,11,16,4,22,20,28,36,35,40,34],[]),([31,1135,118],[0,19,11],[227]),([31,1135,134],[0,20,35,11],[228]),([31,1135,142],[0,21,30,11],[229,230,231,232,233]),([31,1135,638],[22,19,11],[234,235]),([31,1143,56],[17,0,36,11,16,4,22,19,30,21,40,38],[]),([31,1143,142],[0,20,21,11],[]),([31,1143,152],[17,40,36,0,11,16,4,22,19,30,21],[]),([31,1143,156],[38,17,0,11,16,4,22,19,30,21],[]),([31,1151,48],[0,36,11,16,4,22,25,30,35,40,38],[]),([31,1151,112],[22,17,0,36,25,11,16,4,30,35,40,38],[161]),([31,1151,116],[19,25,0,11,16,4,30,35,40,38],[162]),([31,1151,134],[0,21,32,11],[]),([31,1159,56],[17,0,40,11,16,4,22,19,30,21,36,38],[]),([31,1159,126],[0,18,19,11],[]),([31,1159,152],[17,36,40,0,11,16,4,22,19,30,21],[]),([31,1159,156],[38,17,0,11,16,4,22,19,30,21],[]),([31,1167,48],[0,40,11,16,4,22,29,30,34,36,38],[]),([31,1167,118],[0,19,27,11],[]),([31,1167,128],[30,17,0,40,34,11,16,4,22,29,36,38],[163]),([31,1167,132],[21,34,0,11,16,4,22,29,36,38],[164]),([31,1391,48],[0,22,11,16,4,19,23,36,25,40,29,34],[236,220,235]),([31,1391,114],[0,30,22,17,11,14,4],[237,238,239,240,241,242,219,234]),([31,1391,118],[0,23,19,11],[]),([31,1391,122],[0,17,11],[243]),([31,1423,48],[0,22,11,16,4,19,26,30,28,36,25,34],[244]),([31,1423,114],[0,22,17,34,11],[245]),([31,1423,118],[0,40,26,19,11],[209]),([31,1423,144],[22,36,0,34,40,11,16,4,19],[190,210,169]),([31,1423,148],[25,40,0,11,16,4,19,30,28],[170]),([31,1663,48],[0,30,11,16,4,21,31,22,25,40,34],[246]),([31,1663,114],[0,30,17,25,11],[247]),([31,1663,118],[0,36,31,21,11],[225]),([31,1663,144],[30,36,40,0,25,11,16,4,21],[204,226,173]),([31,1663,148],[31,0,11,16,4,21,22,25],[174]),([39,56,839],[11,17,22,4,16,30,36,25,40],[248,249,250]),([39,56,847],[11,22,17,4,30,36,25,40,16],[251,252,253,254,255]),([39,56,855],[11,17,30,4,16,22,36,40,34],[256,257,258]),([39,56,863],[11,30,17,4,22,36,40,34,16],[259,252,260,261,262]),([39,56,871],[11,17,36,4,16,22,25,30,40,38],[263,264,265]),([39,56,879],[11,36,17,4,25,30,40,38,16],[266,267,268]),([39,56,887],[11,17,40,4,16,22,30,34,36,38],[269,270,271]),([39,56,895],[11,40,17,4,22,34,36,38,16],[272,273,274]),([39,56,1119],[11,30,22,4,36,25,40,34,16],[275,276,277,252,255,262]),([39,56,1135],[11,36,22,4,24,25,38,16],[]),([39,56,1151],[11,40,22,4,34,36,25,38,16],[278,279,280,281,250]),([39,56,1391],[11,36,30,4,25,40,34,38,16],[282,283,284,285,258]),([39,56,1407],[11,40,30,4,33,34,38,16],[]),([39,56,1663],[11,40,36,4,37,25,16],[]),([39,60,839],[16,17,22,2,30,36,25,40],[286,287,288]),([39,60,847],[16,22,17,2,30,36,25,40],[289,290,291,292,293]),([39,60,855],[16,17,30,2,22,36,40,34],[294,295,296]),([39,60,863],[16,30,17,2,22,36,40,34],[297,290,298,299,300]),([39,60,871],[16,17,36,2,22,25,30,40,38],[301,302,303]),([39,60,879],[16,36,17,2,25,30,40,38],[304,305,306]),([39,60,887],[16,17,40,2,22,30,34,36,38],[307,308,309]),([39,60,895],[16,40,17,2,22,34,36,38],[310,311,312]),([39,60,1119],[16,30,22,2,36,25,40,34],[313,314,315,290,293,300]),([39,60,1135],[16,36,22,2,24,25,38],[]),([39,60,1151],[16,40,22,2,34,36,25,38],[316,317,318,319,288]),([39,60,1391],[16,36,30,2,25,40,34,38],[320,321,322,323,296]),([39,60,1407],[16,40,30,2,33,34,38],[]),([39,60,1663],[16,40,36,2,37,25],[]),([39,74,94],[16,17,4,11,2,30,18,19],[]),([39,74,110],[16,17,4,11,2,22,19,36,20,21],[]),([39,74,126],[16,17,4,11,2,22,19,30,21,40,38],[]),([39,74,142],[16,17,4,11,2,22,19,30,21,36,38],[]),([39,74,1935],[16,17,37,25,36,4],[]),([39,78,86],[0,16,19,4,11,2,30,36,25,40,22],[324,325]),([39,78,102],[0,16,3,17,4,11,2,22,21,36,40,34,30],[326,327]),([39,78,118],[0,16,3,17,4,11,2,22,25,30,40,38,36],[328]),([39,78,134],[0,16,3,17,4,11,2,22,34,36,38,40],[329]),([39,78,351],[16,22,4,19],[]),([39,78,367],[16,30,4,21],[]),([39,78,383],[16,36,4,25],[330,331]),([39,78,399],[16,40,4,34],[332,333]),([39,78,1391],[16,3,19,22],[334,335,336]),([39,78,1407],[16,24,19,22],[]),([39,78,1423],[16,3,19,22],[337,338,339]),([39,78,1663],[16,3,21,30],[340,341,342]),([39,78,1679],[16,33,21,30],[]),([39,78,1935],[16,37,25,36],[]),([39,94,82],[16,17,22,3,4,2,30,28,36,25,40,29],[343]),([39,94,86],[0,16,3,22,11,2,30,28,36,25,40,29],[]),([39,94,102],[0,16,3,22,11,2,19,28,36,25,40,29,4],[344]),([39,94,134],[0,16,3,22,11,2,19,27,30,28,25],[345]),([39,110,82],[16,17,30,3,4,2,22,28,36,35,40,34],[346]),([39,110,86],[0,16,3,30,11,2,22,28,36,35,40,34],[]),([39,110,102],[0,16,3,22,30,11,2,21,28,36,25,40,34,4],[347]),([39,110,118],[0,16,3,30,11,2,21,25,40,34],[348]),([39,126,82],[16,17,36,3,11,2,22,25,30,35,40,38],[]),([39,126,86],[0,16,3,36,11,2,22,25,30,35,40,38],[]),([39,126,118],[0,16,3,30,36,11,2,35,32],[]),([39,142,82],[16,17,40,3,11,2,22,29,30,34,36,38],[]),([39,142,86],[0,16,3,40,11,2,22,29,30,34,36,38],[]),([39,142,102],[0,16,3,22,40,11,2,29,27],[]),([39,1111,60],[17,22,16,11,2,30,21,36,25,40,29],[]),([39,1111,126],[16,4,20,21],[248,286]),([39,1111,158],[16,4,27],[349,350,351,249,287]),([39,1111,670],[40,16],[352,353,250,288]),([39,1119,52],[17,22,16,0,11,2,30,3,28,36,25,40,29,4],[]),([39,1119,60],[16,3,19,11,2,30,28,36,25,40,29],[]),([39,1119,118],[16,4,18],[354,251,289]),([39,1119,126],[16,4,19],[355,252,290]),([39,1119,150],[16,4,18],[356,253,291]),([39,1119,158],[16,4,19],[357,358,359,360,361,254,292]),([39,1119,638],[30,16],[362,255,293]),([39,1127,60],[17,30,16,11,2,22,19,36,35,40,34],[]),([39,1127,126],[16,4,18,19],[256,294]),([39,1127,142],[16,4,25],[363,364,365,257,295]),([39,1127,654],[36,16],[366,367,258,296]),([39,1135,52],[17,30,16,0,11,2,22,3,28,36,35,40,34,4],[]),([39,1135,60],[16,3,21,11,2,22,28,36,35,40,34],[]),([39,1135,118],[16,4,19],[368,259,297]),([39,1135,134],[16,4,20],[369,260,298]),([39,1135,142],[16,4,21],[370,371,372,373,374,261,299]),([39,1135,638],[22,16],[375,262,300]),([39,1143,60],[17,36,16,11,2,22,19,30,21,40,38],[]),([39,1143,142],[16,4,20,21],[263,301]),([39,1143,152],[17,40,36,16,0,11,2,3,22,4,19,30,21,13],[264,302]),([39,1143,156],[4,38,17,11,2,22,19,30,21,16,13],[265,303]),([39,1151,52],[17,36,16,0,11,2,3,22,25,30,35,40,38,4],[]),([39,1151,112],[22,17,4,16,36,25,11,2,30,35,40,38,13],[330,266,304]),([39,1151,116],[4,19,25,16,11,2,30,35,40,38,13],[331,267,305]),([39,1151,134],[16,4,21,32],[268,306]),([39,1159,60],[17,40,16,11,2,22,19,30,21,36,38],[]),([39,1159,126],[16,4,18,19],[269,307]),([39,1159,152],[17,36,40,16,0,11,2,3,22,4,19,30,21,13],[270,308]),([39,1159,156],[4,38,17,11,2,22,19,30,21,16,13],[271,309]),([39,1167,52],[17,40,16,0,11,2,22,3,29,30,34,36,38,4],[]),([39,1167,118],[16,4,19,27],[272,310]),([39,1167,128],[30,17,4,16,40,34,11,2,22,29,36,38,13],[332,273,311]),([39,1167,132],[4,21,34,16,11,2,22,29,36,38,13],[333,274,312]),([39,1391,52],[22,30,16,0,11,2,3,19,36,25,40,29],[376]),([39,1391,60],[16,3,22,30,11,2,19,36,25,40,29],[]),([39,1391,114],[16,30,22,17,4],[377,378,379,380,381,382,383,362,375,335,275,313]),([39,1391,118],[16,4,23,19],[336,276,314]),([39,1391,122],[16,17,4],[384,277,315]),([39,1423,52],[22,40,16,0,11,2,3,19,30,28,36,25],[385]),([39,1423,114],[16,22,17,4,34],[386,278,316]),([39,1423,118],[16,40,4,26,19],[352,279,317]),([39,1423,144],[22,36,4,34,40,11,2,19,16,13],[353,280,318,338]),([39,1423,148],[4,25,40,11,2,19,30,28,16,13],[281,319,339]),([39,1663,52],[30,36,16,0,11,2,3,21,22,25,40,34],[387]),([39,1663,114],[16,30,17,4,25],[388,282,320]),([39,1663,118],[16,36,4,31,21],[366,283,321]),([39,1663,144],[30,36,40,4,25,11,2,21,16,13],[367,284,322,341]),([39,1663,148],[4,31,11,2,21,22,25,16,13],[285,323,342]),([47,66,94],[0,17,16,11,14,30,18,19],[]),([47,66,110],[0,17,16,11,14,22,19,36,20,21],[]),([47,66,126],[0,17,16,11,14,25,30,21,40,38],[141,389]),([47,66,142],[0,17,16,11,14,22,19,34,36,38],[143,390]),([47,66,1935],[0,17,37,25,36],[]),([47,70,86],[0,5,19,16,11,14,30,36,25,40],[391,392]),([47,70,94],[0,5,22,16,11,14,30,36,25,40,19],[393,394]),([47,70,102],[0,5,9,21,11,14,22,36,40,34],[395,396]),([47,70,110],[0,5,30,16,11,14,22,36,40,34,21],[397,398]),([47,70,118],[0,5,6,16,11,14,22,9,25,30,40,38],[399,400,401]),([47,70,126],[0,5,36,16,11,14,22,25,30,40,38],[402]),([47,70,134],[0,5,7,16,11,14,22,9,30,34,36,38],[403,404,405]),([47,70,142],[0,5,40,16,11,14,22,30,34,36,38],[406]),([47,70,351],[0,22,5],[]),([47,70,367],[0,30,5],[]),([47,70,383],[0,36,5],[407,408]),([47,70,399],[0,40,5],[409,410]),([47,70,1391],[0,19,22],[411,412]),([47,70,1407],[0,24,19,22],[]),([47,70,1423],[0,19,22],[413,414,415,416]),([47,70,1663],[0,21,30],[417,418,419,420]),([47,70,1679],[0,33,21,30],[]),([47,70,1935],[0,37,25,36],[]),([47,86,82],[0,17,22,16,11,14,30,28,36,25,40,29],[]),([47,86,90],[0,17,22,4,2,30,28,36,25,40,29,19],[175,421,422,423,424,425,426]),([47,86,94],[0,9,17,16,14,11,30,19,28,36,25,40,29],[]),([47,86,102],[0,9,30,22,11,14,19,36,25,40,29],[427,428]),([47,86,110],[0,9,22,16,11,14,19,28,36,25,40,29],[429]),([47,86,134],[0,9,40,22,11,14,19,30,28,36,25],[430,431]),([47,86,142],[0,9,22,16,11,14,19,27,30,28,25],[432,433,434]),([47,86,350],[0,22,17,16,14,36,29,25,28],[426]),([47,86,398],[0,22,40,16,14,19,36,30,25,28],[435]),([47,102,82],[0,17,30,16,11,14,22,28,36,35,40,34],[]),([47,102,90],[0,17,30,4,2,22,28,36,35,40,34,21],[191,436,437,438,439,440,441]),([47,102,94],[0,9,17,16,14,11,22,21,28,36,35,40,34],[]),([47,102,110],[0,9,22,16,11,14,21,28,36,25,40,34,30],[442]),([47,102,118],[0,9,36,30,11,14,21,22,25,40,34],[443,444]),([47,102,126],[0,9,30,16,11,14,21,25,40,34],[445,446,447]),([47,102,350],[0,30,17,16,14,35,40,34,28],[441]),([47,102,382],[0,30,36,16,14,21,40,22,25,34],[448]),([47,118,90],[0,17,36,16,11,14,22,25,30,35,40,38],[]),([47,118,94],[0,6,9,16,14,22,25,30,35,38],[]),([47,118,126],[0,6,30,16,11,14,32],[]),([47,134,90],[0,17,40,16,11,14,22,29,30,34,36,38],[]),([47,134,94],[0,7,9,16,14,22,29,34,38],[]),([47,134,110],[0,7,22,16,11,14,27],[]),([47,1111,56],[17,0,22,16,11,14,30,21,36,25,40,29],[449]),([47,1111,126],[0,20,21,16],[]),([47,1111,158],[0,27,40,16],[450,451,452]),([47,1111,670],[40,17,16],[453,454,449]),([47,1119,48],[0,22,16,11,14,30,18,28,36,25,40,29],[]),([47,1119,118],[0,18,16],[455]),([47,1119,126],[0,19,16],[456]),([47,1119,150],[0,18,29,16],[457]),([47,1119,158],[0,19,22,16],[458,459,460,461,462]),([47,1119,638],[30,19,16],[463,464]),([47,1127,56],[17,0,30,16,11,14,22,19,36,35,40,34],[465]),([47,1127,126],[0,18,19,16],[]),([47,1127,142],[0,25,36,16],[466,467,468]),([47,1127,654],[36,17,16],[469,470,465]),([47,1135,48],[0,30,16,11,14,22,20,28,36,35,40,34],[]),([47,1135,118],[0,19,16],[471]),([47,1135,134],[0,20,35,16],[472]),([47,1135,142],[0,21,30,16],[473,474,475,476,477]),([47,1135,638],[22,19,16],[478,479]),([47,1143,56],[17,0,36,16,11,14,22,19,30,21,40,38],[]),([47,1143,142],[0,20,21,16],[]),([47,1143,152],[17,40,36,0,16,11,14,22,19,30,21],[]),([47,1143,156],[38,17,0,16,11,14,22,19,30,21],[]),([47,1151,48],[0,36,16,11,14,22,25,30,35,40,38],[]),([47,1151,112],[22,17,0,36,25,16,11,14,30,35,40,38],[407]),([47,1151,116],[19,25,0,16,11,14,30,35,40,38],[408]),([47,1151,134],[0,21,32,16],[]),([47,1159,56],[17,0,40,16,11,14,22,19,30,21,36,38],[]),([47,1159,126],[0,18,19,16],[]),([47,1159,152],[17,36,40,0,16,11,14,22,19,30,21],[]),([47,1159,156],[38,17,0,16,11,14,22,19,30,21],[]),([47,1167,48],[0,40,16,11,14,22,29,30,34,36,38],[]),([47,1167,118],[0,19,27,16],[]),([47,1167,128],[30,17,0,40,34,16,11,14,22,29,36,38],[409]),([47,1167,132],[21,34,0,16,11,14,22,29,36,38],[410]),([47,1391,48],[0,22,16,11,14,19,23,36,25,40,29,34],[480,464,479]),([47,1391,114],[0,30,22,17,16,4,2],[481,482,483,484,485,486,463,478]),([47,1391,118],[0,23,19,16],[]),([47,1391,122],[0,17,16],[487]),([47,1423,48],[0,22,16,11,14,19,26,30,28,36,25,34],[488]),([47,1423,114],[0,22,17,34,16],[489]),([47,1423,118],[0,40,26,19,16],[453]),([47,1423,144],[22,36,0,34,40,16,11,14,19],[435,454,415]),([47,1423,148],[25,40,0,16,11,14,19,30,28],[416]),([47,1663,48],[0,30,16,11,14,21,31,22,25,40,34],[490]),([47,1663,114],[0,30,17,25,16],[491]),([47,1663,118],[0,36,31,21,16],[469]),([47,1663,144],[30,36,40,0,25,16,11,14,21],[448,470,419]),([47,1663,148],[31,0,16,11,14,21,22,25],[420]),([51,26,118],[0,5,8,17,16,4,22,19,30,21,40,38],[492,493]),([51,26,126],[0,5,36,11,2,16,4,22,19,30,21,40,38],[]),([51,26,134],[0,5,8,17,16,4,22,19,30,21,36,38],[494,495]),([51,26,142],[0,5,40,11,2,16,4,22,19,30,21,36,38],[]),([51,26,1935],[0,37,25,36],[]),([51,126,96],[17,22,36,21,40,11,2,16,4,30,38],[]),([51,126,100],[17,22,36,19,11,2,16,4,30,21,40,38],[]),([51,142,112],[17,30,40,19,36,11,2,16,4,22,38],[]),([51,142,116],[17,30,40,21,11,2,16,4,22,19,36,38],[]),([51,300,20],[11,2,16,4,22,19,30,21,36,40],[496,497,498,499,500]),([51,300,1663],[0,40,36,17,11,2,16,4,22,19,30,21],[500]),([51,375,76],[0,36,6,17,2,4,8],[]),([51,391,76],[0,40,7,17,2,4,8],[]),([55,86,110],[22,8,0,17,30,19,2,16,4,36,25,40,29],[]),([55,86,142],[22,8,0,17,40,19,2,16,4,30,28,25,36],[]),([55,87,76],[22,17,2,4,19,30,8,29,28],[]),([55,87,126],[22,30,8,19],[]),([55,87,158],[22,40,8,19],[]),([55,94,102],[0,22,5,20,19,11,2,16,4,36,21,25,40,29],[]),([55,94,134],[0,22,5,19,11,2,16,4,30,27,28,25],[501,502,503]),([55,95,118],[22,30,20,5,19],[]),([55,95,150],[22,40,5,19],[504,505,506]),([55,102,110],[22,8,30,19,2,16,4,36,25,40,34],[]),([55,102,126],[30,8,0,17,36,21,2,16,4,22,25,40,34],[]),([55,103,76],[30,17,2,4,21,22,8,35,28],[]),([55,103,126],[22,30,8,19],[]),([55,103,142],[30,36,8,21],[]),([55,110,102],[0,22,5,30,18,19,11,2,16,4,36,25,40,34],[]),([55,110,118],[0,30,5,21,11,2,16,4,22,25,40,34],[507,508,509]),([55,111,118],[22,30,18,5,19],[]),([55,111,134],[30,36,5,21],[510,511,512]),([55,118,42],[0,8,16,4,22,25,30,35,40,38],[]),([55,118,62],[17,6,11,2,16,4,22,19,30,21,40,38],[]),([55,118,104],[22,36,17,8,0,2,16,4,30,35,40,38],[]),([55,118,108],[22,36,8,0,19,2,16,4,30,25,35,40,38],[]),([55,118,126],[30,8,36,21,2,16,4,22,25,40,32],[]),([55,119,56],[17,36,0,8,25,35,4],[]),([55,119,76],[36,17,2,4,25,8,6],[]),([55,119,120],[22,36,17,0,11,2,16,4,30,8,35,40,38],[513]),([55,119,124],[36,22,8,19,0,16,4,30,35,40,38],[514]),([55,119,142],[30,36,8,21],[]),([55,119,840],[0,8,36,16,4,22,19,30,21,40,38],[515,516,513,514]),([55,126,118],[0,30,5,36,20,21,11,2,16,4,22,25,40,32],[]),([55,127,134],[30,36,5,21],[]),([55,127,840],[0,5,36,11,2,16,4,22,19,30,21,40,38],[517]),([55,134,42],[0,8,16,4,22,29,30,34,36,38],[]),([55,134,62],[17,7,11,2,16,4,22,10],[]),([55,134,110],[22,8,40,19,2,16,4,30,27],[]),([55,134,120],[30,40,17,8,0,2,16,4,22,29,36,38],[]),([55,134,124],[30,40,8,0,21,2,16,4,22,29,34,36,38],[]),([55,135,56],[17,40,0,8,29,34,4],[]),([55,135,76],[40,17,2,4,34,8,7],[]),([55,135,126],[22,40,8,19],[]),([55,135,136],[30,40,17,0,11,2,16,4,22,8,29,36,38],[518]),([55,135,140],[40,30,8,21,0,16,4,22,29,36,38],[519]),([55,135,840],[0,8,40,16,4,22,19,30,21,36,38],[520,521,518,519]),([55,142,102],[0,22,5,40,18,19,11,2,16,4,30,27],[]),([55,143,118],[22,40,5,19],[]),([55,143,840],[0,5,40,11,2,16,4,22,19,30,21,36,38],[522]),([55,296,30],[0,11,2,16,4,22,10,5,19,30,21,36,40],[516,517,521,522,523]),([55,296,1663],[0,40,36,37,25],[500,523]),([55,342,56],[17,22,36,19,11,2,16,4,30,8,5,21,40,25],[524]),([55,342,110],[22,8,20,19,0,2,4],[]),([55,343,72],[17,0,5,2,4,22,30,8,36,19],[]),([55,343,126],[0,22,20,30,8],[]),([55,343,158],[0,22,40,19],[525,526,527]),([55,350,102],[0,22,5,30,19,2,4,21],[]),([55,358,56],[17,30,21,11,2,16,4,22,8,5,36,19,40,34],[528]),([55,358,110],[22,8,0,18,30,19,21,2,4],[]),([55,359,72],[17,0,5,2,4,30,22,8,21],[]),([55,359,126],[0,22,30,18,8],[]),([55,359,142],[0,30,36,21],[529,530,531]),([55,366,102],[0,30,5,22,19,2,4],[]),([55,375,72],[17,0,5,2,4,36,8],[]),([55,375,142],[0,36,20,8],[]),([55,391,72],[17,0,5,2,4,40,8],[]),([55,391,126],[0,40,18,8],[]),([55,639,68],[0,17,5,19,21,36,2,4,25,38],[532]),([55,639,112],[17,22,0,2,4,36,21,40,11,16,30,38],[]),([55,639,116],[36,19,0,2,4,11,16,30,21,40,38],[]),([55,655,68],[0,17,5,19,21,40,2,4,34,38],[533]),([55,655,128],[17,30,0,2,4,40,19,36,11,16,22,38],[]),([55,655,132],[40,21,0,2,4,11,16,22,19,36,38],[]),([55,1391,48],[22,30,19,23,11,2,16,4,36,25,40,29],[]),([55,1391,50],[22,19,0],[534]),([55,1391,52],[22,30,17,0,19,11,2,4,16,36,23,25,40,29],[]),([55,1391,54],[0,22,19],[]),([55,1391,66],[19],[534]),([55,1423,48],[22,40,19,26,11,2,16,4,30,28,36,25],[]),([55,1423,50],[22,19],[535]),([55,1423,52],[22,40,17,0,19,11,2,16,4,30,26,28,36,25],[]),([55,1423,54],[0,22,19],[]),([55,1423,66],[0,19,22],[535]),([55,1423,144],[22,36,19,40,30,0,11,2,16,4,28],[]),([55,1423,148],[25,40,17,0,11,2,16,4,30,28,19],[]),([55,1663,48],[30,36,21,31,11,2,16,4,22,25,40,34],[]),([55,1663,50],[30,21],[536]),([55,1663,52],[30,36,17,0,21,11,2,16,4,22,25,40,31,34],[]),([55,1663,54],[0,30,21],[]),([55,1663,66],[0,21,30],[536]),([55,1663,144],[30,36,40,21,22,0,11,2,16,4,25],[]),([55,1663,148],[31,17,0,11,2,16,4,22,25,21],[]),([59,56,1663],[0,40,36,11,17,16,4,22,19,30,21],[]),([59,60,1663],[0,40,36,1,14,17,16,4,22,19,30,21],[]),([59,72,1663],[0,40,36,16,17,11,14,22,19,30,21],[]),([59,76,1663],[0,40,36,3,4,17,11,2,22,19,30,21],[]),([59,92,1663],[0,40,36,18,19,17,11,2,16,4,30,21],[]),([59,108,1663],[0,40,36,20,21,17,11,2,16,4,22,19],[]),([63,86,110],[0,10,22,19,11,2,16,4,36,25,40,29],[]),([63,86,142],[0,10,22,19,11,2,16,4,27,30,28,25],[537,538]),([63,102,110],[0,10,22,19,11,2,16,4,36,25,40,34],[]),([63,102,126],[0,10,30,21,11,2,16,4,25,40,34],[539,540]),([63,118,126],[0,6,30,17,21,11,2,16,4,22,25,40,32],[]),([63,134,110],[0,7,22,17,19,11,2,16,4,30,27],[]),([63,342,110],[0,10,22,19],[]),([63,358,110],[0,10,22,30,19,21],[]),([63,639,64],[0,36,10,19,21,25,30,38],[]),([63,639,112],[17,22,0,30,38,36,21,40,11,2,16,4],[]),([63,639,116],[36,19,0,11,2,16,4,30,21,40,38],[]),([63,655,64],[0,40,10,19,21,22,34,38],[]),([63,655,128],[17,30,0,22,38,40,11,2,16,4,19],[]),([63,655,132],[40,21,0,11,2,16,4,22,19,36,38],[]),([63,1391,48],[0,22,19,11,2,16,4,36,23,25,40,29],[]),([63,1391,80],[17,0,22,36,19,30,21,2,4],[541]),([63,1391,84],[0,19,30,2,4],[]),([63,1423,48],[0,22,17,19,11,2,16,4,30,26,28,36,25],[]),([63,1423,144],[22,36,19,40,30,0,11,2,16,4,28],[]),([63,1423,148],[25,40,0,19,11,2,16,4,30,28],[]),([63,1663,48],[0,30,17,21,11,2,16,4,22,25,40,31,34],[]),([63,1663,144],[30,36,40,21,22,0,11,2,16,4,25],[]),([63,1663,148],[31,0,21,11,2,16,4,22,25],[]),([71,82,42],[0,17,22,11,2,16,4,30,8,5,36,19],[]),([71,90,60],[17,0,11,2,16,4,30,18,36,21,40,25],[]),([71,90,72],[11,17,22,16,4,30,36,21,40,25],[]),([71,90,76],[17,2,16,22,30,4,36,21,40,25],[]),([71,90,88],[16,17,22,11,14,30,2,36,21,40,25],[]),([71,90,92],[17,4,11,22,30,2,36,21,40,25],[]),([71,90,104],[17,30,22,11,2,16,4,36,10,40,25],[]),([71,90,108],[17,30,10,0,22,11,2,16,4,36,20,21,29,19,40],[]),([71,90,120],[17,36,22,11,2,16,4,30,10,40,21],[]),([71,90,124],[17,10,0,22,19,11,2,16,4,30,21,40,25,29],[]),([71,90,136],[17,40,22,11,2,16,4,30,10,36,21],[]),([71,90,140],[17,10,0,22,11,2,16,4,30,21,36,25],[]),([71,90,316],[17,18,19,11,2,16,4,30,10,36,21,40,25],[]),([71,102,104],[17,30,19,25,40,11,2,16,4,36,8,22],[]),([71,102,108],[30,8,0,22,2,4,16,36,10,19,40,25],[]),([71,110,102],[0,22,21,30,11,2,16,4,36,25,40,29],[]),([71,134,136],[36,40,19,11,2,16,4,30,8],[]),([71,134,140],[36,40,8,0,22,2,16,4,10,19,30,25],[]),([71,142,102],[0,22,27,40,10,19,11,2,16,4,30,28,25],[]),([71,142,112],[30,40,22,11,2,16,4,19,36,25],[526]),([71,142,116],[40,28,11,2,16,4,19,36,25],[527]),([71,606,52],[0,22,19,11,16,2,30,4,36,25,40,28],[]),([71,654,52],[0,19,11,40,16,2,30,4,36,25],[]),([71,654,128],[22,36,40,19,30,28,11,2,16,4],[]),([79,102,110],[0,21,22,11,2,16,4,36,25,40,29],[]),([79,134,110],[0,7,19,22,11,2,16,4,30,28,25],[]),([87,82,42],[0,17,30,11,2,16,4,22,8,5,21],[]),([87,90,60],[17,0,11,2,16,4,22,19,36,20,40,34],[]),([87,90,72],[11,17,30,16,4,22,36,19,40,34],[]),([87,90,76],[17,2,16,30,22,4,36,19,40,34],[]),([87,90,88],[16,17,30,11,14,22,2,36,19,40,34],[]),([87,90,92],[17,4,11,30,22,2,36,19,40,34],[]),([87,90,104],[17,22,30,11,2,16,4,36,10,40,25],[]),([87,90,108],[17,22,10,0,30,11,2,16,4,36,18,19,35,21],[]),([87,90,120],[17,36,30,11,2,16,4,22,10,40,19],[]),([87,90,124],[17,10,0,30,11,2,16,4,22,19,40,34],[]),([87,90,136],[17,40,30,11,2,16,4,22,10,36,19],[]),([87,90,140],[17,10,0,30,21,11,2,16,4,22,19,36,34,35],[]),([87,90,316],[17,20,21,11,2,16,4,22,10,36,19,40,34],[]),([87,110,102],[0,22,19,11,2,16,4,36,25,40,29],[]),([87,118,136],[36,40,21,11,2,16,4,22,8],[]),([87,118,140],[36,8,0,30,2,16,4,10,21,22,25],[]),([87,126,102],[0,30,25,36,10,21,11,2,16,4,40,28,34],[]),([87,126,112],[22,36,30,11,2,16,4,21,40,34],[530]),([87,126,116],[36,25,30,11,2,16,4,21,40,34],[531]),([87,606,52],[0,30,21,11,16,2,22,4,36,28,34],[]),([87,638,52],[0,21,11,36,16,2,22,4,40,25],[]),([87,638,128],[30,36,40,21,22,25,11,2,16,4],[]),([95,102,110],[0,19,22,11,2,16,4,36,25,40,29,30],[]),([95,118,110],[0,6,21,30,11,2,16,4,22,25,40,34],[]),([303,1111,126],[11,12,14],[]),([303,1111,158],[11,12,14],[542,543]),([303,1111,670],[40,11],[544,545]),([303,1119,118],[11,12,14],[]),([303,1119,126],[11,12,14],[]),([303,1119,150],[11,12,14],[]),([303,1119,158],[11,12,14],[546,547,548,549]),([303,1119,638],[30,11],[550]),([303,1127,126],[11,12,14],[]),([303,1127,142],[11,12,14],[551,552]),([303,1127,654],[36,11],[553,554]),([303,1135,118],[11,12,14],[]),([303,1135,134],[11,12,14],[]),([303,1135,142],[11,12,14],[555,556,557,558]),([303,1135,638],[22,11],[559]),([303,1143,142],[11,12,14],[]),([303,1143,152],[17,40,36,14,11,2,22,12],[]),([303,1143,156],[12,14,11,2],[]),([303,1151,112],[22,17,12,14,36,25,11,2],[]),([303,1151,116],[12,14,11,2],[]),([303,1151,134],[11,12,14],[]),([303,1159,126],[11,12,14],[]),([303,1159,152],[17,36,40,14,11,2,22,12],[]),([303,1159,156],[12,14,11,2],[]),([303,1167,118],[11,12,14],[]),([303,1167,128],[30,17,12,14,40,34,11,2],[]),([303,1167,132],[12,14,11,2],[]),([303,1391,114],[11,30,22,17,12,14,4],[560,561,562,563,564,550,559]),([303,1391,118],[11,12,14],[]),([303,1391,122],[11,17,12,14],[]),([303,1423,114],[11,22,17,12,14,34],[]),([303,1423,118],[11,40,12,14],[544]),([303,1423,144],[22,36,2,34,40,11,12],[545]),([303,1423,148],[12,14,11,2],[]),([303,1663,114],[11,30,17,12,14,25],[]),([303,1663,118],[11,36,12,14],[553]),([303,1663,144],[30,36,40,2,25,11,12],[554]),([303,1663,148],[12,14,11,2],[]),([315,72,1663],[11,40,36,16,17,2,22,19,30,21],[]),([315,76,1663],[11,40,36,13,17,2,22,19,30,21],[]),([319,86,110],[11,19,2,16,13,36,25,40,29,22],[]),([319,86,142],[11,19,2,16,13,27,30,28,25],[565,566]),([319,102,110],[11,19,22,2,16,13,36,25,40,34],[]),([319,102,126],[11,21,2,16,13,25,40,34],[567,568]),([319,118,126],[11,21,30,2,16,13,22,25,40,32],[]),([319,134,110],[11,19,22,2,16,13,30,27],[]),([319,639,112],[17,22,11,2,13,30,38,36,21,40,16],[]),([319,639,116],[36,19,11,2,13,16,30,21,40,38],[]),([319,655,128],[17,30,11,2,13,22,38,40,16,19],[]),([319,655,132],[40,21,11,2,13,16,22,19,36,38],[]),([319,1391,48],[14,22,11,17,2,16,13,36,23,25,40,29,19],[]),([319,1391,80],[17,14,11,2,13,22,36,19,30,21],[569,570]),([319,1391,84],[11,14,2,13,22,30],[]),([319,1423,48],[14,22,11,17,2,16,13,30,26,28,36,25,19],[]),([319,1423,144],[22,36,19,40,30,11,2,16,13,28],[]),([319,1423,148],[25,40,14,11,2,16,13,30,28],[]),([319,1663,48],[14,30,11,17,2,16,13,22,25,40,31,34],[]),([319,1663,144],[30,36,40,21,22,11,2,16,13,25],[]),([319,1663,148],[31,14,11,2,16,13,22,25],[]),([335,102,110],[11,21,22,2,16,13,36,25,40,29],[]),([335,134,110],[11,27,19,2,16,13,30,28,25],[]),([351,102,110],[11,19,22,2,16,13,36,25,40,29,30],[]),([351,118,110],[11,25,30,21,2,16,13,40,34],[]),([571,72,1663],[11,40,36,16,17,4,22,19,30,21],[]),([571,76,1663],[16,40,36,13,17,4,22,19,30,21],[]),([575,86,110],[16,19,4,11,13,36,25,40,29,22],[]),([575,86,142],[16,19,4,11,13,27,30,28,25],[571,572]),([575,102,110],[16,19,22,4,11,13,36,25,40,34],[]),([575,102,126],[16,21,4,11,13,25,40,34],[573,574]),([575,118,126],[16,21,30,4,11,13,22,25,40,32],[]),([575,134,110],[16,19,22,4,11,13,30,27],[]),([575,639,112],[17,22,16,4,13,30,38,36,21,40],[]),([575,639,116],[36,19,16,4,13,30,21,40,38],[]),([575,655,128],[17,30,16,4,13,22,38,40,19],[]),([575,655,132],[40,21,16,4,13,22,19,36,38],[]),([575,1391,48],[22,30,16,4,17,11,13,36,23,25,40,29,19],[]),([575,1391,80],[17,4,16,13,22,36,19,30,21],[575,576]),([575,1391,84],[16,4,13,22,30],[]),([575,1423,48],[22,40,16,17,4,11,13,30,26,28,36,25,19],[]),([575,1423,144],[22,36,19,40,30,16,4,11,13,28],[]),([575,1423,148],[25,40,17,16,4,11,13,30,28],[]),([575,1663,48],[30,36,16,17,4,11,13,22,25,40,31,34],[]),([575,1663,144],[30,36,40,21,22,16,4,11,13,25],[]),([575,1663,148],[31,17,16,4,11,13,22,25],[]),([591,102,110],[16,21,22,4,11,13,36,25,40,29],[]),([591,134,110],[16,27,19,4,11,13,30,28,25],[]),([607,102,110],[16,19,22,4,11,13,36,25,40,29,30],[]),([607,118,110],[16,25,30,21,4,11,13,40,34],[]),([839,58,910],[17,22,19,36,40,30,25,21],[577]),([839,142,66],[17,10,0,22,11,2,16,4,30,21,36,25,40],[]),([839,142,70],[0,17,40,29,11,2,16,4,30,21,36,25],[]),([839,142,86],[11,14,17,22,2,16,13,30,21,36,25],[]),([839,142,102],[11,16,4,17,22,13,30,21,36,25],[]),([839,142,112],[17,30,22,40,36,11,16,25],[102,207,350,451,542]),([839,142,116],[17,30,22,21,40,11,16,36,25],[103,208,351,452,543]),([839,654,52],[17,22,19,40,11,16,30,21,36,25],[104,209,352,453,544]),([839,654,128],[22,36,17,40,30,28,11,16],[577,105,210,353,454,545]),([847,102,74],[22,18,30,11,2,16,4,36,25,40,29],[]),([847,102,78],[22,0,30,18,11,2,16,4,36,25,40,29],[]),([847,102,94],[11,14,17,18,2,16,13,36,25,40,29],[]),([847,102,110],[16,4,17,18,11,13,36,25,40,29],[]),([847,110,66],[22,19,30,11,2,16,4,36,25,40,29],[]),([847,110,70],[0,22,30,17,19,11,2,16,4,36,25,40,29],[]),([847,110,86],[11,14,2,16,13,36,25,40,29],[]),([847,110,102],[11,16,4,13,36,25,40,29],[]),([847,134,74],[22,18,40,11,2,16,4,30,28,25,36],[]),([847,134,78],[22,0,40,18,11,2,16,4,30,28,36,25],[]),([847,134,94],[11,14,17,18,2,16,13,30,28,36,25],[]),([847,134,110],[16,4,17,18,11,13,30,28,36,25],[]),([847,142,66],[22,19,40,11,2,16,4,30,28,36,25],[]),([847,142,70],[0,22,40,17,19,11,2,16,4,30,28,36,25],[]),([847,142,86],[11,14,2,16,13,30,28,36,25],[]),([847,142,102],[11,16,4,13,30,28,36,25],[]),([847,142,112],[30,17,40,22,19,11,16,36,25],[110,215,358,459,546]),([847,142,116],[40,17,19,21,28,11,16,36,25],[111,216,359,460,547]),([847,142,128],[36,17,40,22,19,11,16,30,28],[112,217,360,461,548]),([847,142,132],[40,17,19,25,11,16,30,28],[113,218,361,462,549]),([847,622,48],[17,18,30,21,11,16,36,25,40,29],[114,219,362,463,550]),([847,622,66],[22,19,30,21,36,29,25],[]),([855,58,894],[17,30,21,40,36,22,25,34],[578]),([855,126,66],[17,10,0,30,11,2,16,4,22,19,40,34,36],[]),([855,126,70],[0,17,36,35,11,2,16,4,22,19,40,34],[]),([855,126,86],[11,14,17,30,2,16,13,22,19,40,34],[]),([855,126,102],[11,16,4,17,30,13,22,19,40,34],[]),([855,126,112],[17,22,30,36,40,11,16,34],[116,223,364,467,551]),([855,126,116],[17,22,30,19,36,11,16,40,29],[117,224,365,468,552]),([855,638,52],[17,30,21,36,11,16,22,19,40,29],[118,225,366,469,553]),([855,638,128],[30,36,40,17,22,25,11,16],[578,119,226,367,470,554]),([863,102,74],[22,19,30,11,2,16,4,36,25,40,29],[]),([863,102,78],[22,0,19,30,11,2,16,4,36,25,40,29],[]),([863,102,94],[11,14,17,19,22,30,2,16,13,36,25,40,29],[]),([863,102,110],[16,4,17,19,22,30,11,13,36,25,40,29],[]),([863,118,74],[30,20,36,11,2,16,4,22,25,40,34],[]),([863,118,78],[30,0,36,20,11,2,16,4,22,25,40,34],[]),([863,118,94],[11,14,17,20,2,16,13,22,25,40,34],[]),([863,118,110],[16,4,17,20,11,13,22,25,40,34],[]),([863,126,66],[30,21,36,11,2,16,4,22,25,40,34],[]),([863,126,70],[0,30,36,17,21,11,2,16,4,22,25,40,34],[]),([863,126,86],[11,14,2,16,13,22,25,40,34],[]),([863,126,102],[11,16,4,13,22,25,40,34],[]),([863,126,112],[22,17,36,30,21,11,16,40,34],[123,230,371,474,555]),([863,126,116],[36,17,19,22,30,25,21,11,16,40,34],[124,231,372,475,556]),([863,126,128],[36,17,40,30,21,11,16,22,25],[125,232,373,476,557]),([863,126,132],[36,17,21,34,11,16,22,25],[126,233,374,477,558]),([863,622,48],[17,20,22,36,19,11,16,25,40,29],[127,234,375,478,559]),([863,622,66],[22,19,20,30,25,40,29],[]),([879,54,120],[0,17,30,36,11,2,16,4,22,25,40,34],[]),([879,54,124],[0,17,21,36,11,2,16,4,22,25,40,35,38],[532]),([895,54,104],[0,17,22,40,11,2,16,4,30,34,36,25],[]),([895,54,108],[0,17,19,40,11,2,16,4,30,29,34,38],[533]),([1119,50,110],[22,23,19,11,2,16,4,36,25,40,29],[534]),([1119,54,110],[0,22,30,11,2,16,4,36,25,40,29],[]),([1119,70,110],[11,14,22,30,2,16,13,36,25,40,29],[]),([1119,86,110],[16,4,22,30,11,13,36,25,40,29],[]),([1119,98,72],[17,22,30,11,16,36,25,40,29,19],[541,579,580,581,582,569,575,560]),([1119,98,74],[17,0,22,30,11,2,16,4,36,25,40,29,19],[541,130,238,378,482]),([1119,98,76],[17,22,30,11,14,16,4,36,25,40,27],[]),([1119,98,78],[17,22,30,11,14,16,4,36,25,40,27],[]),([1119,98,88],[11,17,22,30,16,4,36,25,40,29],[]),([1119,98,92],[17,22,30,2,16,15,36,25,40,29],[576,379]),([1119,98,94],[11,14,17,22,30,2,16,13,36,25,40,29],[]),([1119,98,104],[16,17,22,30,11,14,36,25,40,29],[]),([1119,98,108],[17,22,30,4,11,13,36,25,40,29],[570,131]),([1119,98,110],[16,17,22,30,4,11,13,36,25,40,29],[]),([1119,98,120],[17,22,30,36,11,16,40,27],[132,239,380,483,561]),([1119,98,124],[17,22,19,30,25,11,16,40,29],[133,240,381,484,562]),([1119,98,136],[17,22,40,30,11,16,36,25],[134,241,382,485,563]),([1119,98,140],[17,22,30,21,29,11,16,36,25],[135,242,383,486,564]),([1119,106,74],[17,22,30,11,2,16,4,36,25,40,29],[]),([1119,106,78],[17,22,30,11,2,16,4,36,25,40,29],[]),([1119,106,94],[11,14,2,16,13,36,25,40,29],[]),([1119,106,110],[16,17,22,30,4,11,13,36,25,40,29],[]),([1151,50,110],[22,26,19,11,2,16,4,30,28,36,25],[535]),([1151,54,110],[0,22,40,11,2,16,4,30,28,36,25,19],[]),([1151,70,110],[11,14,22,40,2,16,13,30,28,36,25],[]),([1151,86,110],[16,4,22,40,11,13,30,28,36,25],[]),([1151,98,74],[17,22,40,11,2,16,4,30,21,36,25],[]),([1151,98,78],[17,22,40,11,2,16,4,30,21,36,25],[]),([1151,98,94],[11,14,22,40,2,16,13,30,21,36,25],[]),([1151,98,110],[16,17,22,40,4,11,13,30,21,36,25],[]),([1391,50,110],[30,31,21,11,2,16,4,22,25,40,34],[536]),([1391,54,110],[0,30,36,11,2,16,4,22,25,40,34,21],[]),([1391,70,110],[11,14,30,36,2,16,13,22,25,40,34],[]),([1391,86,110],[16,4,30,36,11,13,22,25,40,34],[]),([1391,98,74],[17,30,36,11,2,16,4,22,19,40,29],[]),([1391,98,78],[17,30,36,11,2,16,4,22,19,40,29],[]),([1391,98,94],[11,14,30,36,2,16,13,22,19,40,29],[]),([1391,98,110],[16,17,30,36,4,11,13,22,19,40,29],[])],[([23,56,839,110],[11],[]),([23,56,839,142],[11],[0,1]),([23,56,839,654],[40],[2,3]),([23,56,847,102],[11],[]),([23,56,847,110],[11],[]),([23,56,847,134],[11],[]),([23,56,847,142],[11],[4,5,6,7]),([23,56,847,622],[30],[8]),([23,56,855,110],[11],[]),([23,56,855,126],[11],[9,10]),([23,56,855,638],[36],[11,12]),([23,56,863,102],[11],[]),([23,56,863,118],[11],[]),([23,56,863,126],[11],[13,14,15,16]),([23,56,863,622],[22],[17]),([23,56,871,126],[11],[]),([23,56,871,136],[17,40,16,0],[]),([23,56,871,140],[16,11,14],[]),([23,56,879,96],[22,16,11,14,36,25],[18]),([23,56,879,100],[16,11,14],[]),([23,56,879,118],[11],[]),([23,56,887,110],[11],[]),([23,56,887,136],[17,36,16,0],[]),([23,56,887,140],[16,11,14],[]),([23,56,895,102],[11],[]),([23,56,895,112],[30,16,11,14,40,34],[19]),([23,56,895,116],[16,11,14],[]),([23,56,1119,98],[11,30,22,14],[20,21,22,23,24,25,8,17]),([23,56,1119,102],[11,14],[]),([23,56,1119,106],[11,14],[]),([23,56,1151,98],[11,22,14,34],[]),([23,56,1151,102],[11,40],[2]),([23,56,1151,128],[22,36,16,1,34,40,14],[26,3]),([23,56,1151,132],[16,0,11,14],[]),([23,56,1391,98],[11,30,14,25],[]),([23,56,1391,102],[11,36],[11]),([23,56,1391,128],[30,36,40,16,1,25,14],[27,12]),([23,56,1391,132],[16,0,11,14],[]),([23,60,839,110],[11],[]),([23,60,839,142],[11],[28,29]),([23,60,839,654],[40],[30,31]),([23,60,847,102],[11],[]),([23,60,847,110],[11],[]),([23,60,847,134],[11],[]),([23,60,847,142],[11],[32,33,34,35]),([23,60,847,622],[30],[36]),([23,60,855,110],[11],[]),([23,60,855,126],[11],[37,38]),([23,60,855,638],[36],[39,40]),([23,60,863,102],[11],[]),([23,60,863,118],[11],[]),([23,60,863,126],[11],[41,42,43,44]),([23,60,863,622],[22],[45]),([23,60,871,126],[11],[]),([23,60,871,136],[17,40],[]),([23,60,871,140],[],[]),([23,60,879,96],[22,36,25],[]),([23,60,879,100],[],[]),([23,60,879,118],[11],[]),([23,60,887,110],[11],[]),([23,60,887,136],[17,36],[]),([23,60,887,140],[],[]),([23,60,895,102],[11],[]),([23,60,895,112],[30,40,34],[]),([23,60,895,116],[],[]),([23,60,1119,98],[11,30,22,14,1],[46,47,48,49,50,36,45]),([23,60,1119,102],[11],[]),([23,60,1119,106],[11],[]),([23,60,1151,98],[11,22,34],[]),([23,60,1151,102],[11,40],[30]),([23,60,1151,128],[22,36,1,34,40],[31]),([23,60,1151,132],[],[]),([23,60,1391,98],[11,30,25],[]),([23,60,1391,102],[11,36],[39]),([23,60,1391,128],[30,36,14,40,1,25],[40]),([23,60,1391,132],[],[]),([23,78,86,110],[11],[]),([23,78,86,142],[11],[51,52]),([23,78,102,110],[11],[]),([23,78,102,126],[11],[53,54]),([23,78,118,126],[11],[]),([23,78,134,110],[11],[]),([23,78,383,112],[11],[]),([23,78,383,116],[11],[]),([23,78,399,128],[11],[]),([23,78,399,132],[11],[]),([23,78,1391,48],[14,11],[55]),([23,78,1391,64],[14],[56]),([23,78,1391,68],[14],[]),([23,78,1423,48],[],[]),([23,78,1423,144],[22,19],[]),([23,78,1423,148],[11],[]),([23,78,1663,48],[],[]),([23,78,1663,144],[30,21],[]),([23,78,1663,148],[11],[]),([23,94,82,92],[],[]),([23,94,102,110],[11],[]),([23,94,134,110],[11,22],[]),([23,110,82,92],[],[]),([23,110,102,110],[11],[]),([23,110,118,110],[11,30],[]),([23,1111,158,68],[],[]),([23,1111,158,128],[11],[0,28]),([23,1111,158,132],[11],[1,29]),([23,1111,670,52],[11],[2,30]),([23,1111,670,144],[11],[3,31]),([23,1119,118,76],[],[]),([23,1119,126,68],[],[]),([23,1119,150,76],[],[]),([23,1119,158,68],[],[]),([23,1119,158,128],[11],[4,32]),([23,1119,158,132],[11],[5,33]),([23,1119,158,144],[11],[6,34]),([23,1119,158,148],[11],[7,35]),([23,1119,638,48],[11],[8,36]),([23,1127,142,68],[],[]),([23,1127,142,128],[11],[9,37]),([23,1127,142,132],[11],[10,38]),([23,1127,654,52],[11],[11,39]),([23,1127,654,144],[11],[12,40]),([23,1135,118,76],[],[]),([23,1135,134,76],[],[]),([23,1135,142,68],[],[]),([23,1135,142,128],[11],[13,41]),([23,1135,142,132],[11],[14,42]),([23,1135,142,144],[11],[15,43]),([23,1135,142,148],[11],[16,44]),([23,1135,638,48],[11],[17,45]),([23,1391,52,110],[11],[]),([23,1391,114,76],[11,14,1],[]),([23,1391,114,88],[11,17,14],[56,21,46]),([23,1391,114,124],[4,14],[57]),([23,1391,114,136],[11],[22,47]),([23,1391,114,140],[11],[23,48]),([23,1391,114,152],[11],[24,49]),([23,1391,114,156],[11],[25,50]),([23,1391,122,76],[],[]),([23,1423,52,110],[11],[]),([23,1423,114,76],[],[]),([23,1663,52,110],[11],[]),([23,1663,114,76],[],[]),([31,66,126,96],[22,36,21,40],[]),([31,66,126,100],[],[]),([31,66,142,112],[30,40,19,36],[]),([31,66,142,116],[],[]),([31,70,86,110],[0],[]),([31,70,86,142],[0],[]),([31,70,94,102],[0],[]),([31,70,94,134],[0],[58,59]),([31,70,102,110],[0],[]),([31,70,102,126],[0],[]),([31,70,110,102],[0],[]),([31,70,110,118],[0],[60,61]),([31,70,118,104],[22],[]),([31,70,118,108],[],[]),([31,70,118,126],[0],[]),([31,70,126,118],[0],[]),([31,70,134,110],[0],[]),([31,70,134,120],[30],[]),([31,70,134,124],[],[]),([31,70,142,102],[0],[]),([31,70,383,112],[0],[]),([31,70,383,116],[0],[]),([31,70,399,128],[0],[]),([31,70,399,132],[0],[]),([31,70,1391,48],[0],[]),([31,70,1391,52],[19],[]),([31,70,1423,48],[40],[]),([31,70,1423,52],[],[]),([31,70,1423,144],[22,19],[]),([31,70,1423,148],[0],[]),([31,70,1663,48],[36],[]),([31,70,1663,52],[],[]),([31,70,1663,144],[30,21],[]),([31,70,1663,148],[0],[]),([31,86,90,104],[],[]),([31,86,90,108],[17,30,29,22,36,19],[]),([31,86,90,120],[],[]),([31,86,90,124],[22,19,29],[]),([31,86,90,136],[17,40],[]),([31,86,90,140],[],[]),([31,86,90,300],[0,18,19],[]),([31,86,102,104],[30,19,25,40,22],[]),([31,86,102,108],[],[]),([31,86,110,102],[0],[]),([31,86,134,136],[36,40,19],[]),([31,86,134,140],[],[]),([31,86,142,102],[0,22],[]),([31,86,142,112],[22,30],[]),([31,86,142,116],[],[]),([31,86,398,128],[36,40,19,30,0,28],[]),([31,102,90,104],[],[]),([31,102,90,108],[17,22,35,30,21],[]),([31,102,90,120],[17,36],[]),([31,102,90,124],[],[]),([31,102,90,136],[],[]),([31,102,90,140],[30,21,35],[]),([31,102,90,300],[0,20,21],[]),([31,102,110,102],[0],[]),([31,102,118,136],[40,36,21],[]),([31,102,118,140],[],[]),([31,102,126,102],[0,30],[]),([31,102,126,112],[22,30],[]),([31,102,126,116],[],[]),([31,102,382,128],[36,30,40,21,22,25],[]),([31,1111,56,654],[],[62]),([31,1111,158,64],[],[]),([31,1111,158,128],[11],[]),([31,1111,158,132],[11],[]),([31,1111,670,52],[11],[]),([31,1111,670,144],[17,11],[62]),([31,1119,118,72],[],[]),([31,1119,126,64],[],[]),([31,1119,150,72],[],[]),([31,1119,158,64],[],[]),([31,1119,158,128],[11],[]),([31,1119,158,132],[11],[]),([31,1119,158,144],[22,19,11],[]),([31,1119,158,148],[11],[]),([31,1119,638,48],[11],[]),([31,1119,638,64],[],[]),([31,1127,56,638],[],[63]),([31,1127,142,64],[],[]),([31,1127,142,128],[11],[]),([31,1127,142,132],[11],[]),([31,1127,654,52],[11],[]),([31,1127,654,144],[17,11],[63]),([31,1135,118,72],[],[]),([31,1135,134,72],[],[]),([31,1135,142,64],[],[]),([31,1135,142,128],[11],[]),([31,1135,142,132],[11],[]),([31,1135,142,144],[30,21,11],[]),([31,1135,142,148],[11],[]),([31,1135,638,48],[11],[]),([31,1135,638,64],[],[]),([31,1391,48,110],[0],[]),([31,1391,114,72],[0,11],[]),([31,1391,114,88],[11,0],[]),([31,1391,114,136],[11],[]),([31,1391,114,140],[11],[]),([31,1391,114,152],[11],[]),([31,1391,114,156],[11],[]),([31,1391,122,72],[],[]),([31,1423,48,110],[0],[]),([31,1423,114,72],[],[]),([31,1663,48,110],[0],[]),([31,1663,114,72],[],[]),([39,56,839,110],[11],[]),([39,56,839,142],[11],[64,65]),([39,56,839,654],[40],[66,67]),([39,56,847,102],[11],[]),([39,56,847,110],[11],[]),([39,56,847,134],[11],[]),([39,56,847,142],[11],[68,69,70,71]),([39,56,847,622],[30],[72]),([39,56,855,110],[11],[]),([39,56,855,126],[11],[73,74]),([39,56,855,638],[36],[75,76]),([39,56,863,102],[11],[]),([39,56,863,118],[11],[]),([39,56,863,126],[11],[77,78,79,80]),([39,56,863,622],[22],[81]),([39,56,871,126],[11],[]),([39,56,871,136],[17,40,11,0],[]),([39,56,871,140],[11,16,17,0],[]),([39,56,879,96],[22,11,16,4,36,25],[82]),([39,56,879,100],[11,16,4],[]),([39,56,879,118],[11],[]),([39,56,887,110],[11],[]),([39,56,887,136],[17,36,11,0],[]),([39,56,887,140],[11,16,17,0],[]),([39,56,895,102],[11],[]),([39,56,895,112],[30,11,16,4,40,34],[83]),([39,56,895,116],[11,16,4],[]),([39,56,1119,98],[11,30,22,4,16],[84,85,86,87,88,89,72,81]),([39,56,1119,102],[11,4],[]),([39,56,1119,106],[11,16,4],[]),([39,56,1151,98],[11,22,16,4,34],[]),([39,56,1151,102],[11,40],[66]),([39,56,1151,128],[22,36,11,4,34,40,16],[90,67]),([39,56,1151,132],[11,0,16,4],[]),([39,56,1391,98],[11,30,16,4,25],[]),([39,56,1391,102],[11,36],[75]),([39,56,1391,128],[30,36,40,11,4,25,16],[91,76]),([39,56,1391,132],[11,0,16,4],[]),([39,60,839,110],[16],[]),([39,60,839,142],[16],[92,93]),([39,60,839,654],[40],[94,95]),([39,60,847,102],[16],[]),([39,60,847,110],[16],[]),([39,60,847,134],[16],[]),([39,60,847,142],[16],[96,97,98,99]),([39,60,847,622],[30],[100]),([39,60,855,110],[16],[]),([39,60,855,126],[16],[101,102]),([39,60,855,638],[36],[103,104]),([39,60,863,102],[16],[]),([39,60,863,118],[16],[]),([39,60,863,126],[16],[105,106,107,108]),([39,60,863,622],[22],[109]),([39,60,871,126],[16],[]),([39,60,871,136],[17,40],[]),([39,60,871,140],[],[]),([39,60,879,96],[22,36,25],[]),([39,60,879,100],[],[]),([39,60,879,118],[16],[]),([39,60,887,110],[16],[]),([39,60,887,136],[17,36],[]),([39,60,887,140],[],[]),([39,60,895,102],[16],[]),([39,60,895,112],[30,40,34],[]),([39,60,895,116],[],[]),([39,60,1119,98],[16,30,22,4,2],[110,111,112,113,114,100,109]),([39,60,1119,102],[16],[]),([39,60,1119,106],[16],[]),([39,60,1151,98],[16,22,34],[]),([39,60,1151,102],[16,40],[94]),([39,60,1151,128],[22,36,2,34,40],[95]),([39,60,1151,132],[],[]),([39,60,1391,98],[16,30,25],[]),([39,60,1391,102],[16,36],[103]),([39,60,1391,128],[30,36,40,2,25],[104]),([39,60,1391,132],[],[]),([39,78,86,110],[16],[]),([39,78,86,142],[16],[115,116]),([39,78,102,110],[16],[]),([39,78,102,126],[16],[117,118]),([39,78,118,126],[16],[]),([39,78,134,110],[16],[]),([39,78,383,112],[16],[]),([39,78,383,116],[16],[]),([39,78,399,128],[16],[]),([39,78,399,132],[16],[]),([39,78,1391,48],[3,4],[119]),([39,78,1391,64],[4],[120]),([39,78,1391,68],[4],[]),([39,78,1423,48],[],[]),([39,78,1423,144],[22,19],[]),([39,78,1423,148],[16],[]),([39,78,1663,48],[],[]),([39,78,1663,144],[30,21],[]),([39,78,1663,148],[16],[]),([39,94,82,92],[],[]),([39,94,102,110],[16],[]),([39,94,134,110],[16,22],[]),([39,110,82,92],[],[]),([39,110,102,110],[16],[]),([39,110,118,110],[16,30],[]),([39,1111,158,68],[],[]),([39,1111,158,128],[16],[64,92]),([39,1111,158,132],[16],[65,93]),([39,1111,670,52],[16],[66,94]),([39,1111,670,144],[16],[67,95]),([39,1119,118,76],[],[]),([39,1119,126,68],[],[]),([39,1119,150,76],[],[]),([39,1119,158,68],[],[]),([39,1119,158,128],[16],[68,96]),([39,1119,158,132],[16],[69,97]),([39,1119,158,144],[16],[70,98]),([39,1119,158,148],[16],[71,99]),([39,1119,638,48],[16],[72,100]),([39,1127,142,68],[],[]),([39,1127,142,128],[16],[73,101]),([39,1127,142,132],[16],[74,102]),([39,1127,654,52],[16],[75,103]),([39,1127,654,144],[16],[76,104]),([39,1135,118,76],[],[]),([39,1135,134,76],[],[]),([39,1135,142,68],[],[]),([39,1135,142,128],[16],[77,105]),([39,1135,142,132],[16],[78,106]),([39,1135,142,144],[16],[79,107]),([39,1135,142,148],[16],[80,108]),([39,1135,638,48],[16],[81,109]),([39,1391,52,110],[16],[]),([39,1391,114,76],[16,3,4],[]),([39,1391,114,88],[16,17,4],[120,85,110]),([39,1391,114,124],[2,4],[121]),([39,1391,114,136],[16],[86,111]),([39,1391,114,140],[16],[87,112]),([39,1391,114,152],[16],[88,113]),([39,1391,114,156],[16],[89,114]),([39,1391,122,76],[],[]),([39,1423,52,110],[16],[]),([39,1423,114,76],[],[]),([39,1663,52,110],[16],[]),([39,1663,114,76],[],[]),([47,66,126,100],[],[]),([47,66,142,116],[],[]),([47,70,86,110],[0],[]),([47,70,86,142],[0],[]),([47,70,94,102],[0],[]),([47,70,94,134],[0],[122,123]),([47,70,102,110],[0],[]),([47,70,102,126],[0],[]),([47,70,110,102],[0],[]),([47,70,110,118],[0],[124,125]),([47,70,118,104],[22],[]),([47,70,118,108],[],[]),([47,70,118,126],[0],[]),([47,70,126,118],[0],[]),([47,70,134,110],[0],[]),([47,70,134,120],[30],[]),([47,70,134,124],[],[]),([47,70,142,102],[0],[]),([47,70,383,112],[0],[]),([47,70,383,116],[0],[]),([47,70,399,128],[0],[]),([47,70,399,132],[0],[]),([47,70,1391,48],[0],[]),([47,70,1391,52],[19],[]),([47,70,1423,48],[40],[]),([47,70,1423,52],[],[]),([47,70,1423,144],[22,19],[]),([47,70,1423,148],[0],[]),([47,70,1663,48],[36],[]),([47,70,1663,52],[],[]),([47,70,1663,144],[30,21],[]),([47,70,1663,148],[0],[]),([47,86,90,108],[17,30,29,22,36,19],[]),([47,86,90,120],[],[]),([47,86,90,124],[22,19,29],[]),([47,86,90,136],[17,40],[]),([47,86,90,140],[],[]),([47,86,90,300],[0,18,19],[]),([47,86,102,104],[30,19,25,40,22],[]),([47,86,102,108],[],[]),([47,86,110,102],[0],[]),([47,86,134,136],[36,40,19],[]),([47,86,134,140],[],[]),([47,86,142,102],[0,22],[]),([47,86,142,112],[22,30],[]),([47,86,142,116],[],[]),([47,86,398,128],[36,40,19,30,0,28],[]),([47,102,90,108],[17,22,35,30,21],[]),([47,102,90,120],[17,36],[]),([47,102,90,124],[],[]),([47,102,90,136],[],[]),([47,102,90,140],[30,21,35],[]),([47,102,90,300],[0,20,21],[]),([47,102,110,102],[0],[]),([47,102,118,136],[40,36,21],[]),([47,102,118,140],[],[]),([47,102,126,102],[0,30],[]),([47,102,126,112],[22,30],[]),([47,102,126,116],[],[]),([47,102,382,128],[36,30,40,21,22,25],[]),([47,1111,56,654],[],[126]),([47,1111,158,64],[],[]),([47,1111,158,128],[16],[]),([47,1111,158,132],[16],[]),([47,1111,670,52],[16],[]),([47,1111,670,144],[17,16],[126]),([47,1119,118,72],[],[]),([47,1119,126,64],[],[]),([47,1119,150,72],[],[]),([47,1119,158,64],[],[]),([47,1119,158,128],[16],[]),([47,1119,158,132],[16],[]),([47,1119,158,144],[22,19,16],[]),([47,1119,158,148],[16],[]),([47,1119,638,48],[16],[]),([47,1119,638,64],[],[]),([47,1127,56,638],[],[127]),([47,1127,142,64],[],[]),([47,1127,142,128],[16],[]),([47,1127,142,132],[16],[]),([47,1127,654,52],[16],[]),([47,1127,654,144],[17,16],[127]),([47,1135,118,72],[],[]),([47,1135,134,72],[],[]),([47,1135,142,64],[],[]),([47,1135,142,128],[16],[]),([47,1135,142,132],[16],[]),([47,1135,142,144],[30,21,16],[]),([47,1135,142,148],[16],[]),([47,1135,638,48],[16],[]),([47,1135,638,64],[],[]),([47,1391,48,110],[0],[]),([47,1391,114,72],[0,16],[]),([47,1391,114,88],[16,0],[]),([47,1391,114,136],[16],[]),([47,1391,114,140],[16],[]),([47,1391,114,152],[16],[]),([47,1391,114,156],[16],[]),([47,1391,122,72],[],[]),([47,1423,48,110],[0],[]),([47,1423,114,72],[],[]),([47,1663,48,110],[0],[]),([47,1663,114,72],[],[]),([51,26,118,104],[22],[]),([51,26,118,108],[],[]),([51,26,134,120],[30],[]),([51,26,134,124],[],[]),([51,300,20,87],[0,36,5,11,2,16,4,22,19,25,30,21,40,38],[128,129]),([51,300,20,95],[0,36,5,11,2,16,4,22,19,30,21,40,38],[]),([51,300,20,103],[0,40,5,11,2,16,4,22,19,30,21,34,36,38],[130,131]),([51,300,20,111],[0,40,5,11,2,16,4,22,19,30,21,36,38],[]),([51,300,20,1391],[0,40,36,37,25],[]),([55,94,134,58],[0],[]),([55,94,134,120],[22,30],[]),([55,94,134,124],[],[]),([55,95,150,72],[5],[]),([55,95,150,136],[22,19],[]),([55,95,150,140],[22,19],[]),([55,110,118,58],[0],[]),([55,110,118,120],[22,30],[]),([55,110,118,124],[],[]),([55,111,134,72],[5],[]),([55,111,134,136],[22,21],[]),([55,111,134,140],[30,21],[]),([55,119,120,840],[0,8,22],[132]),([55,119,124,840],[0,8],[133]),([55,119,840,28],[0,36,5,10,19,38],[]),([55,119,840,44],[0,6,36,5,11,2,16,4,22,8,19,30,21,40,38],[132,133]),([55,127,840,44],[0,36,5,11,2,16,4,22,19,30,21,40,38],[]),([55,135,136,840],[0,8,30],[134]),([55,135,140,840],[0,8],[135]),([55,135,840,28],[0,40,5,10,21,38],[]),([55,135,840,44],[0,7,40,5,11,2,16,4,22,8,19,30,21,36,38],[134,135]),([55,143,840,44],[0,40,5,11,2,16,4,22,19,30,21,36,38],[]),([55,296,30,1663],[0,37,25,36],[]),([55,342,56,46],[17,22,8,5,36,19],[]),([55,343,158,68],[],[]),([55,343,158,128],[0],[]),([55,343,158,132],[0],[]),([55,358,56,46],[17,30,8,5,21],[]),([55,359,142,68],[],[]),([55,359,142,128],[0],[]),([55,359,142,132],[0],[]),([55,639,68,124],[17,21,0,2,4,38],[]),([55,655,68,108],[17,19,0,2,4,38],[]),([55,1391,50,92],[17],[]),([55,1423,50,92],[17,22],[]),([55,1663,50,92],[17,30],[]),([63,86,142,112],[22,30],[]),([63,86,142,116],[],[]),([63,102,126,112],[22,30],[]),([63,102,126,116],[],[]),([63,1391,80,72],[0,17,22,36,19,30,21,2,4],[]),([303,1111,158,128],[11],[]),([303,1111,158,132],[11],[]),([303,1111,670,52],[11],[]),([303,1111,670,144],[11],[]),([303,1119,158,128],[11],[]),([303,1119,158,132],[11],[]),([303,1119,158,144],[11],[]),([303,1119,158,148],[11],[]),([303,1119,638,48],[11],[]),([303,1127,142,128],[11],[]),([303,1127,142,132],[11],[]),([303,1127,654,52],[11],[]),([303,1127,654,144],[11],[]),([303,1135,142,128],[11],[]),([303,1135,142,132],[11],[]),([303,1135,142,144],[11],[]),([303,1135,142,148],[11],[]),([303,1135,638,48],[11],[]),([303,1391,114,120],[14,11],[]),([303,1391,114,136],[11],[]),([303,1391,114,140],[11],[]),([303,1391,114,152],[11],[]),([303,1391,114,156],[11],[]),([319,86,142,112],[22,30],[]),([319,86,142,116],[],[]),([319,102,126,112],[22,30],[]),([319,102,126,116],[],[]),([319,1391,80,88],[14,11,22,36,19,30,21,13],[136]),([319,1391,80,108],[11,14],[]),([575,86,142,112],[22,30],[]),([575,86,142,116],[],[]),([575,102,126,112],[22,30],[]),([575,102,126,116],[],[]),([575,1391,80,88],[4,16,22,36,19,30,21,13],[137]),([575,1391,80,108],[16,4],[]),([839,58,910,128],[36,17,30,21],[]),([855,58,894,128],[36,30,40,17,22,19],[]),([1119,98,72,71],[11,17,14],[56,138,139]),([1119,98,72,79],[11,14],[]),([1119,98,72,87],[16,17,4],[120,140,141]),([1119,98,72,95],[16,17,2],[])],[([23,56,839,142,112],[],[0]),([23,56,839,142,116],[],[]),([23,56,839,654,52],[],[]),([23,56,839,654,128],[],[1]),([23,56,847,142,112],[],[]),([23,56,847,142,116],[],[]),([23,56,847,142,128],[],[]),([23,56,847,142,132],[],[]),([23,56,847,622,48],[],[2]),([23,56,855,126,112],[],[3]),([23,56,855,126,116],[],[]),([23,56,855,638,52],[],[]),([23,56,855,638,128],[],[4]),([23,56,863,126,112],[],[]),([23,56,863,126,116],[],[]),([23,56,863,126,128],[],[]),([23,56,863,126,132],[],[]),([23,56,863,622,48],[],[5]),([23,56,879,96,60],[36,25,14,11],[6,7,8,9,10,11]),([23,56,895,112,60],[40,34,14,11],[12,13,14,15,16,17]),([23,56,1119,98,76],[14],[2,5]),([23,56,1119,98,88],[14],[]),([23,56,1119,98,120],[],[]),([23,56,1119,98,124],[],[]),([23,56,1119,98,136],[],[]),([23,56,1119,98,140],[],[]),([23,56,1151,128,60],[22,40,34,14,11,1],[18,19,20,21,22,1]),([23,56,1391,128,60],[30,36,25,14,11,1],[23,24,25,26,27,4]),([23,60,839,142,112],[],[]),([23,60,839,142,116],[],[]),([23,60,839,654,52],[],[]),([23,60,839,654,128],[],[]),([23,60,847,142,112],[],[]),([23,60,847,142,116],[],[]),([23,60,847,142,128],[],[]),([23,60,847,142,132],[],[]),([23,60,847,622,48],[],[]),([23,60,855,126,112],[],[]),([23,60,855,126,116],[],[]),([23,60,855,638,52],[],[]),([23,60,855,638,128],[],[]),([23,60,863,126,112],[],[]),([23,60,863,126,116],[],[]),([23,60,863,126,128],[],[]),([23,60,863,126,132],[],[]),([23,60,863,622,48],[],[]),([23,60,1119,98,88],[],[]),([23,60,1119,98,120],[],[]),([23,60,1119,98,124],[],[]),([23,60,1119,98,136],[],[]),([23,60,1119,98,140],[],[]),([23,78,86,142,112],[],[]),([23,78,86,142,116],[],[]),([23,78,102,126,112],[],[]),([23,78,102,126,116],[],[]),([23,78,1391,48,108],[],[]),([23,78,1391,64,72],[],[]),([23,1391,114,124,68],[14],[]),([31,70,94,134,120],[],[]),([31,70,94,134,124],[],[]),([31,70,110,118,120],[],[]),([31,70,110,118,124],[],[]),([31,1111,56,654,128],[],[]),([31,1127,56,638,128],[],[]),([39,56,839,142,112],[],[28]),([39,56,839,142,116],[],[]),([39,56,839,654,52],[],[]),([39,56,839,654,128],[],[29]),([39,56,847,142,112],[],[]),([39,56,847,142,116],[],[]),([39,56,847,142,128],[],[]),([39,56,847,142,132],[],[]),([39,56,847,622,48],[],[30]),([39,56,855,126,112],[],[31]),([39,56,855,126,116],[],[]),([39,56,855,638,52],[],[]),([39,56,855,638,128],[],[32]),([39,56,863,126,112],[],[]),([39,56,863,126,116],[],[]),([39,56,863,126,128],[],[]),([39,56,863,126,132],[],[]),([39,56,863,622,48],[],[33]),([39,56,879,96,60],[36,25,4,16],[34,35,36,37,38,39]),([39,56,895,112,60],[40,34,4,16],[40,41,42,43,44,45]),([39,56,1119,98,76],[4],[30,33]),([39,56,1119,98,88],[4],[]),([39,56,1119,98,120],[],[]),([39,56,1119,98,124],[],[]),([39,56,1119,98,136],[],[]),([39,56,1119,98,140],[],[]),([39,56,1151,128,60],[22,40,34,4,16],[46,47,48,49,50,29]),([39,56,1391,128,60],[30,36,25,4,16],[51,52,53,54,55,32]),([39,60,839,142,112],[],[]),([39,60,839,142,116],[],[]),([39,60,839,654,52],[],[]),([39,60,839,654,128],[],[]),([39,60,847,142,112],[],[]),([39,60,847,142,116],[],[]),([39,60,847,142,128],[],[]),([39,60,847,142,132],[],[]),([39,60,847,622,48],[],[]),([39,60,855,126,112],[],[]),([39,60,855,126,116],[],[]),([39,60,855,638,52],[],[]),([39,60,855,638,128],[],[]),([39,60,863,126,112],[],[]),([39,60,863,126,116],[],[]),([39,60,863,126,128],[],[]),([39,60,863,126,132],[],[]),([39,60,863,622,48],[],[]),([39,60,1119,98,88],[],[]),([39,60,1119,98,120],[],[]),([39,60,1119,98,124],[],[]),([39,60,1119,98,136],[],[]),([39,60,1119,98,140],[],[]),([39,78,86,142,112],[],[]),([39,78,86,142,116],[],[]),([39,78,102,126,112],[],[]),([39,78,102,126,116],[],[]),([39,78,1391,48,108],[],[]),([39,78,1391,64,72],[],[]),([39,1391,114,124,68],[4],[]),([47,70,94,134,120],[],[]),([47,70,94,134,124],[],[]),([47,70,110,118,120],[],[]),([47,70,110,118,124],[],[]),([47,1111,56,654,128],[],[]),([47,1127,56,638,128],[],[]),([51,300,20,87,88],[22],[]),([51,300,20,87,92],[],[]),([51,300,20,103,104],[30],[]),([51,300,20,103,108],[],[]),([55,119,120,840,44],[],[]),([55,119,124,840,44],[],[]),([55,135,136,840,44],[],[]),([55,135,140,840,44],[],[]),([319,1391,80,88,57],[14],[56]),([575,1391,80,88,57],[17,4],[57]),([1119,98,72,71,104],[14],[]),([1119,98,72,71,108],[],[]),([1119,98,72,87,104],[4],[]),([1119,98,72,87,108],[],[])],[([23,56,839,142,112,76],[],[]),([23,56,839,654,128,76],[],[]),([23,56,847,622,48,60],[],[]),([23,56,855,126,112,76],[],[]),([23,56,855,638,128,76],[],[]),([23,56,863,622,48,60],[],[]),([23,56,879,96,60,25],[],[]),([23,56,879,96,60,29],[],[0,1]),([23,56,879,96,60,57],[14],[0]),([23,56,879,96,60,89],[],[]),([23,56,879,96,60,93],[],[1,2]),([23,56,879,96,60,109],[25],[2]),([23,56,895,112,60,25],[],[]),([23,56,895,112,60,29],[],[3,4]),([23,56,895,112,60,57],[14],[3]),([23,56,895,112,60,89],[],[]),([23,56,895,112,60,93],[],[4,5]),([23,56,895,112,60,109],[34],[5]),([23,56,1151,128,60,29],[],[6]),([23,56,1151,128,60,57],[14],[7]),([23,56,1151,128,60,89],[],[]),([23,56,1151,128,60,93],[],[6,7,8]),([23,56,1151,128,60,109],[34],[8]),([23,56,1391,128,60,29],[],[9]),([23,56,1391,128,60,57],[14],[10]),([23,56,1391,128,60,89],[],[]),([23,56,1391,128,60,93],[],[9,10,11]),([23,56,1391,128,60,109],[25],[11]),([39,56,839,142,112,76],[],[]),([39,56,839,654,128,76],[],[]),([39,56,847,622,48,60],[],[]),([39,56,855,126,112,76],[],[]),([39,56,855,638,128,76],[],[]),([39,56,863,622,48,60],[],[]),([39,56,879,96,60,25],[],[]),([39,56,879,96,60,29],[],[12,13]),([39,56,879,96,60,57],[4],[12]),([39,56,879,96,60,89],[],[]),([39,56,879,96,60,93],[],[13,14]),([39,56,879,96,60,109],[25],[14]),([39,56,895,112,60,25],[],[]),([39,56,895,112,60,29],[],[15,16]),([39,56,895,112,60,57],[4],[15]),([39,56,895,112,60,89],[],[]),([39,56,895,112,60,93],[],[16,17]),([39,56,895,112,60,109],[34],[17]),([39,56,1151,128,60,29],[],[18]),([39,56,1151,128,60,57],[4],[19]),([39,56,1151,128,60,89],[],[]),([39,56,1151,128,60,93],[],[18,19,20]),([39,56,1151,128,60,109],[34],[20]),([39,56,1391,128,60,29],[],[21]),([39,56,1391,128,60,57],[4],[22]),([39,56,1391,128,60,89],[],[]),([39,56,1391,128,60,93],[],[21,22,23]),([39,56,1391,128,60,109],[25],[23]),([319,1391,80,88,57,92],[14],[]),([575,1391,80,88,57,92],[4],[])],[([23,56,879,96,60,29,312],[],[]),([23,56,879,96,60,29,348],[],[]),([23,56,879,96,60,93,364],[],[]),([23,56,895,112,60,29,312],[],[]),([23,56,895,112,60,29,348],[],[]),([23,56,895,112,60,93,364],[],[]),([23,56,1151,128,60,29,348],[],[]),([23,56,1151,128,60,57,348],[],[]),([23,56,1151,128,60,93,364],[],[]),([23,56,1391,128,60,29,348],[],[]),([23,56,1391,128,60,57,348],[],[]),([23,56,1391,128,60,93,364],[],[]),([39,56,879,96,60,29,312],[],[]),([39,56,879,96,60,29,348],[],[]),([39,56,879,96,60,93,364],[],[]),([39,56,895,112,60,29,312],[],[]),([39,56,895,112,60,29,348],[],[]),([39,56,895,112,60,93,364],[],[]),([39,56,1151,128,60,29,348],[],[]),([39,56,1151,128,60,57,348],[],[]),([39,56,1151,128,60,93,364],[],[]),([39,56,1391,128,60,29,348],[],[]),([39,56,1391,128,60,57,348],[],[]),([39,56,1391,128,60,93,364],[],[])]]
set_option maxRecDepth 100000 in
theorem g178 : GoodC c178 := claim_sound [c7,c14,c6,c15,c22,c24,c26,c28,c30,c31,c33,c58,c34,c35,c59,c60,c84,c106,c93,c97,c98,c99,c129,c111,c116,c122,c124,c128,c130,c134,c154,c145,c147,c148,c153,c157,c166,c164,c165,c167,c177] (gcons g7 (gcons g14 (gcons g6 (gcons g15 (gcons g22 (gcons g24 (gcons g26 (gcons g28 (gcons g30 (gcons g31 (gcons g33 (gcons g58 (gcons g34 (gcons g35 (gcons g59 (gcons g60 (gcons g84 (gcons g106 (gcons g93 (gcons g97 (gcons g98 (gcons g99 (gcons g129 (gcons g111 (gcons g116 (gcons g122 (gcons g124 (gcons g128 (gcons g130 (gcons g134 (gcons g154 (gcons g145 (gcons g147 (gcons g148 (gcons g153 (gcons g157 (gcons g166 (gcons g164 (gcons g165 (gcons g167 (gcons g177 gnil))))))))))))))))))))))))))))))))))))))))) r178 d178 e178 c178 (by decide +kernel)

end Check516

end PEqualNP.Outside.L_meta_8439

theorem PEqualNP.Outside.L_meta_8439 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 13 ≤ t :=
  fun t h => PEqualNP.Outside.L_meta_8439.Check516.final_bound 12 PEqualNP.Outside.L_meta_8439.Check516.g178 t h
