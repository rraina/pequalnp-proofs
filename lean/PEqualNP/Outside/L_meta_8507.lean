import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8507


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
  [0xc21f8087e021127c1f8087c0fc043e0427c1094fc00f8003e000003c0f8003c07c001e0003c00007,
   0x45f0817c205f05c420897c41044be2084852f8b901f0007c001f01c000007c000003e0000000f838,
   0xbe210f8843e20e89f107888f883c447c1c8f10d23e000f8003e00e01f007800f803c007c1c0f00c0,
   0x842121087fff01042121112109088ffe10fff040000000003fff000000000000000007fe00fff00,
   0x1084242108842923fff8200fffc1007ffff020200000000000000001fff8000fffc0007ffff00000,
   0x21084ffffd0840008424422fffffff908004420000000ffffc0000000000000fffffff8000000000,
   0x3ffff84212108001fffffff421221121000884003ffff00000000001fffffff00000000000000000,
   0x3fffffffffffffff0840000842000042122000003ffffffffffffffe000000000000000000000000]

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
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6)

def assignment (k : Fin 320) (i : Fin 8) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live516.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 160) := [3, 0, 1, 2, 5, 9, 10, 21]
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
  have ht : (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) =
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

theorem level_sound {R : List RR} {av : List W} (hR : ∀ y ∈ R, RInv av.toFinset y)
    (K : Nat) (D : List Entry) (T : List (List W))
    (hT : ∀ l ∈ T, ¬ Live516.live basicOps goal (K - 1) l.toFinset)
    (h : levelOK R av K D T = true) :
    ∀ e ∈ D, ¬ Live516.live basicOps goal K (wsOf av e).toFinset := by
  intro e he
  have hE := List.all_eq_true.mp h e he
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
    | succ k => exact state_sound hR (by simpa using hT) hE inv.1 inv.2

theorem map_dead {av : List W} {K : Nat} {D : List Entry}
    (h : ∀ e ∈ D, ¬ Live516.live basicOps goal K (wsOf av e).toFinset) :
    ∀ l ∈ D.map (wsOf av), ¬ Live516.live basicOps goal K l.toFinset := by
  intro l hl
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
  exact h e he

theorem app_dead {av : List W} {K : Nat} {D1 D2 : List Entry}
    (h1 : ∀ e ∈ D1, ¬ Live516.live basicOps goal K (wsOf av e).toFinset)
    (h2 : ∀ e ∈ D2, ¬ Live516.live basicOps goal K (wsOf av e).toFinset) :
    ∀ e ∈ D1 ++ D2, ¬ Live516.live basicOps goal K (wsOf av e).toFinset := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

theorem nil_dead {K : Nat} : ∀ l ∈ ([] : List (List W)),
    ¬ Live516.live basicOps goal K l.toFinset := fun _ h => absurd h List.not_mem_nil

theorem res_inv (cl : List Claim) (hcl : ∀ c ∈ cl, GoodC c) (rs : List RE) (av : List W) :
    ∀ y ∈ rs.map (resolve cl av), RInv av.toFinset y := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
  exact resolve_inv cl hcl av x

def topOK (D0 : List Entry) (c : Claim) : Bool :=
  decide c.2.Nodup &&
    ((c.2.filter (fun a => cuts (c.2.erase a) == -1)).sublists.all (fun J =>
      (D0.map (wsOf c.2)).any (seteq ((c.2.filter (fun a => cuts (c.2.erase a) != -1)) ++ J))))

theorem claim_sound2 (D0 : List Entry) (c : Claim)
    (dead0 : ∀ e ∈ D0, ¬ Live516.live basicOps goal c.1 (wsOf c.2 e).toFinset)
    (h : topOK D0 c = true) : GoodC c := by
  intro hb
  simp only [topOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hn, hsubl⟩ := h
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
  have dead := dead0 e he
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

def c0 : Claim := (3, available 0x50001400c000000000300000018000000600 9 inputs)
def r0 : List RE := []
def d0 : List Entry := [([4099],[],[]),([],[],[])]
def e0 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g0 : GoodC c0 := claim_sound [] gnil r0 d0 e0 c0 (by decide +kernel)
def c1 : Claim := (3, available 0x3000000180000180000000 31 inputs)
def r1 : List RE := []
def d1 : List Entry := [([],[],[])]
def e1 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g1 : GoodC c1 := claim_sound [] gnil r1 d1 e1 c1 (by decide +kernel)
def c2 : Claim := (4, available 0x7000000380000380200000 21 inputs)
def r2 : List RE := [(0x3000000180000180000000,31,0)]
def d2 : List Entry := [([],[0],[])]
def e2 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g2 : GoodC c2 := claim_sound [c1] (gcons g1 gnil) r2 d2 e2 c2 (by decide +kernel)
def c3 : Claim := (5, available 0x70001c00e002007000300380018380200600 9 inputs)
def r3 : List RE := [(0x50001400c000000000300000018000000600,9,0),(0x7000000380000380200000,21,1)]
def d3 : List Entry := [([],[0,1],[])]
def e3 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g3 : GoodC c3 := claim_sound [c0,c2] (gcons g0 (gcons g2 gnil)) r3 d3 e3 c3 (by decide +kernel)
def c4 : Claim := (5, available 0x38007e001f80e803c076003e03b001f3902c0600 9 inputs)
def r4 : List RE := [(0x70001c00e002007000300380018380200600,9,0)]
def d4 : List Entry := [([4096],[0],[]),([],[0],[])]
def e4 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g4 : GoodC c4 := claim_sound [c3] (gcons g3 gnil) r4 d4 e4 c4 (by decide +kernel)
def c5 : Claim := (3, available 0x14000500018000000005000000280000000c000 14 inputs)
def r5 : List RE := []
def d5 : List Entry := [([4099],[],[]),([],[],[])]
def e5 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g5 : GoodC c5 := claim_sound [] gnil r5 d5 e5 c5 (by decide +kernel)
def c6 : Claim := (4, available 0x1c00070001c010000007000000380000000e020 5 inputs)
def r6 : List RE := [(0x14000500018000000005000000280000000c000,14,0)]
def d6 : List Entry := [([4100],[0],[]),([],[],[])]
def e6 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g6 : GoodC c6 := claim_sound [c5] (gcons g5 gnil) r6 d6 e6 c6 (by decide +kernel)
def c7 : Claim := (5, available 0x1e00078001e0180000078000003c0000000f030 4 inputs)
def r7 : List RE := [(0x1c00070001c010000007000000380000000e020,5,0)]
def d7 : List Entry := [([4101],[0],[]),([],[0],[])]
def e7 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g7 : GoodC c7 := claim_sound [c6] (gcons g6 gnil) r7 d7 e7 c7 (by decide +kernel)
def c8 : Claim := (6, available 0x1c070701c1ce1020078703003c38183c030e620 5 inputs)
def r8 : List RE := [(0x70001c00e002007000300380018380200600,9,0)]
def d8 : List Entry := [([],[0],[])]
def e8 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g8 : GoodC c8 := claim_sound [c3] (gcons g3 gnil) r8 d8 e8 c8 (by decide +kernel)
def c9 : Claim := (3, available 0x28000a00030000000006000000300000000c0000 18 inputs)
def r9 : List RE := []
def d9 : List Entry := [([4099],[],[]),([],[],[])]
def e9 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g9 : GoodC c9 := claim_sound [] gnil r9 d9 e9 c9 (by decide +kernel)
def c10 : Claim := (3, available 0xc00000060000003000000000 36 inputs)
def r10 : List RE := []
def d10 : List Entry := [([],[],[])]
def e10 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g10 : GoodC c10 := claim_sound [] gnil r10 d10 e10 c10 (by decide +kernel)
def c11 : Claim := (4, available 0x1c000000e0000007010000000 28 inputs)
def r11 : List RE := [(0xc00000060000003000000000,36,0)]
def d11 : List Entry := [([],[0],[])]
def e11 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g11 : GoodC c11 := claim_sound [c10] (gcons g10 gnil) r11 d11 e11 c11 (by decide +kernel)
def c12 : Claim := (5, available 0x38000e0003800801c006000e00300070100c0000 18 inputs)
def r12 : List RE := [(0x28000a00030000000006000000300000000c0000,18,0),(0x1c000000e0000007010000000,28,1)]
def d12 : List Entry := [([],[0,1],[])]
def e12 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g12 : GoodC c12 := claim_sound [c9,c11] (gcons g9 (gcons g11 gnil)) r12 d12 e12 c12 (by decide +kernel)
def c13 : Claim := (6, available 0x3c000f0003c00c01e007000f00380078180e0080 7 inputs)
def r13 : List RE := [(0x38000e0003800801c006000e00300070100c0000,18,0)]
def d13 : List Entry := [([],[0],[])]
def e13 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g13 : GoodC c13 := claim_sound [c12] (gcons g12 gnil) r13 d13 e13 c13 (by decide +kernel)
def c14 : Claim := (3, available 0x14a0200000000d832049280000000000183000b0 4 inputs)
def r14 : List RE := []
def d14 : List Entry := [([4099],[],[]),([],[],[])]
def e14 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g14 : GoodC c14 := claim_sound [] gnil r14 d14 e14 c14 (by decide +kernel)
def c15 : Claim := (5, available 0x35a06d6818000d83a06d682d036b4100183000b0 4 inputs)
def r15 : List RE := [(0x14a0200000000d832049280000000000183000b0,4,0)]
def d15 : List Entry := [([],[0],[])]
def e15 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g15 : GoodC c15 := claim_sound [c14] (gcons g14 gnil) r15 d15 e15 c15 (by decide +kernel)
def c16 : Claim := (4, available 0x2d6a000000000000000006b400ab400 10 inputs)
def r16 : List RE := []
def d16 : List Entry := [([],[],[])]
def e16 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g16 : GoodC c16 := claim_sound [] gnil r16 d16 e16 c16 (by decide +kernel)
def c17 : Claim := (5, available 0x3dee000000000000000007bc00ef600 9 inputs)
def r17 : List RE := [(0x2d6a000000000000000006b400ab400,10,0)]
def d17 : List Entry := [([],[0],[])]
def e17 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g17 : GoodC c17 := claim_sound [c16] (gcons g16 gnil) r17 d17 e17 c17 (by decide +kernel)
def c18 : Claim := (4, available 0x1600058001a0080000058000002c0000000d010 4 inputs)
def r18 : List RE := [(0x14000500018000000005000000280000000c000,14,0)]
def d18 : List Entry := [([4100],[0],[]),([],[],[])]
def e18 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g18 : GoodC c18 := claim_sound [c5] (gcons g5 gnil) r18 d18 e18 c18 (by decide +kernel)
def c19 : Claim := (5, available 0x2d605b58175ac48000075830003ac180000ed690 4 inputs)
def r19 : List RE := [(0x1600058001a0080000058000002c0000000d010,4,0)]
def d19 : List Entry := [([4101],[0],[]),([],[0],[])]
def e19 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g19 : GoodC c19 := claim_sound [c18] (gcons g18 gnil) r19 d19 e19 c19 (by decide +kernel)
def c20 : Claim := (4, available 0x1c070000e0380007390200000 21 inputs)
def r20 : List RE := [(0x7000000380000380200000,21,0)]
def d20 : List Entry := [([4096],[0],[]),([],[],[])]
def e20 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g20 : GoodC c20 := claim_sound [c2] (gcons g2 gnil) r20 d20 e20 c20 (by decide +kernel)
def c21 : Claim := (5, available 0x1e078000f03c0007bd8300000 20 inputs)
def r21 : List RE := [(0x1c070000e0380007390200000,21,0)]
def d21 : List Entry := [([4097],[0],[]),([],[0],[])]
def e21 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g21 : GoodC c21 := claim_sound [c20] (gcons g20 gnil) r21 d21 e21 c21 (by decide +kernel)
def c22 : Claim := (5, available 0x1ce0300002d6ad83605b38100000006b583ab4b0 4 inputs)
def r22 : List RE := [(0x14a0200000000d832049280000000000183000b0,4,0)]
def d22 : List Entry := [([],[0],[])]
def e22 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g22 : GoodC c22 := claim_sound [c14] (gcons g14 gnil) r22 d22 e22 c22 (by decide +kernel)
def c23 : Claim := (4, available 0xd68180000000000000d036b410000000000 40 inputs)
def r23 : List RE := []
def d23 : List Entry := [([],[],[])]
def e23 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g23 : GoodC c23 := claim_sound [] gnil r23 d23 e23 c23 (by decide +kernel)
def c24 : Claim := (5, available 0xf781c0000000000000f03fbc18000000000 39 inputs)
def r24 : List RE := [(0xd68180000000000000d036b410000000000,40,0)]
def d24 : List Entry := [([],[0],[])]
def e24 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g24 : GoodC c24 := claim_sound [c23] (gcons g23 gnil) r24 d24 e24 c24 (by decide +kernel)
def c25 : Claim := (3, available 0x52808000d820000000902494000183000b0 4 inputs)
def r25 : List RE := []
def d25 : List Entry := [([4099],[],[]),([],[],[])]
def e25 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g25 : GoodC c25 := claim_sound [] gnil r25 d25 e25 c25 (by decide +kernel)
def c26 : Claim := (5, available 0x7380dce6d820000000b02d9c0dad83672b0 4 inputs)
def r26 : List RE := [(0x52808000d820000000902494000183000b0,4,0)]
def d26 : List Entry := [([],[0],[])]
def e26 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g26 : GoodC c26 := claim_sound [c25] (gcons g25 gnil) r26 d26 e26 c26 (by decide +kernel)
def c27 : Claim := (4, available 0x35a0600000000001a06d68200000000000000000 69 inputs)
def r27 : List RE := []
def d27 : List Entry := [([],[],[])]
def e27 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g27 : GoodC c27 := claim_sound [] gnil r27 d27 e27 c27 (by decide +kernel)
def c28 : Claim := (5, available 0x3de0700000000001e07f78300000000000000000 68 inputs)
def r28 : List RE := [(0x35a0600000000001a06d68200000000000000000,69,0)]
def d28 : List Entry := [([],[0],[])]
def e28 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g28 : GoodC c28 := claim_sound [c27] (gcons g27 gnil) r28 d28 e28 c28 (by decide +kernel)
def c29 : Claim := (8, available 0x3de07f781fdeed83e07f783f03fbc1fbd83ef6b0 4 inputs)
def r29 : List RE := [(0x38007e001f80e803c076003e03b001f3902c0600,9,0),(0x1e00078001e0180000078000003c0000000f030,4,1),(0x1c070701c1ce1020078703003c38183c030e620,5,2),(0x3c000f0003c00c01e007000f00380078180e0080,7,3),(0x35a06d6818000d83a06d682d036b4100183000b0,4,4),(0x3dee000000000000000007bc00ef600,9,5),(0x2d605b58175ac48000075830003ac180000ed690,4,6),(0x1e078000f03c0007bd8300000,20,7),(0x1ce0300002d6ad83605b38100000006b583ab4b0,4,8),(0xf781c0000000000000f03fbc18000000000,39,9),(0x7380dce6d820000000b02d9c0dad83672b0,4,10),(0x3de0700000000001e07f78300000000000000000,68,11)]
def d29 : List Entry := [([],[1,0,2,3,4,5,6,7,8,9,10,11],[])]
def e29 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g29 : GoodC c29 := claim_sound [c4,c7,c8,c13,c15,c17,c19,c21,c22,c24,c26,c28] (gcons g4 (gcons g7 (gcons g8 (gcons g13 (gcons g15 (gcons g17 (gcons g19 (gcons g21 (gcons g22 (gcons g24 (gcons g26 (gcons g28 gnil)))))))))))) r29 d29 e29 c29 (by decide +kernel)
def c30 : Claim := (6, available 0xe70039c00f0320e70033073801983a3200704 2 inputs)
def r30 : List RE := [(0x70001c00e002007000300380018380200600,9,0)]
def d30 : List Entry := [([],[0],[])]
def e30 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g30 : GoodC c30 := claim_sound [c3] (gcons g3 gnil) r30 d30 e30 c30 (by decide +kernel)
def c31 : Claim := (5, available 0xe70000073800003a3200000 21 inputs)
def r31 : List RE := [(0x7000000380000380200000,21,0)]
def d31 : List Entry := [([],[0],[])]
def e31 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g31 : GoodC c31 := claim_sound [c2] (gcons g2 gnil) r31 d31 e31 c31 (by decide +kernel)
def c32 : Claim := (3, available 0xc03000060180003180000000 31 inputs)
def r32 : List RE := []
def d32 : List Entry := [([4096],[],[]),([],[],[])]
def e32 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g32 : GoodC c32 := claim_sound [] gnil r32 d32 e32 c32 (by decide +kernel)
def c33 : Claim := (4, available 0x630000031800001a1000000 24 inputs)
def r33 : List RE := [(0x3000000180000180000000,31,0)]
def d33 : List Entry := [([],[0],[])]
def e33 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g33 : GoodC c33 := claim_sound [c1] (gcons g1 gnil) r33 d33 e33 c33 (by decide +kernel)
def c34 : Claim := (4, available 0xd00000068000003404000000 26 inputs)
def r34 : List RE := [(0xc00000060000003000000000,36,0)]
def d34 : List Entry := [([],[0],[])]
def e34 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g34 : GoodC c34 := claim_sound [c10] (gcons g10 gnil) r34 d34 e34 c34 (by decide +kernel)
def c35 : Claim := (3, available 0x531000000000002525800000 23 inputs)
def r35 : List RE := []
def d35 : List Entry := [([],[],[])]
def e35 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g35 : GoodC c35 := claim_sound [] gnil r35 d35 e35 c35 (by decide +kernel)
def c36 : Claim := (3, available 0x298800014a5800000 23 inputs)
def r36 : List RE := []
def d36 : List Entry := [([],[],[])]
def e36 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g36 : GoodC c36 := claim_sound [] gnil r36 d36 e36 c36 (by decide +kernel)
def c37 : Claim := (6, available 0xd7300006b9800035a5800000 23 inputs)
def r37 : List RE := [(0xc03000060180003180000000,31,0),(0x3000000180000180000000,31,1),(0x630000031800001a1000000,24,2),(0xd00000068000003404000000,26,3),(0x531000000000002525800000,23,4),(0x298800014a5800000,23,5)]
def d37 : List Entry := [([],[2,0,1,3,4,5],[0,1,2,3,4])]
def e37 : List (List Entry) := [[([567],[2,3,4],[]),([575],[2,1,4],[0]),([583],[2,3,5],[]),([591],[2,1,5],[1]),([847],[2,4],[])],[([575,80],[],[]),([591,80],[],[])]]
set_option maxRecDepth 100000 in
theorem g37 : GoodC c37 := claim_sound [c32,c1,c33,c34,c35,c36] (gcons g32 (gcons g1 (gcons g33 (gcons g34 (gcons g35 (gcons g36 gnil)))))) r37 d37 e37 c37 (by decide +kernel)
def c38 : Claim := (7, available 0x1df70000efb800077b7a00000 21 inputs)
def r38 : List RE := [(0x1c070000e0380007390200000,21,0),(0xe70000073800003a3200000,21,1),(0xd7300006b9800035a5800000,23,2)]
def d38 : List Entry := [([],[0,1,2],[])]
def e38 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g38 : GoodC c38 := claim_sound [c20,c31,c37] (gcons g20 (gcons g31 (gcons g37 gnil))) r38 d38 e38 c38 (by decide +kernel)
def c39 : Claim := (8, available 0xba0f7e83dfa0fa3bdf7683befbb41df7b7ad0746 1 inputs)
def r39 : List RE := [(0x38007e001f80e803c076003e03b001f3902c0600,9,0),(0xe70039c00f0320e70033073801983a3200704,2,1),(0x1df70000efb800077b7a00000,21,2)]
def d39 : List Entry := [([],[1,0,2],[])]
def e39 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g39 : GoodC c39 := claim_sound [c4,c30,c38] (gcons g4 (gcons g30 (gcons g38 gnil))) r39 d39 e39 c39 (by decide +kernel)
def c40 : Claim := (6, available 0x3a000e8003a00a01d006800e80340074140d0040 6 inputs)
def r40 : List RE := [(0x38000e0003800801c006000e00300070100c0000,18,0)]
def d40 : List Entry := [([],[0],[])]
def e40 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g40 : GoodC c40 := claim_sound [c12] (gcons g12 gnil) r40 d40 e40 c40 (by decide +kernel)
def c41 : Claim := (3, available 0x8a03100002209218000281900000000000090546 1 inputs)
def r41 : List RE := []
def d41 : List Entry := [([4100],[],[]),([],[],[])]
def e41 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g41 : GoodC c41 := claim_sound [] gnil r41 d41 e41 c41 (by decide +kernel)
def c42 : Claim := (5, available 0x9a07300002a0ba3b5b5281900000006737a90546 1 inputs)
def r42 : List RE := [(0x8a03100002209218000281900000000000090546,1,0)]
def d42 : List Entry := [([],[0],[])]
def e42 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g42 : GoodC c42 := claim_sound [c41] (gcons g41 gnil) r42 d42 e42 c42 (by decide +kernel)
def c43 : Claim := (3, available 0x80000280c52052180000000000140c8000050346 1 inputs)
def r43 : List RE := []
def d43 : List Entry := [([4100],[],[]),([],[],[])]
def e43 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g43 : GoodC c43 := claim_sound [] gnil r43 d43 e43 c43 (by decide +kernel)
def c44 : Claim := (5, available 0x80000681cda07a3a0000000ada940cd6b7a50346 1 inputs)
def r44 : List RE := [(0x80000280c52052180000000000140c8000050346,1,0)]
def d44 : List Entry := [([],[0],[])]
def e44 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g44 : GoodC c44 := claim_sound [c43] (gcons g43 gnil) r44 d44 e44 c44 (by decide +kernel)
def c45 : Claim := (5, available 0x1d00074001d0140000074000003a0000000e828 3 inputs)
def r45 : List RE := [(0x1c00070001c010000007000000380000000e020,5,0)]
def d45 : List Entry := [([4101],[0],[]),([],[0],[])]
def e45 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g45 : GoodC c45 := claim_sound [c6] (gcons g6 gnil) r45 d45 e45 c45 (by decide +kernel)
def c46 : Claim := (3, available 0x5000000280000000c000 14 inputs)
def r46 : List RE := []
def d46 : List Entry := [([],[],[])]
def e46 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g46 : GoodC c46 := claim_sound [] gnil r46 d46 e46 c46 (by decide +kernel)
def c47 : Claim := (4, available 0x7000000380000000e020 5 inputs)
def r47 : List RE := [(0x5000000280000000c000,14,0)]
def d47 : List Entry := [([],[0],[])]
def e47 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g47 : GoodC c47 := claim_sound [c46] (gcons g46 gnil) r47 d47 e47 c47 (by decide +kernel)
def c48 : Claim := (5, available 0x78000003c0000000f030 4 inputs)
def r48 : List RE := [(0x7000000380000000e020,5,0)]
def d48 : List Entry := [([],[0],[])]
def e48 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g48 : GoodC c48 := claim_sound [c47] (gcons g47 gnil) r48 d48 e48 c48 (by decide +kernel)
def c49 : Claim := (6, available 0x7c000003e0000000f838 3 inputs)
def r49 : List RE := [(0x78000003c0000000f030,4,0)]
def d49 : List Entry := [([],[0],[])]
def e49 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g49 : GoodC c49 := claim_sound [c48] (gcons g48 gnil) r49 d49 e49 c49 (by decide +kernel)
def c50 : Claim := (5, available 0x74000003a0000000e828 3 inputs)
def r50 : List RE := [(0x7000000380000000e020,5,0)]
def d50 : List Entry := [([],[0],[])]
def e50 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g50 : GoodC c50 := claim_sound [c47] (gcons g47 gnil) r50 d50 e50 c50 (by decide +kernel)
def c51 : Claim := (3, available 0x4094a0000000016608c824400000000002700029 0 inputs)
def r51 : List RE := []
def d51 : List Entry := [([4099],[],[]),([],[],[])]
def e51 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g51 : GoodC c51 := claim_sound [] gnil r51 d51 e51 c51 (by decide +kernel)
def c52 : Claim := (5, available 0x419ce067380001660ce866606743330002700029 0 inputs)
def r52 : List RE := [(0x4094a0000000016608c824400000000002700029,0,0)]
def d52 : List Entry := [([],[0],[])]
def e52 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g52 : GoodC c52 := claim_sound [c51] (gcons g51 gnil) r52 d52 e52 c52 (by decide +kernel)
def c53 : Claim := (4, available 0x6738000000000000006743330000000000 40 inputs)
def r53 : List RE := []
def d53 : List Entry := [([],[],[])]
def e53 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g53 : GoodC c53 := claim_sound [] gnil r53 d53 e53 c53 (by decide +kernel)
def c54 : Claim := (4, available 0x19ce000000000000ce866600000000000000000 69 inputs)
def r54 : List RE := []
def d54 : List Entry := [([],[],[])]
def e54 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g54 : GoodC c54 := claim_sound [] gnil r54 d54 e54 c54 (by decide +kernel)
def c55 : Claim := (3, available 0x14050501418c00000005030000281800000c600 9 inputs)
def r55 : List RE := []
def d55 : List Entry := [([4100,4096],[],[]),([4100],[],[]),([4096],[],[]),([],[],[])]
def e55 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g55 : GoodC c55 := claim_sound [] gnil r55 d55 e55 c55 (by decide +kernel)
def c56 : Claim := (4, available 0xa50029400d010000003300000198000000704 2 inputs)
def r56 : List RE := [(0x50001400c000000000300000018000000600,9,0)]
def d56 : List Entry := [([4100],[0],[]),([],[],[])]
def e56 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g56 : GoodC c56 := claim_sound [c0] (gcons g0 gnil) r56 d56 e56 c56 (by decide +kernel)
def c57 : Claim := (3, available 0x5030000281800000c600 9 inputs)
def r57 : List RE := []
def d57 : List Entry := [([4096],[],[]),([],[],[])]
def e57 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g57 : GoodC c57 := claim_sound [] gnil r57 d57 e57 c57 (by decide +kernel)
def c58 : Claim := (3, available 0x300000018000000600 9 inputs)
def r58 : List RE := []
def d58 : List Entry := [([],[],[])]
def e58 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g58 : GoodC c58 := claim_sound [] gnil r58 d58 e58 c58 (by decide +kernel)
def c59 : Claim := (4, available 0x3300000198000000704 2 inputs)
def r59 : List RE := [(0x300000018000000600,9,0)]
def d59 : List Entry := [([],[0],[])]
def e59 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g59 : GoodC c59 := claim_sound [c58] (gcons g58 gnil) r59 d59 e59 c59 (by decide +kernel)
def c60 : Claim := (4, available 0x54000002a0000000c808 3 inputs)
def r60 : List RE := [(0x5000000280000000c000,14,0)]
def d60 : List Entry := [([],[0],[])]
def e60 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g60 : GoodC c60 := claim_sound [c46] (gcons g46 gnil) r60 d60 e60 c60 (by decide +kernel)
def c61 : Claim := (3, available 0x4000000000000000000015500000000000008d0d 0 inputs)
def r61 : List RE := []
def d61 : List Entry := [([],[],[])]
def e61 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g61 : GoodC c61 := claim_sound [] gnil r61 d61 e61 c61 (by decide +kernel)
def c62 : Claim := (3, available 0x4000000000000000000000000000aa8000004b0d 0 inputs)
def r62 : List RE := []
def d62 : List Entry := [([],[],[])]
def e62 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g62 : GoodC c62 := claim_sound [] gnil r62 d62 e62 c62 (by decide +kernel)
def c63 : Claim := (6, available 0x4000000000000000000057700002bb800000cf0d 0 inputs)
def r63 : List RE := [(0x5030000281800000c600,9,0),(0x300000018000000600,9,1),(0x3300000198000000704,2,2),(0x54000002a0000000c808,3,3),(0x4000000000000000000015500000000000008d0d,0,4),(0x4000000000000000000000000000aa8000004b0d,0,5)]
def d63 : List Entry := [([],[2,0,1,3,4,5],[0,1,2,3,4])]
def e63 : List (List Entry) := [[([567],[2,3,4],[]),([575],[2,1,4],[0]),([583],[2,3,5],[]),([591],[2,1,5],[1]),([847],[2,4],[])],[([575,80],[],[]),([591,80],[],[])]]
set_option maxRecDepth 100000 in
theorem g63 : GoodC c63 := claim_sound [c57,c58,c59,c60,c61,c62] (gcons g57 (gcons g58 (gcons g59 (gcons g60 (gcons g61 (gcons g62 gnil)))))) r63 d63 e63 c63 (by decide +kernel)
def c64 : Claim := (6, available 0x415ad056b419d054000057700002bb800000cf0d 0 inputs)
def r64 : List RE := [(0x14050501418c00000005030000281800000c600,9,0),(0xa50029400d010000003300000198000000704,2,1),(0x4000000000000000000057700002bb800000cf0d,0,2)]
def d64 : List Entry := [([4101],[1,0,2],[]),([],[0,2],[])]
def e64 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g64 : GoodC c64 := claim_sound [c55,c56,c63] (gcons g55 (gcons g56 (gcons g63 gnil))) r64 d64 e64 c64 (by decide +kernel)
def c65 : Claim := (5, available 0x78000003c00003c0300000 20 inputs)
def r65 : List RE := [(0x7000000380000380200000,21,0)]
def d65 : List Entry := [([],[0],[])]
def e65 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g65 : GoodC c65 := claim_sound [c2] (gcons g2 gnil) r65 d65 e65 c65 (by decide +kernel)
def c66 : Claim := (6, available 0xef8000077c00003e3700000 20 inputs)
def r66 : List RE := [(0x78000003c00003c0300000,20,0)]
def d66 : List Entry := [([],[0],[])]
def e66 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g66 : GoodC c66 := claim_sound [c65] (gcons g65 gnil) r66 d66 e66 c66 (by decide +kernel)
def c67 : Claim := (4, available 0x400000000005317600000000000000026370292d 0 inputs)
def r67 : List RE := []
def d67 : List Entry := [([],[],[])]
def e67 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g67 : GoodC c67 := claim_sound [] gnil r67 d67 e67 c67 (by decide +kernel)
def c68 : Claim := (4, available 0xd6b000000000000ad835500000000000000000 68 inputs)
def r68 : List RE := []
def d68 : List Entry := [([],[],[])]
def e68 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g68 : GoodC c68 := claim_sound [] gnil r68 d68 e68 c68 (by decide +kernel)
def c69 : Claim := (4, available 0x400000000000000002983550000000016150ad2d 0 inputs)
def r69 : List RE := []
def d69 : List Entry := [([],[],[])]
def e69 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g69 : GoodC c69 := claim_sound [] gnil r69 d69 e69 c69 (by decide +kernel)
def c70 : Claim := (4, available 0xd6b0000015b176000000000000000000000000 97 inputs)
def r70 : List RE := []
def d70 : List Entry := [([],[],[])]
def e70 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g70 : GoodC c70 := claim_sound [] gnil r70 d70 e70 c70 (by decide +kernel)
def c71 : Claim := (6, available 0x40d6b0000015b1760ad83550000000036370ad2d 0 inputs)
def r71 : List RE := [(0x400000000005317600000000000000026370292d,0,0),(0xd6b000000000000ad835500000000000000000,68,1),(0x400000000000000002983550000000016150ad2d,0,2),(0xd6b0000015b176000000000000000000000000,97,3)]
def d71 : List Entry := [([],[0,1,2,3],[])]
def e71 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g71 : GoodC c71 := claim_sound [c67,c68,c69,c70] (gcons g67 (gcons g68 (gcons g69 (gcons g70 gnil)))) r71 d71 e71 c71 (by decide +kernel)
def c72 : Claim := (4, available 0x35ac0000000000000056c1aa8000000000 39 inputs)
def r72 : List RE := []
def d72 : List Entry := [([],[],[])]
def e72 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g72 : GoodC c72 := claim_sound [] gnil r72 d72 e72 c72 (by decide +kernel)
def c73 : Claim := (4, available 0x40000000000000000000000014c1aa80e1506b2d 0 inputs)
def r73 : List RE := []
def d73 : List Entry := [([],[],[])]
def e73 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g73 : GoodC c73 := claim_sound [] gnil r73 d73 e73 c73 (by decide +kernel)
def c74 : Claim := (4, available 0x35ac0d7176000000000000000000000000 97 inputs)
def r74 : List RE := []
def d74 : List Entry := [([],[],[])]
def e74 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g74 : GoodC c74 := claim_sound [] gnil r74 d74 e74 c74 (by decide +kernel)
def c75 : Claim := (6, available 0x40000035ac0d71760000000056c1aa82e3706b2d 0 inputs)
def r75 : List RE := [(0x400000000005317600000000000000026370292d,0,0),(0x35ac0000000000000056c1aa8000000000,39,1),(0x40000000000000000000000014c1aa80e1506b2d,0,2),(0x35ac0d7176000000000000000000000000,97,3)]
def d75 : List Entry := [([],[0,1,2,3],[])]
def e75 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g75 : GoodC c75 := claim_sound [c67,c72,c73,c74] (gcons g67 (gcons g72 (gcons g73 (gcons g74 gnil)))) r75 d75 e75 c75 (by decide +kernel)
def c76 : Claim := (5, available 0x38703001c38181c010e620 5 inputs)
def r76 : List RE := [(0x7000000380000000e020,5,0)]
def d76 : List Entry := [([],[0],[])]
def e76 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g76 : GoodC c76 := claim_sound [c47] (gcons g47 gnil) r76 d76 e76 c76 (by decide +kernel)
def c77 : Claim := (3, available 0x3000300180018180000600 9 inputs)
def r77 : List RE := []
def d77 : List Entry := [([4097],[],[]),([],[],[])]
def e77 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g77 : GoodC c77 := claim_sound [] gnil r77 d77 e77 c77 (by decide +kernel)
def c78 : Claim := (4, available 0x630033031801981a1000704 2 inputs)
def r78 : List RE := [(0x3000300180018180000600,9,0)]
def d78 : List Entry := [([4098],[0],[]),([],[],[])]
def e78 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g78 : GoodC c78 := claim_sound [c77] (gcons g77 gnil) r78 d78 e78 c78 (by decide +kernel)
def c79 : Claim := (7, available 0x400000000000000006b8777035c3bb81e150ef2d 0 inputs)
def r79 : List RE := [(0x38703001c38181c010e620,5,0),(0x630033031801981a1000704,2,1),(0x74000003a0000000e828,3,2),(0x4000000000000000000057700002bb800000cf0d,0,3)]
def d79 : List Entry := [([],[0,1,2,3],[])]
def e79 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g79 : GoodC c79 := claim_sound [c76,c78,c50,c63] (gcons g76 (gcons g78 (gcons g50 (gcons g63 gnil)))) r79 d79 e79 c79 (by decide +kernel)
def c80 : Claim := (3, available 0x50001400c000000000000000000000000000 110 inputs)
def r80 : List RE := []
def d80 : List Entry := [([],[],[])]
def e80 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g80 : GoodC c80 := claim_sound [] gnil r80 d80 e80 c80 (by decide +kernel)
def c81 : Claim := (4, available 0x70001c00e002000000000000000000000000 97 inputs)
def r81 : List RE := [(0x50001400c000000000000000000000000000,110,0)]
def d81 : List Entry := [([],[0],[])]
def e81 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g81 : GoodC c81 := claim_sound [c80] (gcons g80 gnil) r81 d81 e81 c81 (by decide +kernel)
def c82 : Claim := (4, available 0x1c070701c1ce102000000000000000000000000 97 inputs)
def r82 : List RE := [(0x70001c00e002000000000000000000000000,97,0)]
def d82 : List Entry := [([4096],[0],[]),([],[],[])]
def e82 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g82 : GoodC c82 := claim_sound [c81] (gcons g81 gnil) r82 d82 e82 c82 (by decide +kernel)
def c83 : Claim := (5, available 0xe70039c00f032000000000000000000000000 97 inputs)
def r83 : List RE := [(0x70001c00e002000000000000000000000000,97,0)]
def d83 : List Entry := [([],[0],[])]
def e83 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g83 : GoodC c83 := claim_sound [c81] (gcons g81 gnil) r83 d83 e83 c83 (by decide +kernel)
def c84 : Claim := (3, available 0x14050501418c000000000000000000000000000 110 inputs)
def r84 : List RE := []
def d84 : List Entry := [([4096],[],[]),([],[],[])]
def e84 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g84 : GoodC c84 := claim_sound [] gnil r84 d84 e84 c84 (by decide +kernel)
def c85 : Claim := (4, available 0xa50029400d010000000000000000000000000 100 inputs)
def r85 : List RE := [(0x50001400c000000000000000000000000000,110,0)]
def d85 : List Entry := [([],[0],[])]
def e85 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g85 : GoodC c85 := claim_sound [c80] (gcons g80 gnil) r85 d85 e85 c85 (by decide +kernel)
def c86 : Claim := (3, available 0x140005000180000000000000000000000000000 115 inputs)
def r86 : List RE := []
def d86 : List Entry := [([],[],[])]
def e86 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g86 : GoodC c86 := claim_sound [] gnil r86 d86 e86 c86 (by decide +kernel)
def c87 : Claim := (4, available 0x150005400190040000000000000000000000000 102 inputs)
def r87 : List RE := [(0x140005000180000000000000000000000000000,115,0)]
def d87 : List Entry := [([],[0],[])]
def e87 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g87 : GoodC c87 := claim_sound [c86] (gcons g86 gnil) r87 d87 e87 c87 (by decide +kernel)
def c88 : Claim := (3, available 0x52900000119054000000000000000000000000 98 inputs)
def r88 : List RE := []
def d88 : List Entry := [([],[],[])]
def e88 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g88 : GoodC c88 := claim_sound [] gnil r88 d88 e88 c88 (by decide +kernel)
def c89 : Claim := (3, available 0x14a4095054000000000000000000000000 98 inputs)
def r89 : List RE := []
def d89 : List Entry := [([],[],[])]
def e89 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g89 : GoodC c89 := claim_sound [] gnil r89 d89 e89 c89 (by decide +kernel)
def c90 : Claim := (6, available 0x15ad056b419d054000000000000000000000000 98 inputs)
def r90 : List RE := [(0x14050501418c000000000000000000000000000,110,0),(0x50001400c000000000000000000000000000,110,1),(0xa50029400d010000000000000000000000000,100,2),(0x150005400190040000000000000000000000000,102,3),(0x52900000119054000000000000000000000000,98,4),(0x14a4095054000000000000000000000000,98,5)]
def d90 : List Entry := [([],[2,0,1,3,4,5],[0,1,2,3,4])]
def e90 : List (List Entry) := [[([567],[2,3,4],[]),([575],[2,1,4],[0]),([583],[2,3,5],[]),([591],[2,1,5],[1]),([847],[2,4],[])],[([575,80],[],[]),([591,80],[],[])]]
set_option maxRecDepth 100000 in
theorem g90 : GoodC c90 := claim_sound [c84,c80,c85,c87,c88,c89] (gcons g84 (gcons g80 (gcons g85 (gcons g87 (gcons g88 (gcons g89 gnil)))))) r90 d90 e90 c90 (by decide +kernel)
def c91 : Claim := (7, available 0x1def077bc1df176000000000000000000000000 97 inputs)
def r91 : List RE := [(0x1c070701c1ce102000000000000000000000000,97,0),(0xe70039c00f032000000000000000000000000,97,1),(0x15ad056b419d054000000000000000000000000,98,2)]
def d91 : List Entry := [([],[0,1,2],[])]
def e91 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g91 : GoodC c91 := claim_sound [c82,c83,c90] (gcons g82 (gcons g83 (gcons g90 gnil))) r91 d91 e91 c91 (by decide +kernel)
def c92 : Claim := (9, available 0x41def077bc1df1760ef8777077c3bb83e370ef2d 0 inputs)
def r92 : List RE := [(0x70001c00e002007000300380018380200600,9,0),(0xe70039c00f0320e70033073801983a3200704,2,1),(0x74000003a0000000e828,3,2),(0x419ce067380001660ce866606743330002700029,0,3),(0x6738000000000000006743330000000000,40,4),(0x19ce000000000000ce866600000000000000000,69,5),(0x415ad056b419d054000057700002bb800000cf0d,0,6),(0xef8000077c00003e3700000,20,7),(0x40d6b0000015b1760ad83550000000036370ad2d,0,8),(0x400000000005317600000000000000026370292d,0,9),(0xd6b000000000000ad835500000000000000000,68,10),(0x40000035ac0d71760000000056c1aa82e3706b2d,0,11),(0x400000000000000006b8777035c3bb81e150ef2d,0,12),(0x1def077bc1df176000000000000000000000000,97,13)]
def d92 : List Entry := [([],[1,0,6,7,8,11,12,2,13],[0,1,2,3,4,5,6,7,8])]
def e92 : List (List Entry) := [[([35],[0,3,6,7,8,4,11,5,12],[]),([39],[12,3,0,6,7,8,4,11,5],[]),([71],[8,0,4,6,7,11,10,12],[]),([87],[11,0,5,6,7,8,10,12],[]),([583],[3,8,0,2,6,7,11,5,12,13],[0]),([591],[8,3,0,4,2,6,7,11,5,12,10,13],[1,2,3]),([599],[3,11,0,2,6,7,8,4,12,13],[4]),([607],[11,3,0,5,2,6,7,8,4,12,10,13],[5,6,7]),([1119],[8,11,9,4,12,13],[])],[([583,58],[3],[]),([591,50],[8],[]),([591,96],[11,3,8,4,12,13],[]),([591,100],[12,13],[]),([599,58],[3],[]),([607,50],[11],[]),([607,96],[8,3,11,5,12,13],[]),([607,100],[12,13],[])]]
set_option maxRecDepth 100000 in
theorem g92 : GoodC c92 := claim_sound [c3,c30,c50,c52,c53,c54,c64,c66,c71,c67,c68,c75,c79,c91] (gcons g3 (gcons g30 (gcons g50 (gcons g52 (gcons g53 (gcons g54 (gcons g64 (gcons g66 (gcons g71 (gcons g67 (gcons g68 (gcons g75 (gcons g79 (gcons g91 gnil)))))))))))))) r92 d92 e92 c92 (by decide +kernel)
def c93 : Claim := (5, available 0x77bc0000000000000077c3bb8000000000 39 inputs)
def r93 : List RE := [(0x6738000000000000006743330000000000,40,0)]
def d93 : List Entry := [([],[0],[])]
def e93 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g93 : GoodC c93 := claim_sound [c53] (gcons g53 gnil) r93 d93 e93 c93 (by decide +kernel)
def c94 : Claim := (5, available 0x1def000000000000ef877700000000000000000 68 inputs)
def r94 : List RE := [(0x19ce000000000000ce866600000000000000000,69,0)]
def d94 : List Entry := [([],[0],[])]
def e94 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g94 : GoodC c94 := claim_sound [c54] (gcons g54 gnil) r94 d94 e94 c94 (by decide +kernel)
def c95 : Claim := (5, available 0x1e000000f0000007818000000 27 inputs)
def r95 : List RE := [(0x1c000000e0000007010000000,28,0)]
def d95 : List Entry := [([],[0],[])]
def e95 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g95 : GoodC c95 := claim_sound [c11] (gcons g11 gnil) r95 d95 e95 c95 (by decide +kernel)
def c96 : Claim := (6, available 0x1f000000f8000007c1c000000 26 inputs)
def r96 : List RE := [(0x1e000000f0000007818000000,27,0)]
def d96 : List Entry := [([],[0],[])]
def e96 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g96 : GoodC c96 := claim_sound [c95] (gcons g95 gnil) r96 d96 e96 c96 (by decide +kernel)
def c97 : Claim := (3, available 0xd820000000000000000183000b0 4 inputs)
def r97 : List RE := []
def d97 : List Entry := [([],[],[])]
def e97 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g97 : GoodC c97 := claim_sound [] gnil r97 d97 e97 c97 (by decide +kernel)
def c98 : Claim := (3, available 0x4000000000000166000000000000000002700029 0 inputs)
def r98 : List RE := []
def d98 : List Entry := [([],[],[])]
def e98 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g98 : GoodC c98 := claim_sound [] gnil r98 d98 e98 c98 (by decide +kernel)
def c99 : Claim := (3, available 0xc0000000000000000000000000000000000000db 0 inputs)
def r99 : List RE := []
def d99 : List Entry := [([],[],[])]
def e99 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g99 : GoodC c99 := claim_sound [] gnil r99 d99 e99 c99 (by decide +kernel)
def c100 : Claim := (4, available 0xc00000000000000000000000000000000cd000fb 0 inputs)
def r100 : List RE := [(0xc0000000000000000000000000000000000000db,0,0)]
def d100 : List Entry := [([],[0],[])]
def e100 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g100 : GoodC c100 := claim_sound [c99] (gcons g99 gnil) r100 d100 e100 c100 (by decide +kernel)
def c101 : Claim := (3, available 0x6cc000000000000000000000000 98 inputs)
def r101 : List RE := []
def d101 : List Entry := [([],[],[])]
def e101 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g101 : GoodC c101 := claim_sound [] gnil r101 d101 e101 c101 (by decide +kernel)
def c102 : Claim := (4, available 0xfee000000000000000000000000 97 inputs)
def r102 : List RE := [(0x6cc000000000000000000000000,98,0)]
def d102 : List Entry := [([],[0],[])]
def e102 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g102 : GoodC c102 := claim_sound [c101] (gcons g101 gnil) r102 d102 e102 c102 (by decide +kernel)
def c103 : Claim := (6, available 0xc000000000000fee00000000000000001ef000fb 0 inputs)
def r103 : List RE := [(0xd820000000000000000183000b0,4,0),(0x4000000000000166000000000000000002700029,0,1),(0xc0000000000000000000000000000000000000db,0,2),(0xc00000000000000000000000000000000cd000fb,0,3),(0xfee000000000000000000000000,97,4)]
def d103 : List Entry := [([],[0,1,2,4],[0,1,2,3,4])]
def e103 : List (List Entry) := [[([19],[0,3,4],[]),([23],[0,2],[0]),([39],[0],[]),([295],[1,3,4],[]),([303],[1,2],[1])],[([23,56],[],[]),([303,52],[],[])]]
set_option maxRecDepth 100000 in
theorem g103 : GoodC c103 := claim_sound [c97,c98,c99,c100,c102] (gcons g97 (gcons g98 (gcons g99 (gcons g100 (gcons g102 gnil))))) r103 d103 e103 c103 (by decide +kernel)
def c104 : Claim := (6, available 0xd6b5a00000000fef39c9acc0000000001ef000fb 0 inputs)
def r104 : List RE := [(0xc000000000000fee00000000000000001ef000fb,0,0)]
def d104 : List Entry := [([4100],[0],[]),([],[0],[])]
def e104 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g104 : GoodC c104 := claim_sound [c103] (gcons g103 gnil) r104 d104 e104 c104 (by decide +kernel)
def c105 : Claim := (3, available 0x52808000000000000090249400000000000 46 inputs)
def r105 : List RE := []
def d105 : List Entry := [([],[],[])]
def e105 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g105 : GoodC c105 := claim_sound [] gnil r105 d105 e105 c105 (by decide +kernel)
def c106 : Claim := (3, available 0x2528000000000000004641220000000000 41 inputs)
def r106 : List RE := []
def d106 : List Entry := [([],[],[])]
def e106 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g106 : GoodC c106 := claim_sound [] gnil r106 d106 e106 c106 (by decide +kernel)
def c107 : Claim := (3, available 0xc660000000000 41 inputs)
def r107 : List RE := []
def d107 : List Entry := [([],[],[])]
def e107 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g107 : GoodC c107 := claim_sound [] gnil r107 d107 e107 c107 (by decide +kernel)
def c108 : Claim := (4, available 0x18c4d660000000000 41 inputs)
def r108 : List RE := [(0xc660000000000,41,0)]
def d108 : List Entry := [([],[0],[])]
def e108 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g108 : GoodC c108 := claim_sound [c107] (gcons g107 gnil) r108 d108 e108 c108 (by decide +kernel)
def c109 : Claim := (3, available 0x18c60000000000000000000000000000000 125 inputs)
def r109 : List RE := []
def d109 : List Entry := [([],[],[])]
def e109 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g109 : GoodC c109 := claim_sound [] gnil r109 d109 e109 c109 (by decide +kernel)
def c110 : Claim := (4, available 0x5ad68000000000000000000000000000000 123 inputs)
def r110 : List RE := [(0x18c60000000000000000000000000000000,125,0)]
def d110 : List Entry := [([],[0],[])]
def e110 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g110 : GoodC c110 := claim_sound [c109] (gcons g109 gnil) r110 d110 e110 c110 (by decide +kernel)
def c111 : Claim := (6, available 0x5ad6800000000000009ce4d660000000000 41 inputs)
def r111 : List RE := [(0x52808000000000000090249400000000000,46,0),(0x2528000000000000004641220000000000,41,1),(0xc660000000000,41,2),(0x18c4d660000000000,41,3),(0x5ad68000000000000000000000000000000,123,4)]
def d111 : List Entry := [([],[0,1,2,4],[0,1,2,3,4])]
def e111 : List (List Entry) := [[([19],[0,3,4],[]),([23],[0,2],[0]),([39],[0],[]),([295],[1,3,4],[]),([303],[1,2],[1])],[([23,56],[],[]),([303,52],[],[])]]
set_option maxRecDepth 100000 in
theorem g111 : GoodC c111 := claim_sound [c105,c106,c107,c108,c110] (gcons g105 (gcons g106 (gcons g107 (gcons g108 (gcons g110 gnil))))) r111 d111 e111 c111 (by decide +kernel)
def c112 : Claim := (7, available 0xdef780000000000000def6f770000000000 40 inputs)
def r112 : List RE := [(0xd68180000000000000d036b410000000000,40,0),(0x5ad6800000000000009ce4d660000000000,41,1)]
def d112 : List Entry := [([],[0,1],[])]
def e112 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g112 : GoodC c112 := claim_sound [c23,c111] (gcons g23 (gcons g111 gnil)) r112 d112 e112 c112 (by decide +kernel)
def c113 : Claim := (6, available 0xc00005ad68000fee00000009ce4d66001ef000fb 0 inputs)
def r113 : List RE := [(0xc000000000000fee00000000000000001ef000fb,0,0)]
def d113 : List Entry := [([4100],[0],[]),([],[0],[])]
def e113 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g113 : GoodC c113 := claim_sound [c103] (gcons g103 gnil) r113 d113 e113 c113 (by decide +kernel)
def c114 : Claim := (3, available 0x14a0200000000001204928000000000000000000 75 inputs)
def r114 : List RE := []
def d114 : List Entry := [([],[],[])]
def e114 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g114 : GoodC c114 := claim_sound [] gnil r114 d114 e114 c114 (by decide +kernel)
def c115 : Claim := (3, available 0x94a0000000000008c824400000000000000000 70 inputs)
def r115 : List RE := []
def d115 : List Entry := [([],[],[])]
def e115 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g115 : GoodC c115 := claim_sound [] gnil r115 d115 e115 c115 (by decide +kernel)
def c116 : Claim := (3, available 0x18cc00000000000000000 70 inputs)
def r116 : List RE := []
def d116 : List Entry := [([],[],[])]
def e116 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g116 : GoodC c116 := claim_sound [] gnil r116 d116 e116 c116 (by decide +kernel)
def c117 : Claim := (4, available 0x3189acc00000000000000000 70 inputs)
def r117 : List RE := [(0x18cc00000000000000000,70,0)]
def d117 : List Entry := [([],[0],[])]
def e117 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g117 : GoodC c117 := claim_sound [c116] (gcons g116 gnil) r117 d117 e117 c117 (by decide +kernel)
def c118 : Claim := (3, available 0x631800000000000000000000000000000000000 143 inputs)
def r118 : List RE := []
def d118 : List Entry := [([],[],[])]
def e118 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g118 : GoodC c118 := claim_sound [] gnil r118 d118 e118 c118 (by decide +kernel)
def c119 : Claim := (4, available 0x16b5a00000000000000000000000000000000000 141 inputs)
def r119 : List RE := [(0x631800000000000000000000000000000000000,143,0)]
def d119 : List Entry := [([],[0],[])]
def e119 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g119 : GoodC c119 := claim_sound [c118] (gcons g118 gnil) r119 d119 e119 c119 (by decide +kernel)
def c120 : Claim := (6, available 0x16b5a0000000000139c9acc00000000000000000 70 inputs)
def r120 : List RE := [(0x14a0200000000001204928000000000000000000,75,0),(0x94a0000000000008c824400000000000000000,70,1),(0x18cc00000000000000000,70,2),(0x3189acc00000000000000000,70,3),(0x16b5a00000000000000000000000000000000000,141,4)]
def d120 : List Entry := [([],[0,1,2,4],[0,1,2,3,4])]
def e120 : List (List Entry) := [[([19],[0,3,4],[]),([23],[0,2],[0]),([39],[0],[]),([295],[1,3,4],[]),([303],[1,2],[1])],[([23,56],[],[]),([303,52],[],[])]]
set_option maxRecDepth 100000 in
theorem g120 : GoodC c120 := claim_sound [c114,c115,c116,c117,c119] (gcons g114 (gcons g115 (gcons g116 (gcons g117 (gcons g119 gnil))))) r120 d120 e120 c120 (by decide +kernel)
def c121 : Claim := (7, available 0x37bde00000000001bdedeee00000000000000000 69 inputs)
def r121 : List RE := [(0x35a0600000000001a06d68200000000000000000,69,0),(0x16b5a0000000000139c9acc00000000000000000,70,1)]
def d121 : List Entry := [([],[0,1],[])]
def e121 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g121 : GoodC c121 := claim_sound [c27,c120] (gcons g27 (gcons g120 gnil)) r121 d121 e121 c121 (by decide +kernel)
def c122 : Claim := (5, available 0x2f7b000000000000000006f600bbd00 8 inputs)
def r122 : List RE := [(0x2d6a000000000000000006b400ab400,10,0)]
def d122 : List Entry := [([],[0],[])]
def e122 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g122 : GoodC c122 := claim_sound [c16] (gcons g16 gnil) r122 d122 e122 c122 (by decide +kernel)
def c123 : Claim := (4, available 0x1ce6000000000000000005ac0067200 9 inputs)
def r123 : List RE := []
def d123 : List Entry := [([],[],[])]
def e123 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g123 : GoodC c123 := claim_sound [] gnil r123 d123 e123 c123 (by decide +kernel)
def c124 : Claim := (5, available 0x1ef7000000000000000005ee0077b00 8 inputs)
def r124 : List RE := [(0x1ce6000000000000000005ac0067200,9,0)]
def d124 : List Entry := [([],[0],[])]
def e124 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g124 : GoodC c124 := claim_sound [c123] (gcons g123 gnil) r124 d124 e124 c124 (by decide +kernel)
def c125 : Claim := (3, available 0x28005a001700c0000006003000300180000c0600 9 inputs)
def r125 : List RE := []
def d125 : List Entry := [([4100,4096],[],[]),([4100],[],[]),([4096],[],[]),([],[],[])]
def e125 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g125 : GoodC c125 := claim_sound [] gnil r125 d125 e125 c125 (by decide +kernel)
def c126 : Claim := (3, available 0x6003000300180000c0600 9 inputs)
def r126 : List RE := []
def d126 : List Entry := [([4096],[],[]),([],[],[])]
def e126 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g126 : GoodC c126 := claim_sound [] gnil r126 d126 e126 c126 (by decide +kernel)
def c127 : Claim := (3, available 0x6000000300000000c0000 18 inputs)
def r127 : List RE := []
def d127 : List Entry := [([],[],[])]
def e127 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g127 : GoodC c127 := claim_sound [] gnil r127 d127 e127 c127 (by decide +kernel)
def c128 : Claim := (4, available 0x6800000340000000d0040 6 inputs)
def r128 : List RE := [(0x6000000300000000c0000,18,0)]
def d128 : List Entry := [([],[0],[])]
def e128 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g128 : GoodC c128 := claim_sound [c127] (gcons g127 gnil) r128 d128 e128 c128 (by decide +kernel)
def c129 : Claim := (3, available 0x8000000000000000000281900000000000090546 1 inputs)
def r129 : List RE := []
def d129 : List Entry := [([],[],[])]
def e129 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g129 : GoodC c129 := claim_sound [] gnil r129 d129 e129 c129 (by decide +kernel)
def c130 : Claim := (3, available 0x80000000000000000000000000140c8000050346 1 inputs)
def r130 : List RE := []
def d130 : List Entry := [([],[],[])]
def e130 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g130 : GoodC c130 := claim_sound [] gnil r130 d130 e130 c130 (by decide +kernel)
def c131 : Claim := (6, available 0x8000000000000000000683b000341d80000d0746 1 inputs)
def r131 : List RE := [(0x6003000300180000c0600,9,0),(0x300000018000000600,9,1),(0x3300000198000000704,2,2),(0x6800000340000000d0040,6,3),(0x8000000000000000000281900000000000090546,1,4),(0x80000000000000000000000000140c8000050346,1,5)]
def d131 : List Entry := [([],[2,0,1,3,4,5],[0,1,2,3,4])]
def e131 : List (List Entry) := [[([567],[2,3,4],[]),([575],[2,1,4],[0]),([583],[2,3,5],[]),([591],[2,1,5],[1]),([847],[2,4],[])],[([575,80],[],[]),([591,80],[],[])]]
set_option maxRecDepth 100000 in
theorem g131 : GoodC c131 := claim_sound [c126,c58,c59,c128,c129,c130] (gcons g126 (gcons g58 (gcons g59 (gcons g128 (gcons g129 (gcons g130 gnil)))))) r131 d131 e131 c131 (by decide +kernel)
def c132 : Claim := (6, available 0xaa0b5a82d720d218000683b000341d80000d0746 1 inputs)
def r132 : List RE := [(0x28005a001700c0000006003000300180000c0600,9,0),(0xa50029400d010000003300000198000000704,2,1),(0x8000000000000000000683b000341d80000d0746,1,2)]
def d132 : List Entry := [([4101],[1,0,2],[]),([],[0,2],[])]
def e132 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g132 : GoodC c132 := claim_sound [c125,c56,c131] (gcons g125 (gcons g56 (gcons g131 gnil))) r132 d132 e132 c132 (by decide +kernel)
def c133 : Claim := (4, available 0x58000002c0000000d010 4 inputs)
def r133 : List RE := [(0x5000000280000000c000,14,0)]
def d133 : List Entry := [([],[0],[])]
def e133 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g133 : GoodC c133 := claim_sound [c46] (gcons g46 gnil) r133 d133 e133 c133 (by decide +kernel)
def c134 : Claim := (5, available 0x75830003ac180000ed690 4 inputs)
def r134 : List RE := [(0x58000002c0000000d010,4,0)]
def d134 : List Entry := [([],[0],[])]
def e134 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g134 : GoodC c134 := claim_sound [c133] (gcons g133 gnil) r134 d134 e134 c134 (by decide +kernel)
def c135 : Claim := (4, available 0x7000000380000000e0080 7 inputs)
def r135 : List RE := [(0x6000000300000000c0000,18,0)]
def d135 : List Entry := [([],[0],[])]
def e135 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g135 : GoodC c135 := claim_sound [c127] (gcons g127 gnil) r135 d135 e135 c135 (by decide +kernel)
def c136 : Claim := (5, available 0x5c000002e0000000d818 3 inputs)
def r136 : List RE := [(0x58000002c0000000d010,4,0)]
def d136 : List Entry := [([],[0],[])]
def e136 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g136 : GoodC c136 := claim_sound [c133] (gcons g133 gnil) r136 d136 e136 c136 (by decide +kernel)
def c137 : Claim := (3, available 0xc00000000000000000018cc000000000000000db 0 inputs)
def r137 : List RE := []
def d137 : List Entry := [([4099],[],[]),([],[],[])]
def e137 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g137 : GoodC c137 := claim_sound [] gnil r137 d137 e137 c137 (by decide +kernel)
def c138 : Claim := (4, available 0x2e770000000000 40 inputs)
def r138 : List RE := [(0xc660000000000,41,0)]
def d138 : List Entry := [([],[0],[])]
def e138 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g138 : GoodC c138 := claim_sound [c107] (gcons g107 gnil) r138 d138 e138 c138 (by decide +kernel)
def c139 : Claim := (3, available 0xc00000000000000000000000000c6600000000db 0 inputs)
def r139 : List RE := []
def d139 : List Entry := [([4099],[],[]),([],[],[])]
def e139 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g139 : GoodC c139 := claim_sound [] gnil r139 d139 e139 c139 (by decide +kernel)
def c140 : Claim := (4, available 0x5cee00000000000000000 69 inputs)
def r140 : List RE := [(0x18cc00000000000000000,70,0)]
def d140 : List Entry := [([],[0],[])]
def e140 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g140 : GoodC c140 := claim_sound [c116] (gcons g116 gnil) r140 d140 e140 c140 (by decide +kernel)
def c141 : Claim := (4, available 0x39dd00000000000000000 68 inputs)
def r141 : List RE := [(0x18cc00000000000000000,70,0)]
def d141 : List Entry := [([],[0],[])]
def e141 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g141 : GoodC c141 := claim_sound [c116] (gcons g116 gnil) r141 d141 e141 c141 (by decide +kernel)
def c142 : Claim := (6, available 0xc00000000000000000039dd000000000000b9ddf 0 inputs)
def r142 : List RE := [(0x8000000000000000000281900000000000090546,1,0),(0x4000000000000000000015500000000000008d0d,0,1),(0xc0000000000000000000000000000000000000db,0,2),(0x39dd00000000000000000,68,3)]
def d142 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e142 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g142 : GoodC c142 := claim_sound [c129,c61,c99,c141] (gcons g129 (gcons g61 (gcons g99 (gcons g141 gnil)))) r142 d142 e142 c142 (by decide +kernel)
def c143 : Claim := (4, available 0xc0000000000000000000000000000000000319df 0 inputs)
def r143 : List RE := [(0xc0000000000000000000000000000000000000db,0,0)]
def d143 : List Entry := [([],[0],[])]
def e143 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g143 : GoodC c143 := claim_sound [c99] (gcons g99 gnil) r143 d143 e143 c143 (by decide +kernel)
def c144 : Claim := (4, available 0x1cee8000000000 39 inputs)
def r144 : List RE := [(0xc660000000000,41,0)]
def d144 : List Entry := [([],[0],[])]
def e144 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g144 : GoodC c144 := claim_sound [c107] (gcons g107 gnil) r144 d144 e144 c144 (by decide +kernel)
def c145 : Claim := (6, available 0xc00000000000000000000000001cee8000075bdf 0 inputs)
def r145 : List RE := [(0x80000000000000000000000000140c8000050346,1,0),(0x4000000000000000000000000000aa8000004b0d,0,1),(0xc0000000000000000000000000000000000000db,0,2),(0x1cee8000000000,39,3)]
def d145 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e145 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g145 : GoodC c145 := claim_sound [c130,c62,c99,c144] (gcons g130 (gcons g62 (gcons g99 (gcons g144 gnil)))) r145 d145 e145 c145 (by decide +kernel)
def c146 : Claim := (9, available 0xc0000000000000000007dff0003eff80000fdfdf 0 inputs)
def r146 : List RE := [(0x75830003ac180000ed690,4,0),(0x6003000300180000c0600,9,1),(0x58000002c0000000d010,4,2),(0x5030000281800000c600,9,3),(0x7000000380000000e0080,7,4),(0x8000000000000000000683b000341d80000d0746,1,5),(0x3300000198000000704,2,6),(0x6800000340000000d0040,6,7),(0x5c000002e0000000d818,3,8),(0x4000000000000000000057700002bb800000cf0d,0,9),(0xc00000000000000000018cc000000000000000db,0,10),(0x2e770000000000,40,11),(0xc00000000000000000000000000c6600000000db,0,12),(0x5cee00000000000000000,69,13),(0xc00000000000000000039dd000000000000b9ddf,0,14),(0xc0000000000000000000000000000000000319df,0,15),(0x39dd00000000000000000,68,16),(0xc00000000000000000000000001cee8000075bdf,0,17)]
def R146 : List RR := r146.map (resolve [c134,c126,c133,c57,c135,c131,c59,c128,c136,c63,c137,c138,c139,c140,c142,c143,c141,c145] c146.2)
theorem hR146 : ∀ y ∈ R146, RInv c146.2.toFinset y := res_inv [c134,c126,c133,c57,c135,c131,c59,c128,c136,c63,c137,c138,c139,c140,c142,c143,c141,c145] (gcons g134 (gcons g126 (gcons g133 (gcons g57 (gcons g135 (gcons g131 (gcons g59 (gcons g128 (gcons g136 (gcons g63 (gcons g137 (gcons g138 (gcons g139 (gcons g140 (gcons g142 (gcons g143 (gcons g141 (gcons g145 gnil)))))))))))))))))) r146 c146.2
def k146_4_0 : List Entry := [([23,56,847,96,60],[],[]),([23,56,863,96,60],[],[]),([39,56,847,96,60],[],[]),([39,56,863,96,60],[],[])]
set_option maxRecDepth 100000 in
theorem v146_4_0 : ∀ e ∈ k146_4_0, ¬ Live516.live basicOps goal 4 (wsOf c146.2 e).toFinset := level_sound hR146 4 k146_4_0 [] nil_dead (by decide +kernel)
def D146_4 : List Entry := k146_4_0
theorem w146_4 : ∀ e ∈ D146_4, ¬ Live516.live basicOps goal 4 (wsOf c146.2 e).toFinset := v146_4_0
def k146_5_0 : List Entry := [([23,56,847,96],[],[0]),([23,56,863,96],[],[1]),([39,56,847,96],[],[2]),([39,56,863,96],[],[3])]
set_option maxRecDepth 100000 in
theorem v146_5_0 : ∀ e ∈ k146_5_0, ¬ Live516.live basicOps goal 5 (wsOf c146.2 e).toFinset := level_sound hR146 5 k146_5_0 (D146_4.map (wsOf c146.2)) (map_dead w146_4) (by decide +kernel)
def D146_5 : List Entry := k146_5_0
theorem w146_5 : ∀ e ∈ D146_5, ¬ Live516.live basicOps goal 5 (wsOf c146.2 e).toFinset := v146_5_0
def k146_6_0 : List Entry := [([23,56,839],[5,8,14],[]),([23,56,847],[5,1,14],[0]),([23,56,855],[5,8,17],[]),([23,56,863],[5,1,17],[1]),([23,56,1119],[5,14],[]),([23,60,839],[5,14],[]),([23,60,847],[5,10,14],[]),([23,60,855],[5,17],[]),([23,60,863],[5,12,17],[]),([23,60,1119],[5,14],[]),([23,1111,60],[],[]),([23,1119,52],[],[]),([23,1119,112],[5,10],[0]),([23,1119,116],[5,1],[]),([23,1127,60],[],[]),([23,1135,52],[],[]),([23,1135,112],[5,12],[1]),([23,1135,116],[5,1],[]),([31,1111,56],[],[]),([31,1119,48],[],[]),([31,1119,112],[14,11,5],[]),([31,1119,116],[5],[]),([31,1127,56],[],[]),([31,1135,48],[],[]),([31,1135,112],[17,13,5],[]),([31,1135,116],[5],[]),([39,56,839],[5,9,4,14],[]),([39,56,847],[5,3,14],[2]),([39,56,855],[5,9,4,17],[]),([39,56,863],[5,3,17],[3]),([39,56,1119],[5,14],[]),([39,60,839],[9,14],[]),([39,60,847],[9,10,14],[]),([39,60,855],[9,17],[]),([39,60,863],[9,12,17],[]),([39,60,1119],[9,14],[]),([39,1111,60],[],[]),([39,1119,52],[],[]),([39,1119,112],[9,10],[2]),([39,1119,116],[9,3],[]),([39,1127,60],[],[]),([39,1135,52],[],[]),([39,1135,112],[9,12],[3]),([39,1135,116],[9,3],[]),([47,1111,56],[],[]),([47,1119,48],[],[]),([47,1119,112],[14,11,9],[]),([47,1119,116],[9],[]),([47,1127,56],[],[]),([47,1135,48],[],[])]
set_option maxRecDepth 100000 in
theorem v146_6_0 : ∀ e ∈ k146_6_0, ¬ Live516.live basicOps goal 6 (wsOf c146.2 e).toFinset := level_sound hR146 6 k146_6_0 (D146_5.map (wsOf c146.2)) (map_dead w146_5) (by decide +kernel)
def k146_6_1 : List Entry := [([47,1135,112],[17,13,9],[]),([47,1135,116],[9],[]),([51,300,20],[5,2,9,4,14,11,17,13],[]),([55,296,30],[0,5,2,9,4,14,11,17,13],[]),([303,1119,112],[5],[]),([303,1119,116],[5],[]),([303,1135,112],[5],[]),([303,1135,116],[5],[])]
set_option maxRecDepth 100000 in
theorem v146_6_1 : ∀ e ∈ k146_6_1, ¬ Live516.live basicOps goal 6 (wsOf c146.2 e).toFinset := level_sound hR146 6 k146_6_1 (D146_5.map (wsOf c146.2)) (map_dead w146_5) (by decide +kernel)
def D146_6 : List Entry := k146_6_0 ++ (k146_6_1)
theorem w146_6 : ∀ e ∈ D146_6, ¬ Live516.live basicOps goal 6 (wsOf c146.2 e).toFinset := (app_dead v146_6_0 v146_6_1)
def k146_7_0 : List Entry := [([23,56],[5,8,9,1,14,17],[0,1,2,3,4]),([23,60],[5,0,1,14,17],[5,6,7,8,9]),([23,74],[5,8,0,9,1,4,14,11,17,13],[]),([23,78],[5,8,0,9,4,14,11,17,13,1],[]),([23,94],[5,8,0,9,4,11,17,16,14],[]),([23,110],[5,8,0,9,4,13,14,16,17],[]),([23,1111],[5,8,11,14],[10,0,5]),([23,1119],[5,8,11,14],[11,12,13,1,6]),([23,1127],[5,8,11,17],[14,2,7]),([23,1135],[5,8,13,17],[15,16,17,3,8]),([23,1391],[5,8,15,11,14],[4,9]),([31,66],[0,5,9,4,14,11,17,13],[]),([31,70],[0,5,9,4,14,11,17,13],[]),([31,86],[0,5,9,4,11,17,16],[]),([31,102],[0,5,9,4,13,14,16],[]),([31,1111],[0,11,14,5],[18]),([31,1119],[0,11,14,5],[19,20,21]),([31,1127],[0,11,17,5],[22]),([31,1135],[0,13,17,5],[23,24,25]),([31,1391],[0,15,11,14,5],[]),([39,56],[5,9,0,4,14,17],[26,27,28,29,30]),([39,60],[9,0,2,14,17],[31,32,33,34,35]),([39,74],[9,3,4,5,2,14,11,17,13],[]),([39,78],[9,3,4,5,2,14,11,17,13],[]),([39,94],[9,3,14,5,2,11,17,16],[]),([39,110],[9,3,17,5,2,13,14,16],[]),([39,1111],[9,4,11,14],[36,26,31]),([39,1119],[9,4,11,14],[37,38,39,27,32]),([39,1127],[9,4,11,17],[40,28,33]),([39,1135],[9,4,13,17],[41,42,43,29,34]),([39,1391],[9,4,15,11,14],[30,35]),([47,66],[0,9,5,8,14,11,17,13],[]),([47,70],[0,9,5,8,14,11,17,13],[]),([47,86],[0,9,5,8,11,17,16],[]),([47,102],[0,9,5,8,13,14,16],[]),([47,1111],[0,11,14,9],[44]),([47,1119],[0,11,14,9],[45,46,47]),([47,1127],[0,11,17,9],[48]),([47,1135],[0,13,17,9],[49,50,51]),([47,1391],[0,15,11,14,9],[]),([51,26],[0,10,5,2,9,4,11,17,13],[]),([51,28],[0,5,9,14,17],[]),([51,300],[0,11,5,9,2,17,4],[52]),([55,296],[0,5,2,9,4,14,11,17,13],[52,53]),([59,56],[0,5,9,4,14,10,17,11],[]),([59,60],[0,1,8,9,4,14,10,17,11],[]),([59,72],[0,9,5,8,14,10,17,11],[]),([59,76],[0,3,4,5,2,14,10,17,11],[]),([59,88],[0,14,5,8,9,4,17,10,11],[]),([59,92],[0,10,5,2,9,4,17,11],[])]
set_option maxRecDepth 100000 in
theorem v146_7_0 : ∀ e ∈ k146_7_0, ¬ Live516.live basicOps goal 7 (wsOf c146.2 e).toFinset := level_sound hR146 7 k146_7_0 (D146_6.map (wsOf c146.2)) (map_dead w146_6) (by decide +kernel)
def k146_7_1 : List Entry := [([59,104],[0,17,5,8,9,4,14,10],[]),([59,108],[0,10,17,11,5,2,9,4],[]),([79,96],[0,17,5,14,9,2,4],[]),([79,100],[0,14,5,2,9,4,11],[]),([95,96],[0,14,5,17,9,2,4],[]),([95,100],[0,17,5,2,9,4,11,13],[]),([303,1111],[5,6,8,14],[]),([303,1119],[5,6,8,14],[54,55]),([303,1127],[5,6,8,17],[]),([303,1135],[5,6,8,17],[56,57]),([303,1391],[5,6,8,14],[]),([315,72],[5,9,8,2,14,10,17,11],[]),([315,76],[5,9,8,2,14,7,10,17,11],[]),([571,72],[5,9,4,14,10,17,11],[]),([571,76],[5,9,2,14,7,4,10,17,11],[]),([839,58],[14,10,0,5,2,9,4,17,13],[]),([839,62],[14,0,11,5,2,9,4,17,13],[]),([839,78],[5,8,2,9,7,17,13],[]),([839,94],[9,4,5,7,17,13],[]),([847,50],[14,10,11,5,2,9,4,17,13],[]),([847,54],[0,14,10,11,5,2,9,4,17,13],[]),([847,70],[5,8,2,9,7,17,13],[]),([847,86],[5,9,4,7,17,13],[]),([847,96],[14,17,10,11,5,9],[12,20,38,46,54]),([847,100],[14,17,10,5,9],[13,21,39,47,55]),([855,58],[17,10,0,5,2,9,4,11],[]),([855,62],[17,0,11,5,2,9,4],[]),([855,78],[5,8,2,9,7,14,11],[]),([855,94],[9,4,5,7,14,11],[]),([863,50],[17,12,13,5,2,9,4,14,11],[]),([863,54],[0,17,11,13,5,2,9,4,14],[]),([863,70],[5,8,2,9,7,14,11],[]),([863,86],[5,9,4,7,14,11],[]),([863,96],[14,17,10,12,13,5,9],[16,24,42,50,56]),([863,100],[17,14,11,5,9],[17,25,43,51,57])]
set_option maxRecDepth 100000 in
theorem v146_7_1 : ∀ e ∈ k146_7_1, ¬ Live516.live basicOps goal 7 (wsOf c146.2 e).toFinset := level_sound hR146 7 k146_7_1 (D146_6.map (wsOf c146.2)) (map_dead w146_6) (by decide +kernel)
def D146_7 : List Entry := k146_7_0 ++ (k146_7_1)
theorem w146_7 : ∀ e ∈ D146_7, ¬ Live516.live basicOps goal 7 (wsOf c146.2 e).toFinset := (app_dead v146_7_0 v146_7_1)
def k146_8_0 : List Entry := [([23],[5,0,8,9,4,14,17,7,2],[0,1,2,3,4,5,6,7,8,9,10]),([31],[5,0,9,4,14,17],[11,12,13,14,15,16,17,18,19]),([39],[9,0,5,2,3,4,14,17,7],[20,21,22,23,24,25,26,27,28,29,30]),([47],[9,0,5,8,14,17],[31,32,33,34,35,36,37,38,39]),([51],[11,5,2,9,4,17,13],[40,41,42]),([55],[0,11,5,2,9,4,14,17,13],[40,41,43]),([59],[0,11,5,2,9,4,17,13],[41,44,45,46,47,48,49,50,51,43]),([63],[0,5,2,9,4,14,11,17,13],[41,40,42]),([71],[14,0,5,2,9,4,11,17,16],[]),([79],[14,0,5,2,9,4,11,17,16],[52,53]),([87],[17,0,5,2,9,4,13,14,16],[]),([95],[17,0,5,2,9,4,13,14,16],[54,55]),([303],[5,8,2,6,14,17],[56,57,58,59,60]),([315],[5,8,2,9,7,14,11,17,13],[61,62]),([319],[5,8,2,9,7,14,11,17,13],[]),([335],[5,8,2,9,7,11,17,16],[]),([351],[5,8,2,9,7,13,14,16],[]),([571],[5,9,4,7,14,11,17,13],[63,64]),([575],[9,4,5,7,14,11,17,13],[]),([591],[9,14,4,5,7,11,17,16],[]),([607],[9,17,4,5,7,13,14,16],[]),([839],[14,11,5,9,17,13],[65,66,67,68,6,15,26,35,56]),([847],[14,11,5,9,17,13,16],[69,70,71,72,73,74,7,16,27,36,57]),([855],[17,11,5,9],[75,76,77,78,8,17,28,37,58]),([863],[17,11,12,13,5,9,14,16],[79,80,81,82,83,84,9,18,29,38,59]),([1119],[14,17,15,11,5,9],[10,19,30,39,60])]
set_option maxRecDepth 100000 in
theorem v146_8_0 : ∀ e ∈ k146_8_0, ¬ Live516.live basicOps goal 8 (wsOf c146.2 e).toFinset := level_sound hR146 8 k146_8_0 (D146_7.map (wsOf c146.2)) (map_dead w146_7) (by decide +kernel)
def D146_8 : List Entry := k146_8_0
theorem w146_8 : ∀ e ∈ D146_8, ¬ Live516.live basicOps goal 8 (wsOf c146.2 e).toFinset := v146_8_0
def k146_9_0 : List Entry := [([],[5,9,14,17],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25])]
set_option maxRecDepth 100000 in
theorem v146_9_0 : ∀ e ∈ k146_9_0, ¬ Live516.live basicOps goal 9 (wsOf c146.2 e).toFinset := level_sound hR146 9 k146_9_0 (D146_8.map (wsOf c146.2)) (map_dead w146_8) (by decide +kernel)
def D146_9 : List Entry := k146_9_0
theorem w146_9 : ∀ e ∈ D146_9, ¬ Live516.live basicOps goal 9 (wsOf c146.2 e).toFinset := v146_9_0
theorem g146 : GoodC c146 := claim_sound2 D146_9 c146 w146_9 (by decide +kernel)
def c147 : Claim := (9, available 0xef7bdbdef77bd6dc0007dff0003eff80000fdfdf 0 inputs)
def r147 : List RE := [(0xaa0b5a82d720d218000683b000341d80000d0746,1,0),(0xc0000000000000000007dff0003eff80000fdfdf,0,1)]
def d147 : List Entry := [([4102],[0,1],[]),([],[0,1],[])]
def e147 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g147 : GoodC c147 := claim_sound [c132,c146] (gcons g132 (gcons g146 gnil)) r147 d147 e147 c147 (by decide +kernel)
def c148 : Claim := (4, available 0x15b5000000000006737a00000 21 inputs)
def r148 : List RE := []
def d148 : List Entry := [([],[],[])]
def e148 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g148 : GoodC c148 := claim_sound [] gnil r148 d148 e148 c148 (by decide +kernel)
def c149 : Claim := (6, available 0xce739000027396dc00039dd000000000000b9ddf 0 inputs)
def r149 : List RE := [(0x8a03100002209218000281900000000000090546,1,0),(0xc00000000000000000039dd000000000000b9ddf,0,1)]
def d149 : List Entry := [([4101],[0,1],[]),([],[1],[])]
def e149 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g149 : GoodC c149 := claim_sound [c41,c142] (gcons g41 (gcons g142 gnil)) r149 d149 e149 c149 (by decide +kernel)
def c150 : Claim := (7, available 0xc000000000e73ffe000000000000004e7ff339ff 0 inputs)
def r150 : List RE := [(0xc000000000000fee00000000000000001ef000fb,0,0)]
def d150 : List Entry := [([],[0],[])]
def e150 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g150 : GoodC c150 := claim_sound [c103] (gcons g103 gnil) r150 d150 e150 c150 (by decide +kernel)
def c151 : Claim := (4, available 0x1ce0300000000001605b38100000000000000000 68 inputs)
def r151 : List RE := []
def d151 : List Entry := [([],[],[])]
def e151 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g151 : GoodC c151 := claim_sound [] gnil r151 d151 e151 c151 (by decide +kernel)
def c152 : Claim := (7, available 0x1ef7b000000000017bdbbdd00000000000000000 68 inputs)
def r152 : List RE := [(0x1ce0300000000001605b38100000000000000000,68,0),(0x16b5a0000000000139c9acc00000000000000000,70,1)]
def d152 : List Entry := [([],[0,1],[])]
def e152 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g152 : GoodC c152 := claim_sound [c151,c120] (gcons g151 (gcons g120 gnil)) r152 d152 e152 c152 (by decide +kernel)
def c153 : Claim := (7, available 0xc000000000000000739bbdd00000002d6ddbbdff 0 inputs)
def r153 : List RE := [(0xc00000000000000000039dd000000000000b9ddf,0,0)]
def d153 : List Entry := [([],[0],[])]
def e153 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g153 : GoodC c153 := claim_sound [c142] (gcons g142 gnil) r153 d153 e153 c153 (by decide +kernel)
def c154 : Claim := (4, available 0x1a07300002a0ba3a000000000000000000000000 97 inputs)
def r154 : List RE := []
def d154 : List Entry := [([],[],[])]
def e154 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g154 : GoodC c154 := claim_sound [] gnil r154 d154 e154 c154 (by decide +kernel)
def c155 : Claim := (3, available 0xa03100002209218000000000000000000000000 99 inputs)
def r155 : List RE := []
def d155 : List Entry := [([],[],[])]
def e155 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g155 : GoodC c155 := claim_sound [] gnil r155 d155 e155 c155 (by decide +kernel)
def c156 : Claim := (4, available 0xe73900000000000000000000000000000000000 140 inputs)
def r156 : List RE := [(0x631800000000000000000000000000000000000,143,0)]
def d156 : List Entry := [([],[0],[])]
def e156 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g156 : GoodC c156 := claim_sound [c118] (gcons g118 gnil) r156 d156 e156 c156 (by decide +kernel)
def c157 : Claim := (6, available 0xe739000027396dc000000000000000000000000 98 inputs)
def r157 : List RE := [(0xa03100002209218000000000000000000000000,99,0),(0x52900000119054000000000000000000000000,98,1),(0x6cc000000000000000000000000,98,2),(0xe73900000000000000000000000000000000000,140,3)]
def d157 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e157 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g157 : GoodC c157 := claim_sound [c155,c88,c101,c156] (gcons g155 (gcons g88 (gcons g101 (gcons g156 gnil)))) r157 d157 e157 c157 (by decide +kernel)
def c158 : Claim := (7, available 0x1ef7b00002f7bffe000000000000000000000000 97 inputs)
def r158 : List RE := [(0x1a07300002a0ba3a000000000000000000000000,97,0),(0xe739000027396dc000000000000000000000000,98,1)]
def d158 : List Entry := [([],[0,1],[])]
def e158 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g158 : GoodC c158 := claim_sound [c154,c157] (gcons g154 (gcons g157 gnil)) r158 d158 e158 c158 (by decide +kernel)
def c159 : Claim := (9, available 0xdef7b00002f7bfff7bdbbdd00000006f7ffbbdff 0 inputs)
def r159 : List RE := [(0x2d6a000000000000000006b400ab400,10,0),(0x9a07300002a0ba3b5b5281900000006737a90546,1,1),(0x15b5000000000006737a00000,21,2),(0x40d6b0000015b1760ad83550000000036370ad2d,0,3),(0xd6b5a00000000fef39c9acc0000000001ef000fb,0,4),(0xc000000000000fee00000000000000001ef000fb,0,5),(0xce739000027396dc00039dd000000000000b9ddf,0,6),(0xc00000000000000000039dd000000000000b9ddf,0,7),(0xc000000000e73ffe000000000000004e7ff339ff,0,8),(0x1ef7b000000000017bdbbdd00000000000000000,68,9),(0xc000000000000000739bbdd00000002d6ddbbdff,0,10),(0x1ef7b00002f7bffe000000000000000000000000,97,11)]
def R159 : List RR := r159.map (resolve [c16,c42,c148,c71,c104,c103,c149,c142,c150,c152,c153,c158] c159.2)
theorem hR159 : ∀ y ∈ R159, RInv c159.2.toFinset y := res_inv [c16,c42,c148,c71,c104,c103,c149,c142,c150,c152,c153,c158] (gcons g16 (gcons g42 (gcons g148 (gcons g71 (gcons g104 (gcons g103 (gcons g149 (gcons g142 (gcons g150 (gcons g152 (gcons g153 (gcons g158 gnil)))))))))))) r159 c159.2
def k159_5_0 : List Entry := [([19,300,20,25],[],[]),([19,300,20,29],[],[]),([23,57,568,28],[],[]),([23,61,568,28],[],[]),([23,61,568,44],[],[]),([23,310,56,28],[],[])]
set_option maxRecDepth 100000 in
theorem v159_5_0 : ∀ e ∈ k159_5_0, ¬ Live516.live basicOps goal 5 (wsOf c159.2 e).toFinset := level_sound hR159 5 k159_5_0 [] nil_dead (by decide +kernel)
def D159_5 : List Entry := k159_5_0
theorem w159_5 : ∀ e ∈ D159_5, ¬ Live516.live basicOps goal 5 (wsOf c159.2 e).toFinset := v159_5_0
def k159_6_0 : List Entry := [([19,26,56],[],[]),([19,26,60],[],[]),([19,300,20],[4,6],[0,1]),([23,57,568],[],[2,0]),([23,61,568],[],[3,4]),([23,296,30],[1],[3,0,4]),([23,296,44],[4,6],[2,3]),([23,296,46],[1],[]),([23,310,56],[],[5]),([23,310,316],[3],[5]),([23,318,312],[],[]),([23,574,52],[],[5]),([39,58,60],[],[5]),([39,58,76],[],[]),([39,58,92],[11],[]),([39,58,316],[3],[]),([39,574,52],[3],[]),([47,54,308],[],[]),([47,570,56],[],[]),([303,54,76],[9],[]),([303,54,92],[],[])]
set_option maxRecDepth 100000 in
theorem v159_6_0 : ∀ e ∈ k159_6_0, ¬ Live516.live basicOps goal 6 (wsOf c159.2 e).toFinset := level_sound hR159 6 k159_6_0 (D159_5.map (wsOf c159.2)) (map_dead w159_5) (by decide +kernel)
def D159_6 : List Entry := k159_6_0
theorem w159_6 : ∀ e ∈ D159_6, ¬ Live516.live basicOps goal 6 (wsOf c159.2 e).toFinset := v159_6_0
def k159_7_0 : List Entry := [([19,26],[1],[0,1]),([19,62],[1],[]),([19,300],[1,0,6],[2]),([19,574],[1],[]),([23,54],[3],[1]),([23,56],[3,8,9,10,11],[]),([23,57],[3],[1,3]),([23,60],[8,9,10,11],[]),([23,61],[3,8],[4]),([23,62],[3,8],[]),([23,296],[1,4,6],[2,5,6,7,3,4]),([23,310],[3],[8,9]),([23,318],[0,3],[10]),([23,566],[1,3],[10]),([23,574],[3],[11,9]),([27,60],[1,0,6],[6]),([27,62],[1],[7]),([27,76],[8,9,1,0,6],[]),([27,92],[10,11,1,8,9],[]),([31,54],[3],[]),([31,310],[3],[]),([39,50],[3,10,11],[]),([39,58],[3,9,11,8,10],[12,13,14,8,15]),([39,62],[3,11],[]),([39,574],[],[12,16,15,9]),([47,50],[3,10,11,0],[]),([47,54],[3],[1,17]),([47,570],[],[1,18,17,10]),([295,58],[1],[1,18]),([295,62],[1,8,9],[]),([303,50],[3,9],[]),([303,54],[3,9,11,8,10],[12,19,20,11,16]),([303,62],[3,8,9],[])]
set_option maxRecDepth 100000 in
theorem v159_7_0 : ∀ e ∈ k159_7_0, ¬ Live516.live basicOps goal 7 (wsOf c159.2 e).toFinset := level_sound hR159 7 k159_7_0 (D159_6.map (wsOf c159.2)) (map_dead w159_6) (by decide +kernel)
def D159_7 : List Entry := k159_7_0
theorem w159_7 : ∀ e ∈ D159_7, ¬ Live516.live basicOps goal 7 (wsOf c159.2 e).toFinset := v159_7_0
def k159_8_0 : List Entry := [([19],[1,8,3,4,0,6,2,10,11,9],[0,1,2,3]),([23],[8,1,0,3,4,6,2,10,9,11],[4,5,6,7,8,9,10,11,12,13,14]),([27],[1,8,0,9,11,2,10],[15,16,17,18,10]),([31],[8,1,0,3,6,2,9,10,11],[0,19,2,20]),([39],[3,0,4,6,7,8,9,11],[21,4,22,23,11,20,24]),([47],[3,0,6,7,8,9,11],[25,26,12,27]),([295],[1,3,4,5,6,2,10,11,9],[28,29,13,27]),([303],[3,1,4,5,6,2,10,11,9],[30,31,4,32,3,14,24])]
set_option maxRecDepth 100000 in
theorem v159_8_0 : ∀ e ∈ k159_8_0, ¬ Live516.live basicOps goal 8 (wsOf c159.2 e).toFinset := level_sound hR159 8 k159_8_0 (D159_7.map (wsOf c159.2)) (map_dead w159_7) (by decide +kernel)
def D159_8 : List Entry := k159_8_0
theorem w159_8 : ∀ e ∈ D159_8, ¬ Live516.live basicOps goal 8 (wsOf c159.2 e).toFinset := v159_8_0
def k159_9_0 : List Entry := [([],[3,4,5,6,7,9,11],[0,1,2,3,4,5,6,7])]
set_option maxRecDepth 100000 in
theorem v159_9_0 : ∀ e ∈ k159_9_0, ¬ Live516.live basicOps goal 9 (wsOf c159.2 e).toFinset := level_sound hR159 9 k159_9_0 (D159_8.map (wsOf c159.2)) (map_dead w159_8) (by decide +kernel)
def D159_9 : List Entry := k159_9_0
theorem w159_9 : ∀ e ∈ D159_9, ¬ Live516.live basicOps goal 9 (wsOf c159.2 e).toFinset := v159_9_0
theorem g159 : GoodC c159 := claim_sound2 D159_9 c159 w159_9 (by decide +kernel)
def c160 : Claim := (4, available 0x7380c0000000000000b02d9c08000000000 39 inputs)
def r160 : List RE := []
def d160 : List Entry := [([],[],[])]
def e160 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g160 : GoodC c160 := claim_sound [] gnil r160 d160 e160 c160 (by decide +kernel)
def c161 : Claim := (7, available 0x7bdec0000000000000bdeddee8000000000 39 inputs)
def r161 : List RE := [(0x7380c0000000000000b02d9c08000000000,39,0),(0x5ad6800000000000009ce4d660000000000,41,1)]
def d161 : List Entry := [([],[0,1],[])]
def e161 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g161 : GoodC c161 := claim_sound [c160,c111] (gcons g160 (gcons g111 gnil)) r161 d161 e161 c161 (by decide +kernel)
def c162 : Claim := (4, available 0xada800056b7a00000 21 inputs)
def r162 : List RE := []
def d162 : List Entry := [([],[],[])]
def e162 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g162 : GoodC c162 := claim_sound [] gnil r162 d162 e162 c162 (by decide +kernel)
def c163 : Claim := (6, available 0xc000039ce56b56dc00000000001cee8000075bdf 0 inputs)
def r163 : List RE := [(0x80000280c52052180000000000140c8000050346,1,0),(0xc00000000000000000000000001cee8000075bdf,0,1)]
def d163 : List Entry := [([4101],[0,1],[]),([],[1],[])]
def e163 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g163 : GoodC c163 := claim_sound [c43,c145] (gcons g43 (gcons g145 gnil)) r163 d163 e163 c163 (by decide +kernel)
def c164 : Claim := (7, available 0xc000000000000000000000039cddee9cedd77bff 0 inputs)
def r164 : List RE := [(0xc00000000000000000000000001cee8000075bdf,0,0)]
def d164 : List Entry := [([],[0],[])]
def e164 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g164 : GoodC c164 := claim_sound [c145] (gcons g145 gnil) r164 d164 e164 c164 (by decide +kernel)
def c165 : Claim := (4, available 0x681cda07a3a000000000000000000000000 97 inputs)
def r165 : List RE := []
def d165 : List Entry := [([],[],[])]
def e165 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g165 : GoodC c165 := claim_sound [] gnil r165 d165 e165 c165 (by decide +kernel)
def c166 : Claim := (3, available 0x280c5205218000000000000000000000000 99 inputs)
def r166 : List RE := []
def d166 : List Entry := [([],[],[])]
def e166 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g166 : GoodC c166 := claim_sound [] gnil r166 d166 e166 c166 (by decide +kernel)
def c167 : Claim := (4, available 0x39ce4000000000000000000000000000000 122 inputs)
def r167 : List RE := [(0x18c60000000000000000000000000000000,125,0)]
def d167 : List Entry := [([],[0],[])]
def e167 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g167 : GoodC c167 := claim_sound [c109] (gcons g109 gnil) r167 d167 e167 c167 (by decide +kernel)
def c168 : Claim := (6, available 0x39ce56b56dc000000000000000000000000 98 inputs)
def r168 : List RE := [(0x280c5205218000000000000000000000000,99,0),(0x14a4095054000000000000000000000000,98,1),(0x6cc000000000000000000000000,98,2),(0x39ce4000000000000000000000000000000,122,3)]
def d168 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e168 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g168 : GoodC c168 := claim_sound [c166,c89,c101,c167] (gcons g166 (gcons g89 (gcons g101 (gcons g167 gnil)))) r168 d168 e168 c168 (by decide +kernel)
def c169 : Claim := (7, available 0x7bdedef7ffe000000000000000000000000 97 inputs)
def r169 : List RE := [(0x681cda07a3a000000000000000000000000,97,0),(0x39ce56b56dc000000000000000000000000,98,1)]
def d169 : List Entry := [([],[0,1],[])]
def e169 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g169 : GoodC c169 := claim_sound [c165,c168] (gcons g165 (gcons g168 gnil)) r169 d169 e169 c169 (by decide +kernel)
def c170 : Claim := (9, available 0xc00007bdedef7ffe0000000bdeddeedefff77bff 0 inputs)
def r170 : List RE := [(0x1ce6000000000000000005ac0067200,9,0),(0x80000681cda07a3a0000000ada940cd6b7a50346,1,1),(0xada800056b7a00000,21,2),(0x40000035ac0d71760000000056c1aa82e3706b2d,0,3),(0xc00005ad68000fee00000009ce4d66001ef000fb,0,4),(0xc000000000000fee00000000000000001ef000fb,0,5),(0xc000039ce56b56dc00000000001cee8000075bdf,0,6),(0xc00000000000000000000000001cee8000075bdf,0,7),(0xc000000000e73ffe000000000000004e7ff339ff,0,8),(0x7bdec0000000000000bdeddee8000000000,39,9),(0xc000000000000000000000039cddee9cedd77bff,0,10),(0x7bdedef7ffe000000000000000000000000,97,11)]
def R170 : List RR := r170.map (resolve [c123,c44,c162,c75,c113,c103,c163,c145,c150,c161,c164,c169] c170.2)
theorem hR170 : ∀ y ∈ R170, RInv c170.2.toFinset y := res_inv [c123,c44,c162,c75,c113,c103,c163,c145,c150,c161,c164,c169] (gcons g123 (gcons g44 (gcons g162 (gcons g75 (gcons g113 (gcons g103 (gcons g163 (gcons g145 (gcons g150 (gcons g161 (gcons g164 (gcons g169 gnil)))))))))))) r170 c170.2
def k170_5_0 : List Entry := [([19,300,20,25],[],[]),([19,300,20,29],[],[]),([23,57,568,28],[],[]),([23,61,568,28],[],[]),([23,61,568,44],[],[]),([23,310,56,28],[],[])]
set_option maxRecDepth 100000 in
theorem v170_5_0 : ∀ e ∈ k170_5_0, ¬ Live516.live basicOps goal 5 (wsOf c170.2 e).toFinset := level_sound hR170 5 k170_5_0 [] nil_dead (by decide +kernel)
def D170_5 : List Entry := k170_5_0
theorem w170_5 : ∀ e ∈ D170_5, ¬ Live516.live basicOps goal 5 (wsOf c170.2 e).toFinset := v170_5_0
def k170_6_0 : List Entry := [([19,26,56],[],[]),([19,26,60],[],[]),([19,300,20],[4,6],[0,1]),([23,57,568],[],[2,0]),([23,61,568],[],[3,4]),([23,296,30],[1],[3,0,4]),([23,296,44],[4,6],[2,3]),([23,296,46],[1],[]),([23,310,56],[],[5]),([23,310,316],[3],[5]),([23,318,312],[],[]),([23,574,52],[],[5]),([39,58,60],[],[5]),([39,58,76],[],[]),([39,58,92],[11],[]),([39,58,316],[3],[]),([39,574,52],[3],[]),([47,54,308],[],[]),([47,570,56],[],[]),([303,54,76],[9],[]),([303,54,92],[],[])]
set_option maxRecDepth 100000 in
theorem v170_6_0 : ∀ e ∈ k170_6_0, ¬ Live516.live basicOps goal 6 (wsOf c170.2 e).toFinset := level_sound hR170 6 k170_6_0 (D170_5.map (wsOf c170.2)) (map_dead w170_5) (by decide +kernel)
def D170_6 : List Entry := k170_6_0
theorem w170_6 : ∀ e ∈ D170_6, ¬ Live516.live basicOps goal 6 (wsOf c170.2 e).toFinset := v170_6_0
def k170_7_0 : List Entry := [([19,26],[1],[0,1]),([19,62],[1],[]),([19,300],[1,0,6],[2]),([19,574],[1],[]),([23,54],[3],[1]),([23,56],[3,8,9,10,11],[]),([23,57],[3],[1,3]),([23,60],[8,9,10,11],[]),([23,61],[3,8],[4]),([23,62],[3,8],[]),([23,296],[1,4,6],[2,5,6,7,3,4]),([23,310],[3],[8,9]),([23,318],[0,3],[10]),([23,566],[1,3],[10]),([23,574],[3],[11,9]),([27,60],[1,0,6],[6]),([27,62],[1],[7]),([27,76],[8,9,1,0,6],[]),([27,92],[10,11,1,8,9],[]),([31,54],[3],[]),([31,310],[3],[]),([39,50],[3,10,11],[]),([39,58],[3,9,11,8,10],[12,13,14,8,15]),([39,62],[3,11],[]),([39,574],[],[12,16,15,9]),([47,50],[3,10,11,0],[]),([47,54],[3],[1,17]),([47,570],[],[1,18,17,10]),([295,58],[1],[1,18]),([295,62],[1,8,9],[]),([303,50],[3,9],[]),([303,54],[3,9,11,8,10],[12,19,20,11,16]),([303,62],[3,8,9],[])]
set_option maxRecDepth 100000 in
theorem v170_7_0 : ∀ e ∈ k170_7_0, ¬ Live516.live basicOps goal 7 (wsOf c170.2 e).toFinset := level_sound hR170 7 k170_7_0 (D170_6.map (wsOf c170.2)) (map_dead w170_6) (by decide +kernel)
def D170_7 : List Entry := k170_7_0
theorem w170_7 : ∀ e ∈ D170_7, ¬ Live516.live basicOps goal 7 (wsOf c170.2 e).toFinset := v170_7_0
def k170_8_0 : List Entry := [([19],[1,8,3,4,0,6,2,10,11,9],[0,1,2,3]),([23],[8,1,0,3,4,6,2,10,9,11],[4,5,6,7,8,9,10,11,12,13,14]),([27],[1,8,0,9,11,2,10],[15,16,17,18,10]),([31],[8,1,0,3,6,2,9,10,11],[0,19,2,20]),([39],[3,0,4,6,7,8,9,11],[21,4,22,23,11,20,24]),([47],[3,0,6,7,8,9,11],[25,26,12,27]),([295],[1,3,4,5,6,2,10,11,9],[28,29,13,27]),([303],[3,1,4,5,6,2,10,11,9],[30,31,4,32,3,14,24])]
set_option maxRecDepth 100000 in
theorem v170_8_0 : ∀ e ∈ k170_8_0, ¬ Live516.live basicOps goal 8 (wsOf c170.2 e).toFinset := level_sound hR170 8 k170_8_0 (D170_7.map (wsOf c170.2)) (map_dead w170_7) (by decide +kernel)
def D170_8 : List Entry := k170_8_0
theorem w170_8 : ∀ e ∈ D170_8, ¬ Live516.live basicOps goal 8 (wsOf c170.2 e).toFinset := v170_8_0
def k170_9_0 : List Entry := [([],[3,4,5,6,7,9,11],[0,1,2,3,4,5,6,7])]
set_option maxRecDepth 100000 in
theorem v170_9_0 : ∀ e ∈ k170_9_0, ¬ Live516.live basicOps goal 9 (wsOf c170.2 e).toFinset := level_sound hR170 9 k170_9_0 (D170_8.map (wsOf c170.2)) (map_dead w170_8) (by decide +kernel)
def D170_9 : List Entry := k170_9_0
theorem w170_9 : ∀ e ∈ D170_9, ¬ Live516.live basicOps goal 9 (wsOf c170.2 e).toFinset := v170_9_0
theorem g170 : GoodC c170 := claim_sound2 D170_9 c170 w170_9 (by decide +kernel)
def c171 : Claim := (10, available 0xc000000000000000f7bffff7bdffffbdeddfffff 0 inputs)
def r171 : List RE := [(0xc0000000000000000007dff0003eff80000fdfdf,0,0)]
def d171 : List Entry := [([],[0],[])]
def e171 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g171 : GoodC c171 := claim_sound [c146] (gcons g146 gnil) r171 d171 e171 c171 (by decide +kernel)
def c172 : Claim := (4, available 0x38007e001f80e802000000000000000000000000 97 inputs)
def r172 : List RE := [(0x70001c00e002000000000000000000000000,97,0)]
def d172 : List Entry := [([4096],[0],[]),([],[],[])]
def e172 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g172 : GoodC c172 := claim_sound [c81] (gcons g81 gnil) r172 d172 e172 c172 (by decide +kernel)
def c173 : Claim := (3, available 0x28005a001700c000000000000000000000000000 110 inputs)
def r173 : List RE := []
def d173 : List Entry := [([4096],[],[]),([],[],[])]
def e173 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g173 : GoodC c173 := claim_sound [] gnil r173 d173 e173 c173 (by decide +kernel)
def c174 : Claim := (3, available 0x28000a0003000000000000000000000000000000 120 inputs)
def r174 : List RE := []
def d174 : List Entry := [([],[],[])]
def e174 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g174 : GoodC c174 := claim_sound [] gnil r174 d174 e174 c174 (by decide +kernel)
def c175 : Claim := (4, available 0x2a000a8003200200000000000000000000000000 105 inputs)
def r175 : List RE := [(0x28000a0003000000000000000000000000000000,120,0)]
def d175 : List Entry := [([],[0],[])]
def e175 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g175 : GoodC c175 := claim_sound [c174] (gcons g174 gnil) r175 d175 e175 c175 (by decide +kernel)
def c176 : Claim := (6, available 0x2a0b5a82d720d218000000000000000000000000 99 inputs)
def r176 : List RE := [(0x28005a001700c000000000000000000000000000,110,0),(0x50001400c000000000000000000000000000,110,1),(0xa50029400d010000000000000000000000000,100,2),(0x2a000a8003200200000000000000000000000000,105,3),(0xa03100002209218000000000000000000000000,99,4),(0x280c5205218000000000000000000000000,99,5)]
def d176 : List Entry := [([],[2,0,1,3,4,5],[0,1,2,3,4])]
def e176 : List (List Entry) := [[([567],[2,3,4],[]),([575],[2,1,4],[0]),([583],[2,3,5],[]),([591],[2,1,5],[1]),([847],[2,4],[])],[([575,80],[],[]),([591,80],[],[])]]
set_option maxRecDepth 100000 in
theorem g176 : GoodC c176 := claim_sound [c173,c80,c85,c175,c155,c166] (gcons g173 (gcons g80 (gcons g85 (gcons g175 (gcons g155 (gcons g166 gnil)))))) r176 d176 e176 c176 (by decide +kernel)
def c177 : Claim := (7, available 0x3a0f7e83dfa0fa3a000000000000000000000000 97 inputs)
def r177 : List RE := [(0x38007e001f80e802000000000000000000000000,97,0),(0xe70039c00f032000000000000000000000000,97,1),(0x2a0b5a82d720d218000000000000000000000000,99,2)]
def d177 : List Entry := [([],[0,1,2],[])]
def e177 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g177 : GoodC c177 := claim_sound [c172,c83,c176] (gcons g172 (gcons g83 (gcons g176 gnil))) r177 d177 e177 c177 (by decide +kernel)
def c178 : Claim := (4, available 0x1600058001a0080000000000000000000000000 103 inputs)
def r178 : List RE := [(0x140005000180000000000000000000000000000,115,0)]
def d178 : List Entry := [([],[0],[])]
def e178 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g178 : GoodC c178 := claim_sound [c86] (gcons g86 gnil) r178 d178 e178 c178 (by decide +kernel)
def c179 : Claim := (5, available 0x2d605b58175ac480000000000000000000000000 103 inputs)
def r179 : List RE := [(0x1600058001a0080000000000000000000000000,103,0)]
def d179 : List Entry := [([],[0],[])]
def e179 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g179 : GoodC c179 := claim_sound [c178] (gcons g178 gnil) r179 d179 e179 c179 (by decide +kernel)
def c180 : Claim := (4, available 0x2c000b0003400400000000000000000000000000 106 inputs)
def r180 : List RE := [(0x28000a0003000000000000000000000000000000,120,0)]
def d180 : List Entry := [([],[0],[])]
def e180 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g180 : GoodC c180 := claim_sound [c174] (gcons g174 gnil) r180 d180 e180 c180 (by decide +kernel)
def c181 : Claim := (5, available 0x170005c001b00c0000000000000000000000000 102 inputs)
def r181 : List RE := [(0x1600058001a0080000000000000000000000000,103,0)]
def d181 : List Entry := [([],[0],[])]
def e181 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g181 : GoodC c181 := claim_sound [c178] (gcons g178 gnil) r181 d181 e181 c181 (by decide +kernel)
def c182 : Claim := (3, available 0x6318000000006cc000000000000000000000000 98 inputs)
def r182 : List RE := []
def d182 : List Entry := [([4099],[],[]),([],[],[])]
def e182 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g182 : GoodC c182 := claim_sound [] gnil r182 d182 e182 c182 (by decide +kernel)
def c183 : Claim := (4, available 0x9ce70000000000000000000000000000000 124 inputs)
def r183 : List RE := [(0x18c60000000000000000000000000000000,125,0)]
def d183 : List Entry := [([],[0],[])]
def e183 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g183 : GoodC c183 := claim_sound [c109] (gcons g109 gnil) r183 d183 e183 c183 (by decide +kernel)
def c184 : Claim := (3, available 0x18c600006cc000000000000000000000000 98 inputs)
def r184 : List RE := []
def d184 : List Entry := [([4099],[],[]),([],[],[])]
def e184 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g184 : GoodC c184 := claim_sound [] gnil r184 d184 e184 c184 (by decide +kernel)
def c185 : Claim := (4, available 0x2739c00000000000000000000000000000000000 142 inputs)
def r185 : List RE := [(0x631800000000000000000000000000000000000,143,0)]
def d185 : List Entry := [([],[0],[])]
def e185 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g185 : GoodC c185 := claim_sound [c118] (gcons g118 gnil) r185 d185 e185 c185 (by decide +kernel)
def c186 : Claim := (4, available 0x6316dc000000000000000000000000 98 inputs)
def r186 : List RE := [(0x6cc000000000000000000000000,98,0)]
def d186 : List Entry := [([],[0],[])]
def e186 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g186 : GoodC c186 := claim_sound [c101] (gcons g101 gnil) r186 d186 e186 c186 (by decide +kernel)
def c187 : Claim := (9, available 0x2f7bdbdef77bd6dc000000000000000000000000 98 inputs)
def r187 : List RE := [(0x2d605b58175ac480000000000000000000000000,103,0),(0x28005a001700c000000000000000000000000000,110,1),(0x1600058001a0080000000000000000000000000,103,2),(0x14050501418c000000000000000000000000000,110,3),(0x2c000b0003400400000000000000000000000000,106,4),(0x2a0b5a82d720d218000000000000000000000000,99,5),(0xa50029400d010000000000000000000000000,100,6),(0x2a000a8003200200000000000000000000000000,105,7),(0x170005c001b00c0000000000000000000000000,102,8),(0x15ad056b419d054000000000000000000000000,98,9),(0x6318000000006cc000000000000000000000000,98,10),(0x9ce70000000000000000000000000000000,124,11),(0x18c600006cc000000000000000000000000,98,12),(0x2739c00000000000000000000000000000000000,142,13),(0xe739000027396dc000000000000000000000000,98,14),(0x6316dc000000000000000000000000,98,15),(0xe73900000000000000000000000000000000000,140,16),(0x39ce56b56dc000000000000000000000000,98,17)]
def R187 : List RR := r187.map (resolve [c179,c173,c178,c84,c180,c176,c85,c175,c181,c90,c182,c183,c184,c185,c157,c186,c156,c168] c187.2)
theorem hR187 : ∀ y ∈ R187, RInv c187.2.toFinset y := res_inv [c179,c173,c178,c84,c180,c176,c85,c175,c181,c90,c182,c183,c184,c185,c157,c186,c156,c168] (gcons g179 (gcons g173 (gcons g178 (gcons g84 (gcons g180 (gcons g176 (gcons g85 (gcons g175 (gcons g181 (gcons g90 (gcons g182 (gcons g183 (gcons g184 (gcons g185 (gcons g157 (gcons g186 (gcons g156 (gcons g168 gnil)))))))))))))))))) r187 c187.2
def k187_4_0 : List Entry := [([23,56,847,96,60],[],[]),([23,56,863,96,60],[],[]),([39,56,847,96,60],[],[]),([39,56,863,96,60],[],[])]
set_option maxRecDepth 100000 in
theorem v187_4_0 : ∀ e ∈ k187_4_0, ¬ Live516.live basicOps goal 4 (wsOf c187.2 e).toFinset := level_sound hR187 4 k187_4_0 [] nil_dead (by decide +kernel)
def D187_4 : List Entry := k187_4_0
theorem w187_4 : ∀ e ∈ D187_4, ¬ Live516.live basicOps goal 4 (wsOf c187.2 e).toFinset := v187_4_0
def k187_5_0 : List Entry := [([23,56,847,96],[],[0]),([23,56,863,96],[],[1]),([39,56,847,96],[],[2]),([39,56,863,96],[],[3])]
set_option maxRecDepth 100000 in
theorem v187_5_0 : ∀ e ∈ k187_5_0, ¬ Live516.live basicOps goal 5 (wsOf c187.2 e).toFinset := level_sound hR187 5 k187_5_0 (D187_4.map (wsOf c187.2)) (map_dead w187_4) (by decide +kernel)
def D187_5 : List Entry := k187_5_0
theorem w187_5 : ∀ e ∈ D187_5, ¬ Live516.live basicOps goal 5 (wsOf c187.2 e).toFinset := v187_5_0
def k187_6_0 : List Entry := [([23,56,839],[5,8,14],[]),([23,56,847],[5,1,14],[0]),([23,56,855],[5,8,17],[]),([23,56,863],[5,1,17],[1]),([23,56,1119],[5,14],[]),([23,60,839],[5,14],[]),([23,60,847],[5,10,14],[]),([23,60,855],[5,17],[]),([23,60,863],[5,12,17],[]),([23,60,1119],[5,14],[]),([23,1111,60],[],[]),([23,1119,52],[],[]),([23,1119,112],[5,10],[0]),([23,1119,116],[5,1],[]),([23,1127,60],[],[]),([23,1135,52],[],[]),([23,1135,112],[5,12],[1]),([23,1135,116],[5,1],[]),([31,1111,56],[],[]),([31,1119,48],[],[]),([31,1119,112],[14,11,5],[]),([31,1119,116],[5],[]),([31,1127,56],[],[]),([31,1135,48],[],[]),([31,1135,112],[17,13,5],[]),([31,1135,116],[5],[]),([39,56,839],[5,9,4,14],[]),([39,56,847],[5,3,14],[2]),([39,56,855],[5,9,4,17],[]),([39,56,863],[5,3,17],[3]),([39,56,1119],[5,14],[]),([39,60,839],[9,14],[]),([39,60,847],[9,10,14],[]),([39,60,855],[9,17],[]),([39,60,863],[9,12,17],[]),([39,60,1119],[9,14],[]),([39,1111,60],[],[]),([39,1119,52],[],[]),([39,1119,112],[9,10],[2]),([39,1119,116],[9,3],[]),([39,1127,60],[],[]),([39,1135,52],[],[]),([39,1135,112],[9,12],[3]),([39,1135,116],[9,3],[]),([47,1111,56],[],[]),([47,1119,48],[],[]),([47,1119,112],[14,11,9],[]),([47,1119,116],[9],[]),([47,1127,56],[],[]),([47,1135,48],[],[])]
set_option maxRecDepth 100000 in
theorem v187_6_0 : ∀ e ∈ k187_6_0, ¬ Live516.live basicOps goal 6 (wsOf c187.2 e).toFinset := level_sound hR187 6 k187_6_0 (D187_5.map (wsOf c187.2)) (map_dead w187_5) (by decide +kernel)
def k187_6_1 : List Entry := [([47,1135,112],[17,13,9],[]),([47,1135,116],[9],[]),([51,300,20],[5,2,9,4,14,11,17,13],[]),([55,296,30],[0,5,2,9,4,14,11,17,13],[]),([303,1119,112],[5],[]),([303,1119,116],[5],[]),([303,1135,112],[5],[]),([303,1135,116],[5],[])]
set_option maxRecDepth 100000 in
theorem v187_6_1 : ∀ e ∈ k187_6_1, ¬ Live516.live basicOps goal 6 (wsOf c187.2 e).toFinset := level_sound hR187 6 k187_6_1 (D187_5.map (wsOf c187.2)) (map_dead w187_5) (by decide +kernel)
def D187_6 : List Entry := k187_6_0 ++ (k187_6_1)
theorem w187_6 : ∀ e ∈ D187_6, ¬ Live516.live basicOps goal 6 (wsOf c187.2 e).toFinset := (app_dead v187_6_0 v187_6_1)
def k187_7_0 : List Entry := [([23,56],[5,8,9,1,14,17],[0,1,2,3,4]),([23,60],[5,0,1,14,17],[5,6,7,8,9]),([23,74],[5,8,0,9,1,4,14,11,17,13],[]),([23,78],[5,8,0,9,4,14,11,17,13,1],[]),([23,94],[5,8,0,9,4,11,17,16,14],[]),([23,110],[5,8,0,9,4,13,14,16,17],[]),([23,1111],[5,8,11,14],[10,0,5]),([23,1119],[5,8,11,14],[11,12,13,1,6]),([23,1127],[5,8,11,17],[14,2,7]),([23,1135],[5,8,13,17],[15,16,17,3,8]),([23,1391],[5,8,15,11,14],[4,9]),([31,66],[0,5,9,4,14,11,17,13],[]),([31,70],[0,5,9,4,14,11,17,13],[]),([31,86],[0,5,9,4,11,17,16],[]),([31,102],[0,5,9,4,13,14,16],[]),([31,1111],[0,11,14,5],[18]),([31,1119],[0,11,14,5],[19,20,21]),([31,1127],[0,11,17,5],[22]),([31,1135],[0,13,17,5],[23,24,25]),([31,1391],[0,15,11,14,5],[]),([39,56],[5,9,0,4,14,17],[26,27,28,29,30]),([39,60],[9,0,2,14,17],[31,32,33,34,35]),([39,74],[9,3,4,5,2,14,11,17,13],[]),([39,78],[9,3,4,5,2,14,11,17,13],[]),([39,94],[9,3,14,5,2,11,17,16],[]),([39,110],[9,3,17,5,2,13,14,16],[]),([39,1111],[9,4,11,14],[36,26,31]),([39,1119],[9,4,11,14],[37,38,39,27,32]),([39,1127],[9,4,11,17],[40,28,33]),([39,1135],[9,4,13,17],[41,42,43,29,34]),([39,1391],[9,4,15,11,14],[30,35]),([47,66],[0,9,5,8,14,11,17,13],[]),([47,70],[0,9,5,8,14,11,17,13],[]),([47,86],[0,9,5,8,11,17,16],[]),([47,102],[0,9,5,8,13,14,16],[]),([47,1111],[0,11,14,9],[44]),([47,1119],[0,11,14,9],[45,46,47]),([47,1127],[0,11,17,9],[48]),([47,1135],[0,13,17,9],[49,50,51]),([47,1391],[0,15,11,14,9],[]),([51,26],[0,10,5,2,9,4,11,17,13],[]),([51,28],[0,5,9,14,17],[]),([51,300],[0,11,5,9,2,17,4],[52]),([55,296],[0,5,2,9,4,14,11,17,13],[52,53]),([59,56],[0,5,9,4,14,10,17,11],[]),([59,60],[0,1,8,9,4,14,10,17,11],[]),([59,72],[0,9,5,8,14,10,17,11],[]),([59,76],[0,3,4,5,2,14,10,17,11],[]),([59,88],[0,14,5,8,9,4,17,10,11],[]),([59,92],[0,10,5,2,9,4,17,11],[])]
set_option maxRecDepth 100000 in
theorem v187_7_0 : ∀ e ∈ k187_7_0, ¬ Live516.live basicOps goal 7 (wsOf c187.2 e).toFinset := level_sound hR187 7 k187_7_0 (D187_6.map (wsOf c187.2)) (map_dead w187_6) (by decide +kernel)
def k187_7_1 : List Entry := [([59,104],[0,17,5,8,9,4,14,10],[]),([59,108],[0,10,17,11,5,2,9,4],[]),([79,96],[0,17,5,14,9,2,4],[]),([79,100],[0,14,5,2,9,4,11],[]),([95,96],[0,14,5,17,9,2,4],[]),([95,100],[0,17,5,2,9,4,11,13],[]),([303,1111],[5,6,8,14],[]),([303,1119],[5,6,8,14],[54,55]),([303,1127],[5,6,8,17],[]),([303,1135],[5,6,8,17],[56,57]),([303,1391],[5,6,8,14],[]),([315,72],[5,9,8,2,14,10,17,11],[]),([315,76],[5,9,8,2,14,7,10,17,11],[]),([571,72],[5,9,4,14,10,17,11],[]),([571,76],[5,9,2,14,7,4,10,17,11],[]),([839,58],[14,10,0,5,2,9,4,17,13],[]),([839,62],[14,0,11,5,2,9,4,17,13],[]),([839,78],[5,8,2,9,7,17,13],[]),([839,94],[9,4,5,7,17,13],[]),([847,50],[14,10,11,5,2,9,4,17,13],[]),([847,54],[0,14,10,11,5,2,9,4,17,13],[]),([847,70],[5,8,2,9,7,17,13],[]),([847,86],[5,9,4,7,17,13],[]),([847,96],[14,17,10,11,5,9],[12,20,38,46,54]),([847,100],[14,17,10,5,9],[13,21,39,47,55]),([855,58],[17,10,0,5,2,9,4,11],[]),([855,62],[17,0,11,5,2,9,4],[]),([855,78],[5,8,2,9,7,14,11],[]),([855,94],[9,4,5,7,14,11],[]),([863,50],[17,12,13,5,2,9,4,14,11],[]),([863,54],[0,17,11,13,5,2,9,4,14],[]),([863,70],[5,8,2,9,7,14,11],[]),([863,86],[5,9,4,7,14,11],[]),([863,96],[14,17,10,12,13,5,9],[16,24,42,50,56]),([863,100],[17,14,11,5,9],[17,25,43,51,57])]
set_option maxRecDepth 100000 in
theorem v187_7_1 : ∀ e ∈ k187_7_1, ¬ Live516.live basicOps goal 7 (wsOf c187.2 e).toFinset := level_sound hR187 7 k187_7_1 (D187_6.map (wsOf c187.2)) (map_dead w187_6) (by decide +kernel)
def D187_7 : List Entry := k187_7_0 ++ (k187_7_1)
theorem w187_7 : ∀ e ∈ D187_7, ¬ Live516.live basicOps goal 7 (wsOf c187.2 e).toFinset := (app_dead v187_7_0 v187_7_1)
def k187_8_0 : List Entry := [([23],[5,0,8,9,4,14,17,7,2],[0,1,2,3,4,5,6,7,8,9,10]),([31],[5,0,9,4,14,17],[11,12,13,14,15,16,17,18,19]),([39],[9,0,5,2,3,4,14,17,7],[20,21,22,23,24,25,26,27,28,29,30]),([47],[9,0,5,8,14,17],[31,32,33,34,35,36,37,38,39]),([51],[11,5,2,9,4,17,13],[40,41,42]),([55],[0,11,5,2,9,4,14,17,13],[40,41,43]),([59],[0,11,5,2,9,4,17,13],[41,44,45,46,47,48,49,50,51,43]),([63],[0,5,2,9,4,14,11,17,13],[41,40,42]),([71],[14,0,5,2,9,4,11,17,16],[]),([79],[14,0,5,2,9,4,11,17,16],[52,53]),([87],[17,0,5,2,9,4,13,14,16],[]),([95],[17,0,5,2,9,4,13,14,16],[54,55]),([303],[5,8,2,6,14,17],[56,57,58,59,60]),([315],[5,8,2,9,7,14,11,17,13],[61,62]),([319],[5,8,2,9,7,14,11,17,13],[]),([335],[5,8,2,9,7,11,17,16],[]),([351],[5,8,2,9,7,13,14,16],[]),([571],[5,9,4,7,14,11,17,13],[63,64]),([575],[9,4,5,7,14,11,17,13],[]),([591],[9,14,4,5,7,11,17,16],[]),([607],[9,17,4,5,7,13,14,16],[]),([839],[14,11,5,9,17,13],[65,66,67,68,6,15,26,35,56]),([847],[14,11,5,9,17,13,16],[69,70,71,72,73,74,7,16,27,36,57]),([855],[17,11,5,9],[75,76,77,78,8,17,28,37,58]),([863],[17,11,12,13,5,9,14,16],[79,80,81,82,83,84,9,18,29,38,59]),([1119],[14,17,15,11,5,9],[10,19,30,39,60])]
set_option maxRecDepth 100000 in
theorem v187_8_0 : ∀ e ∈ k187_8_0, ¬ Live516.live basicOps goal 8 (wsOf c187.2 e).toFinset := level_sound hR187 8 k187_8_0 (D187_7.map (wsOf c187.2)) (map_dead w187_7) (by decide +kernel)
def D187_8 : List Entry := k187_8_0
theorem w187_8 : ∀ e ∈ D187_8, ¬ Live516.live basicOps goal 8 (wsOf c187.2 e).toFinset := v187_8_0
def k187_9_0 : List Entry := [([],[5,9,14,17],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25])]
set_option maxRecDepth 100000 in
theorem v187_9_0 : ∀ e ∈ k187_9_0, ¬ Live516.live basicOps goal 9 (wsOf c187.2 e).toFinset := level_sound hR187 9 k187_9_0 (D187_8.map (wsOf c187.2)) (map_dead w187_8) (by decide +kernel)
def D187_9 : List Entry := k187_9_0
theorem w187_9 : ∀ e ∈ D187_9, ¬ Live516.live basicOps goal 9 (wsOf c187.2 e).toFinset := v187_9_0
theorem g187 : GoodC c187 := claim_sound2 D187_9 c187 w187_9 (by decide +kernel)
def c188 : Claim := (10, available 0x3ffffffffffffffe000000000000000000000000 97 inputs)
def r188 : List RE := [(0x3a0f7e83dfa0fa3a000000000000000000000000,97,0),(0x2f7bdbdef77bd6dc000000000000000000000000,98,1)]
def d188 : List Entry := [([],[0,1],[])]
def e188 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g188 : GoodC c188 := claim_sound [c177,c187] (gcons g177 (gcons g187 gnil)) r188 d188 e188 c188 (by decide +kernel)
def c189 : Claim := (12, inputs)
def r189 : List RE := [(0x3de07f781fdeed83e07f783f03fbc1fbd83ef6b0,4,0),(0x38007e001f80e803c076003e03b001f3902c0600,9,1),(0x1e00078001e0180000078000003c0000000f030,4,2),(0x1c070701c1ce1020078703003c38183c030e620,5,3),(0x3c000f0003c00c01e007000f00380078180e0080,7,4),(0x35a06d6818000d83a06d682d036b4100183000b0,4,5),(0x3dee000000000000000007bc00ef600,9,6),(0xba0f7e83dfa0fa3bdf7683befbb41df7b7ad0746,1,7),(0xe70039c00f0320e70033073801983a3200704,2,8),(0x3a000e8003a00a01d006800e80340074140d0040,6,9),(0x1df70000efb800077b7a00000,21,10),(0x9a07300002a0ba3b5b5281900000006737a90546,1,11),(0x80000681cda07a3a0000000ada940cd6b7a50346,1,12),(0x1d00074001d0140000074000003a0000000e828,3,13),(0x7c000003e0000000f838,3,14),(0x41def077bc1df1760ef8777077c3bb83e370ef2d,0,15),(0x419ce067380001660ce866606743330002700029,0,16),(0x40d6b0000015b1760ad83550000000036370ad2d,0,17),(0x77bc0000000000000077c3bb8000000000,39,18),(0x40000035ac0d71760000000056c1aa82e3706b2d,0,19),(0x1def000000000000ef877700000000000000000,68,20),(0x1f000000f8000007c1c000000,26,21),(0xd6b5a00000000fef39c9acc0000000001ef000fb,0,22),(0xdef780000000000000def6f770000000000,40,23),(0xc00005ad68000fee00000009ce4d66001ef000fb,0,24),(0x37bde00000000001bdedeee00000000000000000,69,25),(0x2f7b000000000000000006f600bbd00,8,26),(0x1ef7000000000000000005ee0077b00,8,27),(0xef7bdbdef77bd6dc0007dff0003eff80000fdfdf,0,28),(0xc0000000000000000007dff0003eff80000fdfdf,0,29),(0xdef7b00002f7bfff7bdbbdd00000006f7ffbbdff,0,30),(0xc000000000e73ffe000000000000004e7ff339ff,0,31),(0x1ef7b000000000017bdbbdd00000000000000000,68,32),(0x7bdec0000000000000bdeddee8000000000,39,33),(0xc00007bdedef7ffe0000000bdeddeedefff77bff,0,34),(0xc000000000000000f7bffff7bdffffbdeddfffff,0,35),(0x3ffffffffffffffe000000000000000000000000,97,36)]
def R189 : List RR := r189.map (resolve [c29,c4,c7,c8,c13,c15,c17,c39,c30,c40,c38,c42,c44,c45,c49,c92,c52,c71,c93,c75,c94,c96,c104,c112,c113,c121,c122,c124,c147,c146,c159,c150,c152,c161,c170,c171,c188] c189.2)
theorem hR189 : ∀ y ∈ R189, RInv c189.2.toFinset y := res_inv [c29,c4,c7,c8,c13,c15,c17,c39,c30,c40,c38,c42,c44,c45,c49,c92,c52,c71,c93,c75,c94,c96,c104,c112,c113,c121,c122,c124,c147,c146,c159,c150,c152,c161,c170,c171,c188] (gcons g29 (gcons g4 (gcons g7 (gcons g8 (gcons g13 (gcons g15 (gcons g17 (gcons g39 (gcons g30 (gcons g40 (gcons g38 (gcons g42 (gcons g44 (gcons g45 (gcons g49 (gcons g92 (gcons g52 (gcons g71 (gcons g93 (gcons g75 (gcons g94 (gcons g96 (gcons g104 (gcons g112 (gcons g113 (gcons g121 (gcons g122 (gcons g124 (gcons g147 (gcons g146 (gcons g159 (gcons g150 (gcons g152 (gcons g161 (gcons g170 (gcons g171 (gcons g188 gnil))))))))))))))))))))))))))))))))))))) r189 c189.2
def k189_5_0 : List Entry := [([19,300,20,25,591,96,60],[],[]),([19,300,20,25,607,96,60],[],[]),([23,56,863,112,60,29,312],[],[]),([23,56,863,112,60,57,332],[],[]),([23,56,863,112,60,77,348],[],[]),([23,56,879,112,60,29,312],[],[]),([23,56,879,112,60,57,332],[],[]),([23,56,879,112,60,77,348],[],[]),([23,57,568,28,591,96,60],[],[]),([23,57,568,28,607,96,60],[],[])]
set_option maxRecDepth 100000 in
theorem v189_5_0 : ∀ e ∈ k189_5_0, ¬ Live516.live basicOps goal 5 (wsOf c189.2 e).toFinset := level_sound hR189 5 k189_5_0 [] nil_dead (by decide +kernel)
def D189_5 : List Entry := k189_5_0
theorem w189_5 : ∀ e ∈ D189_5, ¬ Live516.live basicOps goal 5 (wsOf c189.2 e).toFinset := v189_5_0
def k189_6_0 : List Entry := [([19,26,56,863,112,60],[],[]),([19,26,56,879,112,60],[],[]),([19,300,20,25,591,96],[],[0]),([19,300,20,25,591,100],[],[]),([19,300,20,25,607,96],[],[1]),([19,300,20,25,607,100],[],[]),([19,300,20,29,591,96],[],[]),([19,300,20,29,591,100],[],[]),([19,300,20,29,607,96],[],[]),([19,300,20,29,607,100],[],[]),([19,300,20,35,300,20],[28],[]),([19,300,20,583,58,72],[],[]),([19,300,20,583,58,76],[],[]),([19,300,20,591,50,72],[],[]),([19,300,20,591,50,76],[],[]),([19,300,20,599,58,72],[],[]),([19,300,20,599,58,76],[],[]),([19,300,20,607,50,72],[],[]),([19,300,20,607,50,76],[],[]),([23,56,863,112,60,29],[23],[2]),([23,56,863,112,60,57],[],[2,3]),([23,56,863,112,60,61],[],[]),([23,56,863,112,60,73],[],[]),([23,56,863,112,60,77],[],[3,4]),([23,56,863,112,60,93],[36],[4]),([23,56,879,112,60,29],[25],[5]),([23,56,879,112,60,57],[],[5,6]),([23,56,879,112,60,61],[],[]),([23,56,879,112,60,73],[],[]),([23,56,879,112,60,77],[],[6,7]),([23,56,879,112,60,93],[36],[7]),([23,57,568,28,591,96],[],[8]),([23,57,568,28,591,100],[],[]),([23,57,568,28,607,96],[],[9]),([23,57,568,28,607,100],[],[]),([23,57,568,863,112,60],[],[8]),([23,57,568,863,112,76],[],[8,0]),([23,57,568,879,112,60],[],[9]),([23,57,568,879,112,76],[],[9,1]),([23,61,568,28,591,96],[],[]),([23,61,568,28,591,100],[],[]),([23,61,568,28,607,96],[],[]),([23,61,568,28,607,100],[],[]),([23,61,568,44,591,96],[],[]),([23,61,568,44,591,100],[],[]),([23,61,568,44,607,96],[],[]),([23,61,568,44,607,100],[],[]),([23,61,568,863,112,60],[],[]),([23,61,568,879,112,60],[],[]),([23,296,863,112,60,61],[],[])]
set_option maxRecDepth 100000 in
theorem v189_6_0 : ∀ e ∈ k189_6_0, ¬ Live516.live basicOps goal 6 (wsOf c189.2 e).toFinset := level_sound hR189 6 k189_6_0 (D189_5.map (wsOf c189.2)) (map_dead w189_5) (by decide +kernel)
def k189_6_1 : List Entry := [([23,296,863,112,60,77],[34],[]),([23,296,879,112,60,61],[],[]),([23,296,879,112,60,77],[30],[]),([23,310,56,28,591,96],[],[]),([23,310,56,28,591,100],[],[]),([23,310,56,28,607,96],[],[]),([23,310,56,28,607,100],[],[]),([23,310,56,863,112,60],[],[]),([23,310,56,879,112,60],[],[]),([23,574,52,863,112,60],[],[]),([23,574,52,879,112,60],[],[]),([39,58,316,863,112,76],[],[]),([39,58,316,879,112,76],[],[]),([39,574,52,863,112,60],[],[]),([39,574,52,879,112,60],[],[]),([87,847,68,92,53,108],[23],[]),([103,847,68,92,53,108],[25],[]),([307,300,20,19,300,22],[0],[]),([307,300,20,19,301,36],[],[]),([307,300,20,23,296,29],[0],[]),([307,300,21,42,296,30],[],[])]
set_option maxRecDepth 100000 in
theorem v189_6_1 : ∀ e ∈ k189_6_1, ¬ Live516.live basicOps goal 6 (wsOf c189.2 e).toFinset := level_sound hR189 6 k189_6_1 (D189_5.map (wsOf c189.2)) (map_dead w189_5) (by decide +kernel)
def D189_6 : List Entry := k189_6_0 ++ (k189_6_1)
theorem w189_6 : ∀ e ∈ D189_6, ¬ Live516.live basicOps goal 6 (wsOf c189.2 e).toFinset := (app_dead v189_6_0 v189_6_1)
def k189_7_0 : List Entry := [([19,26,56,863,112],[],[0]),([19,26,56,863,116],[],[]),([19,26,56,879,112],[],[1]),([19,26,56,879,116],[],[]),([19,26,60,863,112],[],[]),([19,26,60,863,116],[],[]),([19,26,60,879,112],[],[]),([19,26,60,879,116],[],[]),([19,300,20,25,583],[0,30],[]),([19,300,20,25,591],[0,30],[2,3]),([19,300,20,25,599],[0,34],[]),([19,300,20,25,607],[0,34],[4,5]),([19,300,20,25,1119],[0,30],[]),([19,300,20,29,583],[0,30],[]),([19,300,20,29,591],[0,30],[6,7]),([19,300,20,29,599],[0,34],[]),([19,300,20,29,607],[0,34],[8,9]),([19,300,20,29,1119],[0,30],[]),([19,300,20,35,56],[15,1,28],[]),([19,300,20,35,60],[15,1,28],[]),([19,300,20,35,300],[0,1,2,28],[10]),([19,300,20,39,56],[15,1,28],[]),([19,300,20,39,60],[15,1,28],[]),([19,300,20,39,296],[0,1,2,28],[10]),([19,300,20,71,56],[15,1,28],[]),([19,300,20,71,60],[15,30,28],[]),([19,300,20,87,56],[15,1,28],[]),([19,300,20,87,60],[15,34,28],[]),([19,300,20,583,58],[0],[11,12]),([19,300,20,583,62],[0],[]),([19,300,20,591,50],[0],[13,14]),([19,300,20,591,54],[0],[]),([19,300,20,591,96],[34,30,6,28],[2,6]),([19,300,20,591,100],[28],[3,7]),([19,300,20,599,58],[0],[15,16]),([19,300,20,599,62],[0],[]),([19,300,20,607,50],[0],[17,18]),([19,300,20,607,54],[0],[]),([19,300,20,607,96],[30,34,6,28],[4,8]),([19,300,20,607,100],[28],[5,9]),([19,1127,60,58,88],[],[]),([19,1127,60,58,92],[],[]),([19,1143,60,58,88],[],[]),([19,1143,60,58,92],[],[]),([23,56,863,112,60],[22,23,36,35],[19,20,21,22,23,24]),([23,56,879,112,60],[24,25,36,35],[25,26,27,28,29,30]),([23,57,568,28,583],[0,30],[]),([23,57,568,28,591],[0,30],[31,32]),([23,57,568,28,599],[0,34],[]),([23,57,568,28,607],[0,34],[33,34])]
set_option maxRecDepth 100000 in
theorem v189_7_0 : ∀ e ∈ k189_7_0, ¬ Live516.live basicOps goal 7 (wsOf c189.2 e).toFinset := level_sound hR189 7 k189_7_0 (D189_6.map (wsOf c189.2)) (map_dead w189_6) (by decide +kernel)
def k189_7_1 : List Entry := [([23,57,568,28,1119],[0,30],[]),([23,57,568,863,112],[],[35,36,31,2]),([23,57,568,863,116],[],[32,3]),([23,57,568,879,112],[],[37,38,33,4]),([23,57,568,879,116],[],[34,5]),([23,57,1135,128,60],[15],[36]),([23,57,1151,128,60],[15],[38]),([23,61,568,28,583],[0,30],[]),([23,61,568,28,591],[0,30],[39,40]),([23,61,568,28,599],[0,34],[]),([23,61,568,28,607],[0,34],[41,42]),([23,61,568,28,1119],[0,30],[]),([23,61,568,44,583],[0,30],[]),([23,61,568,44,591],[0,30],[43,44]),([23,61,568,44,599],[0,34],[]),([23,61,568,44,607],[0,34],[45,46]),([23,61,568,44,1119],[0,30],[]),([23,61,568,863,112],[],[47,39,43]),([23,61,568,863,116],[],[40,44]),([23,61,568,879,112],[],[48,41,45]),([23,61,568,879,116],[],[42,46]),([23,296,30,855,76],[],[]),([23,296,30,863,68],[],[]),([23,296,30,863,112],[0],[39,2,43]),([23,296,30,863,116],[0],[40,3,44]),([23,296,30,871,76],[],[]),([23,296,30,879,68],[],[]),([23,296,30,879,112],[0],[41,4,45]),([23,296,30,879,116],[0],[42,5,46]),([23,296,44,583,78],[0],[]),([23,296,44,591,70],[0],[]),([23,296,44,591,96],[34,30,5,28],[31,39]),([23,296,44,591,100],[28],[32,40]),([23,296,44,599,78],[0],[]),([23,296,44,607,70],[0],[]),([23,296,44,607,96],[30,34,5,28],[33,41]),([23,296,44,607,100],[28],[34,42]),([23,296,46,863,112],[0],[]),([23,296,46,863,116],[0],[]),([23,296,46,879,112],[0],[]),([23,296,46,879,116],[0],[]),([23,296,863,112,60],[22,6,23,36,10],[49,50,35,47]),([23,296,879,112,60],[24,6,25,36,10],[51,52,37,48]),([23,310,56,28,583],[0,30],[]),([23,310,56,28,591],[0,30],[53,54]),([23,310,56,28,599],[0,34],[]),([23,310,56,28,607],[0,34],[55,56]),([23,310,56,28,1119],[0,30],[]),([23,310,56,863,112],[],[57,53]),([23,310,56,863,116],[],[54])]
set_option maxRecDepth 100000 in
theorem v189_7_1 : ∀ e ∈ k189_7_1, ¬ Live516.live basicOps goal 7 (wsOf c189.2 e).toFinset := level_sound hR189 7 k189_7_1 (D189_6.map (wsOf c189.2)) (map_dead w189_6) (by decide +kernel)
def k189_7_2 : List Entry := [([23,310,56,879,112],[],[58,55]),([23,310,56,879,116],[],[56]),([23,310,316,855,56],[],[]),([23,310,316,863,112],[15],[53]),([23,310,316,863,116],[15],[54]),([23,310,316,871,56],[],[]),([23,310,316,879,112],[15],[55]),([23,310,316,879,116],[15],[56]),([23,310,1127,108,52],[9],[]),([23,310,1143,108,52],[9],[]),([23,318,312,863,112],[],[]),([23,318,312,863,116],[],[]),([23,318,312,879,112],[],[]),([23,318,312,879,116],[],[]),([23,574,52,863,112],[],[59,53]),([23,574,52,863,116],[],[54]),([23,574,52,879,112],[],[60,55]),([23,574,52,879,116],[],[56]),([23,590,334,52,41],[9],[]),([23,1127,92,68,76],[1,28],[]),([23,1127,92,68,78],[0],[]),([23,1135,102,76,116],[],[]),([23,1143,92,68,76],[1,28],[]),([23,1143,92,68,78],[0],[]),([23,1151,102,76,116],[],[]),([27,1135,128,60,93],[34],[50]),([27,1151,128,60,93],[30],[52]),([39,58,60,863,112],[],[53]),([39,58,60,863,116],[],[54]),([39,58,60,879,112],[],[55]),([39,58,60,879,116],[],[56]),([39,58,76,95,112],[],[]),([39,58,76,95,116],[],[]),([39,58,76,111,112],[],[]),([39,58,76,111,116],[],[]),([39,58,78,366,112],[],[]),([39,58,78,366,116],[],[]),([39,58,78,382,112],[],[]),([39,58,78,382,116],[],[]),([39,58,92,1119,112],[36],[]),([39,58,92,1119,116],[36],[]),([39,58,92,1135,112],[36],[]),([39,58,92,1135,116],[36],[]),([39,58,108,1135,48],[],[]),([39,58,124,1135,48],[],[]),([39,58,316,863,112],[15],[61]),([39,58,316,863,116],[15],[]),([39,58,316,879,112],[15],[62]),([39,58,316,879,116],[15],[]),([39,58,1135,128,60],[36],[57,61])]
set_option maxRecDepth 100000 in
theorem v189_7_2 : ∀ e ∈ k189_7_2, ¬ Live516.live basicOps goal 7 (wsOf c189.2 e).toFinset := level_sound hR189 7 k189_7_2 (D189_6.map (wsOf c189.2)) (map_dead w189_6) (by decide +kernel)
def k189_7_3 : List Entry := [([39,58,1151,128,60],[36],[58,62]),([39,574,52,863,112],[15],[63]),([39,574,52,863,116],[15],[]),([39,574,52,879,112],[15],[64]),([39,574,52,879,116],[15],[]),([39,1127,92,68,76],[4,3,35,36],[]),([39,1135,102,76,116],[],[]),([39,1143,92,68,76],[4,3,35,36],[]),([39,1151,102,76,116],[],[]),([47,54,308,863,112],[],[]),([47,54,308,863,116],[],[]),([47,54,308,879,112],[],[]),([47,54,308,879,116],[],[]),([47,570,56,863,112],[],[]),([47,570,56,863,116],[],[]),([47,570,56,879,112],[],[]),([47,570,56,879,116],[],[]),([51,300,20,19,300],[0,2,7,28],[10]),([51,300,20,23,56],[15,35,36],[]),([51,300,20,23,60],[35,36],[]),([51,300,20,23,296],[0,7,2,28],[10]),([55,51,300,20,296],[0,28],[]),([55,51,300,568,44],[7,0,35,36],[]),([55,55,88,840,44],[35,36],[]),([55,55,92,840,44],[35,36],[]),([55,55,296,568,44],[0,2,7,28],[]),([87,847,68,92,53],[0,23],[65]),([103,847,68,92,53],[0,25],[66]),([303,54,76,95,48],[],[]),([303,54,76,95,112],[23],[]),([303,54,76,95,116],[],[]),([303,54,76,111,48],[],[]),([303,54,76,111,112],[25],[]),([303,54,76,111,116],[],[]),([303,54,78,366,112],[23],[]),([303,54,78,366,116],[],[]),([303,54,78,382,112],[25],[]),([303,54,78,382,116],[],[]),([303,54,92,1119,112],[],[]),([303,54,92,1119,116],[],[]),([303,54,92,1135,112],[],[]),([303,54,92,1135,116],[],[]),([303,54,108,1135,48],[25],[]),([303,54,124,1135,48],[23],[]),([303,54,1135,128,60],[23],[59,63]),([303,54,1151,128,60],[25],[60,64]),([303,1135,98,72,124],[],[]),([303,1151,98,72,124],[],[]),([307,58,572,17,41],[1],[]),([307,58,572,19,56],[7,1],[])]
set_option maxRecDepth 100000 in
theorem v189_7_3 : ∀ e ∈ k189_7_3, ¬ Live516.live basicOps goal 7 (wsOf c189.2 e).toFinset := level_sound hR189 7 k189_7_3 (D189_6.map (wsOf c189.2)) (map_dead w189_6) (by decide +kernel)
def k189_7_4 : List Entry := [([307,58,572,37,60],[1,28],[]),([307,300,20,19,41],[0],[]),([307,300,20,19,42],[0],[]),([307,300,20,19,300],[0,28],[10,67]),([307,300,20,19,301],[0],[68]),([307,300,20,23,26],[0],[]),([307,300,20,23,60],[0,28],[]),([307,300,20,23,296],[0,28],[10,69]),([307,300,20,23,297],[0],[68]),([307,300,21,42,296],[0,28],[70]),([307,300,21,43,560],[0],[]),([307,300,21,43,568],[0],[]),([307,300,21,294,60],[15,0,28],[])]
set_option maxRecDepth 100000 in
theorem v189_7_4 : ∀ e ∈ k189_7_4, ¬ Live516.live basicOps goal 7 (wsOf c189.2 e).toFinset := level_sound hR189 7 k189_7_4 (D189_6.map (wsOf c189.2)) (map_dead w189_6) (by decide +kernel)
def D189_7 : List Entry := k189_7_0 ++ (k189_7_1 ++ (k189_7_2 ++ (k189_7_3 ++ (k189_7_4))))
theorem w189_7 : ∀ e ∈ D189_7, ¬ Live516.live basicOps goal 7 (wsOf c189.2 e).toFinset := (app_dead v189_7_0 (app_dead v189_7_1 (app_dead v189_7_2 (app_dead v189_7_3 v189_7_4))))
def k189_8_0 : List Entry := [([19,26,56,855],[0,30],[]),([19,26,56,863],[0,30],[0,1]),([19,26,56,871],[0,34],[]),([19,26,56,879],[0,34],[2,3]),([19,26,56,1391],[0,30],[]),([19,26,60,855],[0,30],[]),([19,26,60,863],[0,30],[4,5]),([19,26,60,871],[0,34],[]),([19,26,60,879],[0,34],[6,7]),([19,26,60,1391],[0,30],[]),([19,26,1127,60],[],[]),([19,26,1135,52],[],[]),([19,26,1135,128],[0],[0,4]),([19,26,1135,132],[0],[1,5]),([19,26,1143,60],[],[]),([19,26,1151,52],[],[]),([19,26,1151,128],[0],[2,6]),([19,26,1151,132],[0],[3,7]),([19,62,1135,128],[7],[]),([19,62,1135,132],[7],[]),([19,62,1151,128],[7],[]),([19,62,1151,132],[7],[]),([19,74,76,298],[0,23,4,7,25,28],[]),([19,78,42,72],[15,7,28],[]),([19,78,42,76],[7,28],[]),([19,300,20,25],[0,15,1,28,10,30,34,35],[8,9,10,11,12]),([19,300,20,29],[0,15,1,28,10,30,34,35],[13,14,15,16,17]),([19,300,20,35],[0,2,1,15,4,28,10,30,23,34,25,35],[18,19,20]),([19,300,20,39],[0,2,1,15,4,28,10,30,23,34,25,35],[21,22,23]),([19,300,20,43],[0,1,2,15,4,28,10,30,23,34,25,36],[23]),([19,300,20,47],[0,1,2,15,4,28,10,30,23,34,25,35],[20]),([19,300,20,71],[0,30,1,15,2,4,23,28,10,34,32,35],[24,25]),([19,300,20,79],[0,30,1,15,4,23,28,10,34,32,35],[]),([19,300,20,87],[0,34,1,15,2,4,25,28,10,30,32,35],[26,27]),([19,300,20,95],[0,34,1,15,4,25,28,10,30,32,35],[]),([19,300,20,583],[0,30,6,23,15,4,28,10,25,35],[28,29,8,13]),([19,300,20,591],[0,30,6,15,4,28,10,34,25,35,23],[30,31,32,33,9,14]),([19,300,20,599],[0,34,6,23,15,4,28,10,35],[34,35,10,15]),([19,300,20,607],[0,34,6,15,4,28,10,30,23,35,25],[36,37,38,39,11,16]),([19,300,20,1119],[0,34,30,31,23,28],[12,17]),([19,300,863,112],[34,30,6,7,28],[32]),([19,300,863,116],[0,7,28],[33]),([19,300,879,112],[30,34,6,7,28],[38]),([19,300,879,116],[0,7,28],[39]),([19,574,1135,128],[7],[]),([19,574,1135,132],[7],[]),([19,574,1151,128],[7],[]),([19,574,1151,132],[7],[]),([19,1127,60,58],[0],[40,41]),([19,1143,60,58],[0],[42,43])]
set_option maxRecDepth 100000 in
theorem v189_8_0 : ∀ e ∈ k189_8_0, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_0 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_1 : List Entry := [([23,54,1127,60],[],[]),([23,54,1135,52],[],[]),([23,54,1135,128],[15],[4]),([23,54,1135,132],[15],[5]),([23,54,1143,60],[],[]),([23,54,1151,52],[],[]),([23,54,1151,128],[15],[6]),([23,54,1151,132],[15],[7]),([23,56,855,74],[0],[]),([23,56,863,66],[0],[]),([23,56,863,112],[34,15,30,22,23,35,36],[44]),([23,56,863,116],[15,35,36],[]),([23,56,871,74],[0],[]),([23,56,879,66],[0],[]),([23,56,879,112],[30,15,34,22,25,35,36],[45]),([23,56,879,116],[15,35,36],[]),([23,57,568,28],[0,1,28,10,30,34,35],[46,47,48,49,50]),([23,57,568,855],[0,30],[46,8]),([23,57,568,863],[0,30],[51,52,47,9]),([23,57,568,871],[0,34],[48,10]),([23,57,568,879],[0,34],[53,54,49,11]),([23,57,568,1391],[0,30],[50,12]),([23,57,1135,128],[15],[55,4,51]),([23,57,1135,132],[15],[5,52]),([23,57,1151,128],[15],[56,6,53]),([23,57,1151,132],[15],[7,54]),([23,60,855,58],[30],[]),([23,60,855,74],[0],[]),([23,60,863,50],[30],[]),([23,60,863,66],[0],[]),([23,60,863,112],[34,30,22,23,35,36],[]),([23,60,863,116],[35,36],[]),([23,60,871,58],[34],[]),([23,60,871,74],[0],[]),([23,60,879,50],[34],[]),([23,60,879,66],[0],[]),([23,60,879,112],[30,34,22,25,35,36],[]),([23,60,879,116],[35,36],[]),([23,61,568,28],[0,1,28,10,30,34,35],[57,58,59,60,61]),([23,61,568,44],[0,15,1,28,10,30,34,35],[62,63,64,65,66]),([23,61,568,855],[0,30],[57,62]),([23,61,568,863],[0,30],[67,68,58,63]),([23,61,568,871],[0,34],[59,64]),([23,61,568,879],[0,34],[69,70,60,65]),([23,61,568,1391],[0,30],[61,66]),([23,61,1135,128],[15,30],[67]),([23,61,1135,132],[15,30],[68]),([23,61,1151,128],[15,30],[69]),([23,61,1151,132],[15,34],[70]),([23,62,1127,56],[4],[])]
set_option maxRecDepth 100000 in
theorem v189_8_1 : ∀ e ∈ k189_8_1, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_1 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_2 : List Entry := [([23,62,1135,48],[4],[]),([23,62,1135,128],[15,30],[]),([23,62,1135,132],[15,30],[]),([23,62,1143,56],[4],[]),([23,62,1151,48],[4],[]),([23,62,1151,128],[15,30],[]),([23,62,1151,132],[15,34],[]),([23,74,42,572],[2,7,9,10,23,25],[]),([23,74,298,326],[1,0],[]),([23,74,316,567],[0,9],[]),([23,75,72,78],[9],[]),([23,75,840,44],[0,1,2,15,4,28,10,30,23,34,25,36],[]),([23,75,840,76],[1,3,4,0,2,28,10,30,23,34,25,36,14],[]),([23,75,840,78],[0,15,1,4,35,36,13],[]),([23,78,290,326],[1],[]),([23,78,298,60],[28],[]),([23,79,840,44],[0,1,2,15,4,28,10,30,23,34,25,35],[]),([23,79,840,76],[3,4,1,0,2,28,10,30,23,34,25,35,14],[]),([23,79,840,78],[0,15,4,13],[]),([23,111,840,44],[0,30,1,15,4,23,28,10,34,32,35],[]),([23,111,840,76],[3,4,1,0,30,23,28,10,34,32,35],[]),([23,111,840,78],[0,15,4,30],[]),([23,127,840,44],[0,34,1,15,4,25,28,10,30,32,35],[]),([23,127,840,76],[3,4,1,0,34,25,28,10,30,32,35],[]),([23,127,840,78],[0,15,4,34],[]),([23,296,30,855],[0,5,14,30],[71,57,8,62]),([23,296,30,863],[0,14,6,30],[72,73,74,58,9,63]),([23,296,30,871],[0,5,14,34],[75,59,10,64]),([23,296,30,879],[0,14,6,34],[76,77,78,60,11,65]),([23,296,30,1391],[0,14,31,23,30],[61,12,66]),([23,296,44,583],[0,30,5,3,4,14,28,10,34,25,35],[79,46,57]),([23,296,44,591],[0,30,5,3,4,14,6,28,10,34,25,35,23],[80,81,82,47,58]),([23,296,44,599],[0,34,5,3,4,14,28,10,30,23,35],[83,48,59]),([23,296,44,607],[0,34,5,3,4,14,6,28,10,30,23,35,25],[84,85,86,49,60]),([23,296,44,1119],[0,34,30,3,4,14,31,23,28],[50,61]),([23,296,46,855],[0,15,4,30],[]),([23,296,46,863],[0,15,4,30],[87,88]),([23,296,46,871],[0,15,4,34],[]),([23,296,46,879],[0,15,4,34],[89,90]),([23,296,46,1391],[0,15,4,30],[]),([23,296,855,78],[0],[71,79]),([23,296,863,70],[0],[72,80]),([23,296,863,112],[34,0,30,5,28],[91,32,73,81,87,51,67]),([23,296,863,116],[0,28],[33,74,82,88,52,68]),([23,296,871,78],[0],[75,83]),([23,296,879,70],[0],[76,84]),([23,296,879,112],[30,0,34,5,28],[92,38,77,85,89,53,69]),([23,296,879,116],[0,28],[39,78,86,90,54,70]),([23,310,56,28],[15,1,3,2,28,10,30,34,35],[93,94,95,96,97]),([23,310,56,855],[7,15,9,30],[93])]
set_option maxRecDepth 100000 in
theorem v189_8_2 : ∀ e ∈ k189_8_2, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_2 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_3 : List Entry := [([23,310,56,863],[7,30],[98,99,94]),([23,310,56,871],[7,15,9,34],[95]),([23,310,56,879],[7,34],[100,101,96]),([23,310,56,1391],[7,30],[97]),([23,310,316,54],[15,2,3,14,4,28],[]),([23,310,316,855],[15,4,30],[102,93]),([23,310,316,863],[15,30],[103,104,94]),([23,310,316,871],[15,4,34],[105,95]),([23,310,316,879],[15,34],[106,107,96]),([23,310,316,1391],[15,30],[97]),([23,310,846,36],[3,9,4,28],[]),([23,310,1127,108],[9],[108]),([23,310,1135,128],[15],[98,103]),([23,310,1135,132],[15],[99,104]),([23,310,1143,108],[9],[109]),([23,310,1151,128],[15],[100,106]),([23,310,1151,132],[15],[101,107]),([23,311,338,92],[3,2,4],[]),([23,311,338,348],[3,2,4],[]),([23,311,342,92],[3,2,4],[]),([23,311,342,348],[0,3,2,4,9],[]),([23,311,374,92],[3,2],[]),([23,311,390,92],[3,2],[]),([23,318,312,855],[0,30],[]),([23,318,312,863],[0,30],[110,111]),([23,318,312,871],[0,34],[]),([23,318,312,879],[0,34],[112,113]),([23,318,312,1391],[0,30],[]),([23,318,1135,128],[0,15],[110]),([23,318,1135,132],[0,15],[111]),([23,318,1151,128],[0,15],[112]),([23,318,1151,132],[0,15],[113]),([23,566,1127,60],[4],[]),([23,566,1135,128],[7,15],[110]),([23,566,1135,132],[7,15],[111]),([23,566,1143,60],[4],[]),([23,566,1151,128],[7,15],[112]),([23,566,1151,132],[7,15],[113]),([23,574,52,855],[0,30],[93]),([23,574,52,863],[0,30],[114,115,94]),([23,574,52,871],[0,34],[95]),([23,574,52,879],[0,34],[116,117,96]),([23,574,52,1391],[0,30],[97]),([23,574,1127,56],[],[102]),([23,574,1135,128],[15],[114,103]),([23,574,1135,132],[15],[115,104]),([23,574,1143,56],[],[105]),([23,574,1151,128],[15],[116,106]),([23,574,1151,132],[15],[117,107]),([23,590,52,60],[3,4,1,2,28,5,6,30,10,34,23,35],[])]
set_option maxRecDepth 100000 in
theorem v189_8_3 : ∀ e ∈ k189_8_3, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_3 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_4 : List Entry := [([23,590,52,62],[0,15,1,4,28],[]),([23,590,334,52],[15,1,6,35,36,9,10],[118]),([23,1127,56,58],[0],[]),([23,1127,56,88],[15,35,36],[]),([23,1127,56,92],[35,36],[]),([23,1127,56,94],[15,30],[]),([23,1127,60,86],[15],[]),([23,1127,60,94],[15],[]),([23,1127,88,94],[9],[]),([23,1127,92,68],[0,14,28],[119,120]),([23,1127,92,86],[9],[]),([23,1127,110,64],[15,4],[]),([23,1127,110,68],[15,4,35,36,9],[]),([23,1135,48,58],[0],[]),([23,1135,48,88],[15,35,36],[]),([23,1135,48,92],[35,36],[]),([23,1135,48,94],[15,30],[]),([23,1135,52,94],[15],[]),([23,1135,102,72],[15,4],[]),([23,1135,102,76],[15,23],[121]),([23,1143,56,58],[0],[]),([23,1143,56,88],[15,35,36],[]),([23,1143,56,92],[35,36],[]),([23,1143,56,94],[15,34],[]),([23,1143,60,86],[15],[]),([23,1143,60,94],[15],[]),([23,1143,88,94],[9],[]),([23,1143,92,68],[0,14,28],[122,123]),([23,1143,92,86],[9],[]),([23,1143,110,64],[15,4],[]),([23,1143,110,68],[15,4,35,36,9],[]),([23,1151,48,58],[0],[]),([23,1151,48,88],[15,35,36],[]),([23,1151,48,92],[35,36],[]),([23,1151,48,94],[15,34],[]),([23,1151,52,94],[15],[]),([23,1151,102,72],[15,4],[]),([23,1151,102,76],[15,25],[124]),([27,60,863,112],[34,30,5,0,7,28],[81]),([27,60,863,116],[0,7,28],[82]),([27,60,879,112],[30,34,5,0,7,28],[85]),([27,60,879,116],[0,7,28],[86]),([27,62,1135,128],[0],[87]),([27,62,1135,132],[0],[88]),([27,62,1151,128],[0],[89]),([27,62,1151,132],[0],[90]),([27,76,95,112],[34,30,5,0,7,28],[]),([27,76,95,116],[0,7,28],[]),([27,76,111,112],[30,34,5,0,7,28],[]),([27,76,111,116],[0,7,28],[])]
set_option maxRecDepth 100000 in
theorem v189_8_4 : ∀ e ∈ k189_8_4, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_4 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_5 : List Entry := [([27,78,366,112],[30,34,5,0,7,28],[]),([27,78,366,116],[0,7,28],[]),([27,78,382,112],[30,34,5,0,7,28],[]),([27,78,382,116],[0,7,28],[]),([27,92,1119,112],[34,30,5,0,35,36,7],[]),([27,92,1119,116],[35,36,7],[]),([27,92,1135,112],[30,34,5,0,35,36,7],[]),([27,92,1135,116],[35,36,7],[]),([27,108,1135,48],[23,34,24,0,7,28],[]),([27,124,1135,48],[22,0,7,28],[]),([27,1135,128,60],[22,6,23,7,36,10],[125,91]),([27,1151,128,60],[24,6,25,7,36,10],[126,92]),([31,54,1135,128],[0],[]),([31,54,1135,132],[0],[]),([31,54,1151,128],[0],[]),([31,54,1151,132],[0],[]),([31,310,1135,128],[0],[]),([31,310,1135,132],[0],[]),([31,310,1151,128],[0],[]),([31,310,1151,132],[0],[]),([39,50,1127,60],[],[]),([39,50,1135,52],[],[]),([39,50,1135,128],[15,35,36],[]),([39,50,1135,132],[15,35,36],[]),([39,50,1143,60],[],[]),([39,50,1151,52],[],[]),([39,50,1151,128],[15,35,36],[]),([39,50,1151,132],[15,35,36],[]),([39,58,60,855],[0,30],[93]),([39,58,60,863],[0,30],[127,128,94]),([39,58,60,871],[0,34],[95]),([39,58,60,879],[0,34],[129,130,96]),([39,58,60,1391],[0,30],[97]),([39,58,76,87],[7,30],[]),([39,58,76,95],[7,30],[131,132]),([39,58,76,103],[7,34],[]),([39,58,76,111],[7,34],[133,134]),([39,58,76,1391],[7,30],[]),([39,58,78,358],[7,30],[]),([39,58,78,366],[7,30],[135,136]),([39,58,78,374],[7,34],[]),([39,58,78,382],[7,34],[137,138]),([39,58,92,1111],[7,15,9,30,36],[]),([39,58,92,1119],[7,30,36],[139,140]),([39,58,92,1127],[7,15,9,34,36],[]),([39,58,92,1135],[7,34,36],[141,142]),([39,58,92,1391],[7,30,36],[]),([39,58,108,1135],[7,23],[143]),([39,58,124,1135],[7,25],[144]),([39,58,316,855],[7,30,15],[])]
set_option maxRecDepth 100000 in
theorem v189_8_5 : ∀ e ∈ k189_8_5, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_5 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_6 : List Entry := [([39,58,316,863],[7,30,15],[145,146]),([39,58,316,871],[7,34,15],[]),([39,58,316,879],[7,34,15],[147,148]),([39,58,316,1391],[7,30,15],[]),([39,58,1127,60],[7,30],[]),([39,58,1135,52],[7,22,30],[]),([39,58,1135,128],[15,22,23,36,35],[149,135,127,139,98,145]),([39,58,1135,132],[22,23,15,36,35],[136,128,140,99,146]),([39,58,1143,60],[7,34],[]),([39,58,1151,52],[7,24,34],[]),([39,58,1151,128],[15,24,25,36,35],[150,137,129,141,100,147]),([39,58,1151,132],[23,25,15,36,35],[138,130,142,101,148]),([39,62,1135,128],[15,36],[]),([39,62,1135,132],[15,36],[]),([39,62,1151,128],[15,36],[]),([39,62,1151,132],[15,36],[]),([39,574,52,855],[0,30,15],[]),([39,574,52,863],[0,30,15],[151,152]),([39,574,52,871],[0,34,15],[]),([39,574,52,879],[0,34,15],[153,154]),([39,574,52,1391],[0,30,15],[]),([39,574,1127,56],[],[102]),([39,574,1135,128],[],[127,151,145,103]),([39,574,1135,132],[],[128,152,146,104]),([39,574,1143,56],[],[105]),([39,574,1151,128],[],[129,153,147,106]),([39,574,1151,132],[],[130,154,148,107]),([39,590,52,60],[5,6,4,3,28,21,30,23,34,25,36],[]),([39,1127,60,86],[15,9],[]),([39,1127,92,68],[0,3,9,28],[155]),([39,1127,110,68],[9,15],[108]),([39,1127,110,76],[15],[]),([39,1135,52,94],[15],[]),([39,1135,102,76],[9,23],[156]),([39,1143,60,86],[15,9],[]),([39,1143,92,68],[0,3,9,28],[157]),([39,1143,110,68],[9,15],[109]),([39,1143,110,76],[15],[]),([39,1151,52,94],[15],[]),([39,1151,102,76],[9,25],[158]),([47,50,1127,60],[],[]),([47,50,1127,76],[],[]),([47,50,1135,52],[],[]),([47,50,1135,128],[0,35,36],[]),([47,50,1135,132],[0,35,36],[]),([47,50,1143,60],[],[]),([47,50,1143,76],[],[]),([47,50,1151,52],[],[]),([47,50,1151,128],[0,35,36],[]),([47,50,1151,132],[0,35,36],[])]
set_option maxRecDepth 100000 in
theorem v189_8_6 : ∀ e ∈ k189_8_6, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_6 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_7 : List Entry := [([47,54,308,855],[0,30],[]),([47,54,308,863],[0,30],[159,160]),([47,54,308,871],[0,34],[]),([47,54,308,879],[0,34],[161,162]),([47,54,308,1391],[0,30],[]),([47,54,1135,128],[0],[4,159]),([47,54,1135,132],[0],[5,160]),([47,54,1151,128],[0],[6,161]),([47,54,1151,132],[0],[7,162]),([47,570,56,855],[0,30],[]),([47,570,56,863],[0,30],[163,164]),([47,570,56,871],[0,34],[]),([47,570,56,879],[0,34],[165,166]),([47,570,56,1391],[0,30],[]),([47,570,1127,88],[],[]),([47,570,1135,128],[],[4,163,159,110]),([47,570,1135,132],[],[5,164,160,111]),([47,570,1143,88],[],[]),([47,570,1151,128],[],[6,165,161,112]),([47,570,1151,132],[],[7,166,162,113]),([47,1127,56,86],[0,9],[]),([47,1127,110,64],[],[]),([47,1135,102,72],[],[]),([47,1143,56,86],[0,9],[]),([47,1143,110,64],[],[]),([47,1151,102,72],[],[]),([51,26,58,316],[0,2,7,28],[]),([51,62,78,48],[35,36],[]),([51,78,66,332],[7,6,28],[]),([51,300,20,19],[0,7,2,15,4,28,10,30,23,34,25,35,36,5],[167]),([51,300,20,23],[0,7,2,15,4,28,10,30,23,34,25,35,5],[168,169,170]),([51,300,20,27],[0,7,2,15,4,28,10,30,23,25,35,36,5],[170]),([51,300,20,31],[0,7,2,15,4,28,10,30,23,34,25,35,5],[167]),([51,574,37,78],[],[]),([51,574,78,68],[0,6,7,15,4,35,36],[]),([51,847,68,76],[0,7,35,36,15,4,23,25],[]),([55,51,300,20],[7,1,5,23,25,6,28],[171]),([55,51,300,568],[0,7,2,28],[172,171]),([55,51,840,28],[0,7,35,36,5],[172]),([55,51,840,44],[0,2,7,5,15,4,28,10,30,23,34,25,35,36],[]),([55,55,56,300],[5,6,28],[]),([55,55,56,838],[5],[]),([55,55,88,840],[0,6,15,35,36],[173]),([55,55,92,840],[0,6,35,36],[174]),([55,55,296,568],[0,2,7,28],[175,171]),([55,55,840,28],[0,7,2,5,4,6,10,28],[175]),([55,55,840,44],[0,1,5,15,2,4,28,10,30,23,34,25,35],[173,174]),([55,55,1110,44],[5],[]),([55,58,316,21],[7,2,9,28],[]),([55,59,72,76],[7,5,23,25,28],[])]
set_option maxRecDepth 100000 in
theorem v189_8_7 : ∀ e ∈ k189_8_7, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_7 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_8 : List Entry := [([55,59,840,44],[0,2,7,5,15,4,28,10,30,23,25,35,36],[]),([55,63,840,44],[0,7,5,2,15,4,28,10,30,23,34,25,35],[]),([55,71,90,44],[7],[]),([55,71,90,88],[4],[]),([55,71,1110,44],[4],[]),([55,78,66,78],[7],[]),([55,79,82,40],[7,15,4],[]),([55,79,82,72],[7,3,4],[]),([55,79,82,92],[7,4],[]),([55,566,46,70],[],[]),([55,574,49,326],[],[]),([55,574,52,46],[0,7,4,6,5,35,36],[]),([55,574,53,108],[23,0,4,25,5,35,36],[]),([55,574,53,124],[25,0,4,23,5,35,36],[]),([55,574,78,52],[6,7,15,4,35,36,23,25],[]),([55,574,78,68],[0,6,7,15,4,35,36],[]),([55,574,582,40],[7,3,28],[]),([55,574,582,56],[7,6,28],[]),([55,590,52,46],[0,15,6,5,4,35,36],[]),([55,839,56,57],[0,15,1],[]),([55,839,58,72],[0,15],[]),([55,839,92,65],[0],[]),([55,847,50,72],[0],[]),([87,847,68,92],[23,30,7,35,36,15,4,32],[176]),([87,847,68,124],[30,23,35,36],[]),([103,847,68,92],[25,34,7,35,36,15,4,32],[177]),([103,847,68,124],[34,25,35,36],[]),([295,58,1127,56],[7,4],[]),([295,58,1135,48],[7,4],[]),([295,58,1135,128],[7],[4,163]),([295,58,1135,132],[7],[5,164]),([295,58,1143,56],[7,4],[]),([295,58,1151,48],[7,4],[]),([295,58,1151,128],[7],[6,165]),([295,58,1151,132],[7],[7,166]),([295,62,1127,56],[],[]),([295,62,1135,48],[],[]),([295,62,1135,128],[30,23,7],[]),([295,62,1135,132],[7],[]),([295,62,1143,56],[],[]),([295,62,1151,48],[],[]),([295,62,1151,128],[34,25,7],[]),([295,62,1151,132],[7],[]),([295,1127,60,82],[7],[]),([295,1127,92,68],[7,9,28],[]),([295,1127,106,76],[],[]),([295,1135,52,90],[7],[]),([295,1135,98,76],[],[]),([295,1143,60,82],[7],[]),([295,1143,92,68],[7,9,28],[])]
set_option maxRecDepth 100000 in
theorem v189_8_8 : ∀ e ∈ k189_8_8, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_8 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_9 : List Entry := [([295,1143,106,76],[],[]),([295,1151,52,90],[7],[]),([295,1151,98,76],[],[]),([303,50,1135,64],[4],[]),([303,50,1135,128],[23],[]),([303,50,1135,132],[15],[]),([303,50,1151,64],[4],[]),([303,50,1151,128],[25],[]),([303,50,1151,132],[15],[]),([303,54,76,87],[0,23,30],[]),([303,54,76,95],[0,30,23],[178,179,180]),([303,54,76,103],[0,23,34],[]),([303,54,76,111],[0,34,25],[181,182,183]),([303,54,76,1391],[0,23,30],[]),([303,54,78,358],[0,23,30],[]),([303,54,78,366],[0,30,23],[178,184,185]),([303,54,78,374],[0,23],[]),([303,54,78,382],[0,34,25],[181,186,187]),([303,54,92,1111],[0,30],[]),([303,54,92,1119],[0,30],[188,189]),([303,54,92,1127],[0,34],[]),([303,54,92,1135],[0,34],[190,191]),([303,54,92,1391],[0,30],[]),([303,54,108,1135],[0,23,25],[192]),([303,54,124,1135],[0,25,23],[193]),([303,54,1127,60],[0,30],[]),([303,54,1135,52],[0,22,30,23],[]),([303,54,1135,64],[23],[178]),([303,54,1135,128],[15,22,23,36,35],[194,184,127,188,114,151]),([303,54,1135,132],[22,23,15,36,35],[185,128,189,115,152]),([303,54,1143,60],[0,34],[]),([303,54,1151,52],[0,24,34,25],[]),([303,54,1151,64],[25],[181]),([303,54,1151,128],[15,24,25,36,35],[195,186,129,190,116,153]),([303,54,1151,132],[23,25,15,36,35],[187,130,191,117,154]),([303,62,1127,56],[],[]),([303,62,1135,48],[],[]),([303,62,1135,128],[30,23],[]),([303,62,1135,132],[15],[]),([303,62,1143,56],[],[]),([303,62,1151,48],[],[]),([303,62,1151,128],[34,25],[]),([303,62,1151,132],[15],[]),([303,1127,56,90],[15],[]),([303,1127,60,80],[35,36],[]),([303,1127,60,84],[4,7,35,36,15],[]),([303,1127,106,64],[15],[]),([303,1127,106,72],[4],[]),([303,1135,48,90],[15],[]),([303,1135,98,72],[4,23],[196])]
set_option maxRecDepth 100000 in
theorem v189_8_9 : ∀ e ∈ k189_8_9, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_9 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_10 : List Entry := [([303,1143,56,90],[15],[]),([303,1143,60,80],[35,36],[]),([303,1143,60,84],[4,7,35,36,15],[]),([303,1143,106,64],[15],[]),([303,1143,106,72],[4],[]),([303,1151,48,90],[15],[]),([303,1151,98,72],[4,25],[197]),([307,58,572,17],[7,1,2,9,28],[198]),([307,58,572,19],[7,1],[199]),([307,58,572,21],[0,1,2,28],[]),([307,58,572,33],[7,0,9,10,23,25,1],[]),([307,58,572,37],[0,2,1,9,10,23,25],[200]),([307,300,20,19],[7,0,15,9,28,10,30,23,34,25,35],[201,202,203,204]),([307,300,20,23],[0,7,23,9,36,10,25],[205,206,207,208]),([307,300,20,27],[0,7,15,9,28,10,30,23,34,25,35],[201,205,207,208]),([307,300,20,31],[7,0,15,9,28,10,30,23,34,25,35],[202,203,204]),([307,300,21,35],[7,1,2],[198]),([307,300,21,42],[7,2,9,28],[198,209]),([307,300,21,43],[7,0,2],[198,210,211]),([307,300,21,290],[7,2,15,9,28,10,30,23,34,25,35],[210]),([307,300,21,294],[0,7,14,9,10,25,23,36],[205,212,209,211]),([307,300,39,76],[15,0,2,7,28],[212,200]),([311,46,54,76],[15,0,14,28],[]),([311,46,54,292],[0,5,7,28],[]),([319,51,1110,72],[],[]),([319,590,48,42],[7,15,9,6,28],[]),([319,590,48,58],[7,15,1,6,10,23,25],[]),([855,58,66,42],[0],[]),([855,58,66,94],[7],[]),([855,58,74,60],[0,7,28],[]),([855,58,74,94],[7],[]),([855,58,78,86],[15],[]),([855,58,94,82],[15,35,36],[]),([855,58,94,86],[15,4],[]),([855,62,70,88],[15,35,36],[]),([855,62,70,92],[35,36],[]),([855,78,66,86],[15],[]),([855,78,66,94],[15],[]),([855,78,70,92],[15,0,14,35,36],[119]),([855,78,70,94],[0,15],[120]),([855,78,70,108],[35,36,10],[]),([855,78,71,108],[0,14],[]),([855,78,71,124],[0,14],[]),([855,78,78,86],[0],[]),([855,78,86,90],[15,9],[]),([855,94,70,92],[9,0,15,4,35,36,21],[155]),([855,94,70,94],[0,15,35,36,9,4],[]),([855,94,70,108],[35,36],[]),([855,94,82,90],[7,15],[]),([863,50,74,94],[7],[])]
set_option maxRecDepth 100000 in
theorem v189_8_10 : ∀ e ∈ k189_8_10, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_10 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def k189_8_11 : List Entry := [([863,50,74,124],[7,28],[]),([863,50,78,86],[15],[]),([863,50,94,82],[15,35,36],[]),([863,50,94,86],[15,4],[]),([863,70,74,86],[15],[]),([863,70,74,94],[15],[]),([863,70,78,86],[0],[]),([863,70,78,116],[35,36],[]),([863,70,94,82],[15,9],[]),([863,86,78,86],[0,15],[]),([863,86,78,116],[35,36],[]),([863,86,90,90],[7,15],[]),([863,86,90,124],[7,15,9,28],[]),([871,58,66,42],[0],[]),([871,58,66,94],[7],[]),([871,58,74,94],[7],[]),([871,58,78,86],[15],[]),([871,58,94,82],[15,35,36],[]),([871,58,94,86],[15,4],[]),([871,62,70,92],[35,36],[]),([871,78,66,86],[15],[]),([871,78,66,94],[15],[]),([871,78,70,92],[15,0,14,35,36],[122]),([871,78,70,94],[0,15],[123]),([871,78,70,108],[35,36,10],[]),([871,78,71,108],[0,14],[]),([871,78,71,124],[0,14],[]),([871,78,78,86],[0],[]),([871,78,86,90],[15,9],[]),([871,94,70,92],[9,0,15,4,35,36,21],[157]),([871,94,70,94],[0,15,35,36,9,4],[]),([871,94,70,108],[35,36],[]),([871,94,82,90],[7,15],[]),([879,50,74,94],[7],[]),([879,50,74,124],[7,28],[]),([879,50,78,86],[15],[]),([879,50,94,82],[15,35,36],[]),([879,50,94,86],[15,4],[]),([879,70,74,86],[15],[]),([879,70,74,94],[15],[]),([879,70,78,86],[0],[]),([879,70,78,116],[35,36],[]),([879,70,94,82],[15,9],[]),([879,86,78,86],[0,15],[]),([879,86,78,116],[35,36],[]),([879,86,90,90],[7,15],[]),([879,86,90,124],[7,15,9,28],[])]
set_option maxRecDepth 100000 in
theorem v189_8_11 : ∀ e ∈ k189_8_11, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := level_sound hR189 8 k189_8_11 (D189_7.map (wsOf c189.2)) (map_dead w189_7) (by decide +kernel)
def D189_8 : List Entry := k189_8_0 ++ (k189_8_1 ++ (k189_8_2 ++ (k189_8_3 ++ (k189_8_4 ++ (k189_8_5 ++ (k189_8_6 ++ (k189_8_7 ++ (k189_8_8 ++ (k189_8_9 ++ (k189_8_10 ++ (k189_8_11)))))))))))
theorem w189_8 : ∀ e ∈ D189_8, ¬ Live516.live basicOps goal 8 (wsOf c189.2 e).toFinset := (app_dead v189_8_0 (app_dead v189_8_1 (app_dead v189_8_2 (app_dead v189_8_3 (app_dead v189_8_4 (app_dead v189_8_5 (app_dead v189_8_6 (app_dead v189_8_7 (app_dead v189_8_8 (app_dead v189_8_9 (app_dead v189_8_10 v189_8_11)))))))))))
def k189_9_0 : List Entry := [([19,26,56],[0,7,15,28,10,30,34,35],[0,1,2,3,4]),([19,26,60],[0,7,1,28,10,30,34,35],[5,6,7,8,9]),([19,26,74],[0,1,14,15,4,28,10,30,23,34,25,36],[]),([19,26,78],[0,1,14,15,4,28,10,30,23,34,25],[]),([19,26,110],[0,1,30,15,4,23,28,10,34,32,35],[]),([19,26,126],[0,1,34,15,4,25,28,10,30,32,35],[]),([19,26,1127],[0,14,23,7,30],[10,0,5]),([19,26,1135],[0,14,23,30],[11,12,13,1,6]),([19,26,1143],[0,14,23,7,34],[14,2,7]),([19,26,1151],[0,14,25,34],[15,16,17,3,8]),([19,26,1663],[0,14,31,23,30],[4,9]),([19,62,1127],[7,8,4,30],[]),([19,62,1135],[7,8,4,30],[18,19]),([19,62,1143],[7,8,4,34],[]),([19,62,1151],[7,8,4,34],[20,21]),([19,62,1663],[7,8,4,30],[]),([19,74,42],[0,14,7,15,4,28,10,30,23,34,25,35],[]),([19,74,72],[7,15,23,28,10,34,25,35],[]),([19,74,76],[7,15,4,28,9,23,10,34,25,35],[22]),([19,74,298],[0,23,1,4,10,25],[22]),([19,78,34],[0,14,7,15,4,28,10,30,23,34,25,35],[]),([19,78,42],[0,2,1,15,4,28,10,30,23,34,25,35],[23,24]),([19,78,290],[0,23,1,4,10,2,15],[]),([19,78,298],[0,23,7,2,4,10,25],[]),([19,300,20],[15,4,28,10,30,34,35],[25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]),([19,300,855],[0,30,6,7,15,4,28,10,34,23,25,35],[35]),([19,300,863],[0,30,6,7,15,4,28,10,34,25,35,23],[40,41,36]),([19,300,871],[0,34,6,7,15,4,28,10,30,23,35],[37]),([19,300,879],[0,34,6,7,15,4,28,10,30,23,35,25],[42,43,38]),([19,300,1391],[0,34,30,7,15,4,23,28,10,35],[39]),([19,323,76],[0,2,7,4,6,15,28],[]),([19,323,588],[0,1,2,4,6,7,10,15],[]),([19,327,76],[0,2,4,5,23,25,28],[]),([19,327,588],[7,0,2,4,6,10,23,25],[]),([19,359,76],[0,30,2,4,23,15,32,28],[]),([19,375,76],[0,34,2,4,25,15,32,28],[]),([19,574,1127],[7,8,4,30],[]),([19,574,1135],[7,30],[44,45]),([19,574,1143],[7,8,4,34],[]),([19,574,1151],[7,34],[46,47]),([19,574,1663],[7,30],[]),([19,590,37],[7,2,23,25,5,6,28],[]),([19,1127,60],[7,30,23,15,9,28,10,34,25,35],[48]),([19,1127,74],[0,7,5,35,36],[48]),([19,1127,92],[7,5,9,30,14,25,28],[]),([19,1135,52],[7,30,22,23,15,9,28,10,34,25,35],[]),([19,1135,66],[0,7,22,6,35,36],[]),([19,1135,128],[34,30,22,23,7,15,28,10,35,36,0],[12,18,40,44]),([19,1135,132],[7,22,15,28,10,35,36,0],[13,19,41,45]),([19,1143,60],[7,34,23,15,9,28,10,35],[49])]
set_option maxRecDepth 100000 in
theorem v189_9_0 : ∀ e ∈ k189_9_0, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_0 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_1 : List Entry := [([19,1143,74],[0,7,5,35,36],[49]),([19,1143,92],[7,5,9,34,14,23,28],[]),([19,1151,52],[7,34,24,25,15,9,28,10,30,23,35],[]),([19,1151,66],[0,7,24,6,35,36],[]),([19,1151,128],[30,34,22,7,6,25,15,28,10,35,36],[16,20,42,46]),([19,1151,132],[7,23,34,15,28,10,35,36,0],[17,21,43,47]),([23,54,74],[15,2,4,7,28,10,30,23,34,25,35],[]),([23,54,78],[15,2,4,7,28,10,30,23,34,25,35],[]),([23,54,110],[15,2,30,4,23,28,10,34,32,35],[]),([23,54,126],[15,2,34,4,25,28,10,30,32,35],[]),([23,54,1127],[15,4,23,30],[50,5]),([23,54,1135],[15,4,23,30],[51,52,53,6]),([23,54,1143],[15,4,23,34],[54,7]),([23,54,1151],[15,4,25,34],[55,56,57,8]),([23,54,1663],[15,4,31,23,30],[9]),([23,56,307],[0,23,15,7,1,28,10,34,25,35],[]),([23,56,311],[0,23,7,15,1,28,10,30,34,25,35],[]),([23,56,343],[0,30,7,15,1,23,28,10,34,32,35],[]),([23,56,359],[0,34,7,15,1,25,28,10,30,32,35],[]),([23,56,855],[15,30,23,0,7,14,28,10,34,25,35,36],[58]),([23,56,863],[15,30,23,0,7,14,28,10,34,25,35,32,36],[59,60,61]),([23,56,871],[15,34,23,0,7,14,28,10,35,36],[62]),([23,56,879],[15,34,23,0,25,7,14,28,10,30,35,32,36],[63,64,65]),([23,56,1391],[15,34,30,31,23,35,36],[]),([23,57,568],[0,15,1,28,10,30,34,35],[66,25,67,68,69,70,71]),([23,57,1127],[15,14,1,30],[5,67]),([23,57,1135],[15,14,1,30],[72,73,6,68]),([23,57,1143],[15,14,1,34],[7,69]),([23,57,1151],[15,14,1,34],[74,75,8,70]),([23,57,1663],[15,14,1,30],[9,71]),([23,60,51],[35,23,1,28,10,34,25],[]),([23,60,55],[35,23,1,28,10,30,34,25],[]),([23,60,87],[30,1,23,28,10,34,32,35],[]),([23,60,103],[34,1,25,28,10,30,32,35],[]),([23,60,307],[0,23,1,28,10,34,25,35],[]),([23,60,311],[0,23,1,28,10,30,34,25,35],[]),([23,60,343],[0,30,1,23,28,10,34,32,35],[]),([23,60,359],[0,34,1,25,28,10,30,32,35],[]),([23,60,855],[30,23,1,14,28,10,34,25,35,36],[76,77]),([23,60,863],[30,23,1,14,28,10,34,25,35,32,36],[78,79,80,81]),([23,60,871],[34,23,1,14,28,10,35,36],[82,83]),([23,60,879],[34,23,1,25,14,28,10,30,35,32,36],[84,85,86,87]),([23,60,1391],[30,34,31,23,35,36],[]),([23,61,568],[0,1,28,10,30,34,35],[88,89,90,91,92,93,94]),([23,61,1127],[30,14,1,15],[90]),([23,61,1135],[30,14,1,15],[95,96,91]),([23,61,1143],[34,14,1,15],[92]),([23,61,1151],[34,14,1,15],[97,98,93]),([23,61,1663],[30,14,1,15],[94]),([23,62,66],[15,1,4,9,28,10,30,23,34,25,35],[])]
set_option maxRecDepth 100000 in
theorem v189_9_1 : ∀ e ∈ k189_9_1, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_1 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_2 : List Entry := [([23,62,70],[0,15,1,4,9,28,10,30,23,34,25,35],[]),([23,62,102],[0,15,1,30,4,9,23,28,10,34,32,35],[]),([23,62,118],[0,15,1,34,4,9,25,28,10,30,32,35],[]),([23,62,1127],[15,23,4,30],[99]),([23,62,1135],[15,4,23,30],[100,101,102]),([23,62,1143],[15,23,4,34],[103]),([23,62,1151],[15,4,25,34],[104,105,106]),([23,62,1663],[15,31,23,30],[]),([23,66,72],[15,5,7,2,28,10,30,22,34,23,25,35],[]),([23,66,76],[5,15,4,2,10,30,13,28,22,34,23,25,35],[]),([23,66,78],[15,2,35,4,10,30,13,28],[]),([23,66,334],[15,4,13,28],[]),([23,66,583],[0,15,4],[]),([23,70,72],[15,6,7,2,28,10,30,23,34,25,35],[]),([23,70,76],[15,6,4,2,10,30,13,28,23,34,25,35],[]),([23,70,78],[15,2,35,4,10,30,13,28],[]),([23,70,326],[15,4,13,28],[]),([23,70,334],[15,4,6,9,28],[]),([23,70,583],[0,15,4],[]),([23,74,42],[0,7,2,15,4,28,10,30,23,34,25,35,9],[107]),([23,74,60],[1,2,0,15,4,28,5,6,30,10,34,23,35],[]),([23,74,78],[15,1,4,9,28,10,30,23,34,25,35],[]),([23,74,298],[0,5,1,10,23,25,4,28],[108]),([23,74,316],[35,14,23,10,34,25,28],[107,109]),([23,74,583],[0,7,4,1,3,9,35,36],[108,109]),([23,75,72],[7,1,2,5,14,9,10],[110]),([23,75,94],[15,1,4,9,13],[]),([23,75,840],[0,1,2,15,4,28,10,30,23,34,25,36,14],[111,112,113]),([23,75,854],[15,1,9,14,36],[]),([23,78,34],[0,7,2,15,4,28,10,30,23,34,25,35,9],[]),([23,78,70],[0,15,1,4,3,28,10,30,23,34,25,35,9],[]),([23,78,71],[15,1,13],[]),([23,78,78],[15,1,6,28,10,30,23,34,25,35],[]),([23,78,290],[0,6,1,10,4,28],[114]),([23,78,298],[0,6,1,23,25,4,28],[115]),([23,78,583],[0,4,3,9],[114]),([23,79,86],[15,1,3,13,4],[]),([23,79,840],[0,1,2,15,4,28,10,30,23,34,25,35,14],[116,117,118]),([23,79,854],[15,1,14,9],[]),([23,102,42],[0,2,7,15,4,23,28,10,34,32,35],[]),([23,102,72],[15,30,7,2,23,28,10,34,32,35],[]),([23,102,76],[15,30,4,2,13,23,28,10,34,32,35],[]),([23,102,78],[15,2,30,4,13,28],[]),([23,102,583],[0,15,4],[]),([23,110,70],[0,15,1,30,4,3,23,28,10,34,32,35,36],[]),([23,110,583],[0,4,3,30],[]),([23,111,86],[15,30,1,13,4],[]),([23,111,840],[0,1,30,15,4,23,28,10,34,32,35],[119,120,121]),([23,111,854],[15,1,14],[]),([23,118,42],[0,2,7,15,4,25,28,10,30,32,35],[])]
set_option maxRecDepth 100000 in
theorem v189_9_2 : ∀ e ∈ k189_9_2, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_2 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_3 : List Entry := [([23,118,72],[15,34,7,2,25,28,10,30,32,35],[]),([23,118,76],[15,34,4,2,13,25,28,10,30,32,35],[]),([23,118,78],[15,2,34,4,13,28],[]),([23,118,583],[0,15,4],[]),([23,126,70],[0,15,1,34,4,3,25,28,10,30,32,35,36],[]),([23,126,583],[0,4,3,34],[]),([23,127,86],[15,34,1,13,4],[]),([23,127,840],[0,1,34,15,4,25,28,10,30,32,35],[122,123,124]),([23,127,854],[15,1,14],[]),([23,296,30],[0,15,4,1,2,14,28,10,30,34],[88,25,89,111,116,119,122,125,126,127,128,129]),([23,296,44],[15,3,4,14,28,10,30,34,35],[66,88,112,117,120,123,130,131,132,133,134]),([23,296,46],[0,15,4,13,28,10,30,34,35],[113,118,121,124,135,136,137,138,139]),([23,296,855],[0,30,5,14,15,4,28,10,34,25,35],[140,35,125,130,135,67,90]),([23,296,863],[0,30,5,14,6,15,4,28,10,34,25,35,23],[141,142,143,36,126,131,136,68,91]),([23,296,871],[0,34,5,14,15,4,28,10,30,23,35],[144,37,127,132,137,69,92]),([23,296,879],[0,34,5,14,6,15,4,28,10,30,23,35,25],[145,146,147,38,128,133,138,70,93]),([23,296,1391],[0,34,30,14,31,23,28],[39,129,134,139,71,94]),([23,310,56],[7,15,4,1,9,13,28,10,30,34,35],[148,149,150,151,152,153]),([23,310,316],[7,4,15,10,2,14,28,30,34],[148,154,155,156,157,158,159]),([23,310,846],[15,7,9,13,10,28],[160]),([23,310,1127],[15,9,30],[161,149,155]),([23,310,1135],[15,30],[162,163,150,156]),([23,310,1143],[15,9,34],[164,151,157]),([23,310,1151],[15,34],[165,166,152,158]),([23,310,1663],[15,30],[153,159]),([23,311,338],[0,15,4,9,3],[167,114,168]),([23,311,342],[0,15,4,9,3],[169,108,170]),([23,311,374],[0,15,4,30,9,3],[171]),([23,311,390],[0,15,4,34,9,3],[172]),([23,311,1118],[3,2,4,15],[168,170,109]),([23,318,312],[0,7,1,28,10,30,34,35],[173,174,175,176,177]),([23,318,1127],[0,9,14,30,15],[173]),([23,318,1135],[0,30,15],[178,179,174]),([23,318,1143],[0,9,14,34,15],[175]),([23,318,1151],[0,34,15],[180,181,176]),([23,318,1663],[0,30,15],[177]),([23,323,72],[7,0,2,1,4,6,9,10,23,25],[]),([23,323,76],[2,0,7,4,10,23,25,28],[167]),([23,323,588],[0,1,2,4,6,7,10,23,25,28],[168]),([23,327,72],[7,0,1,4,5,9,10,23,25],[]),([23,327,76],[2,0,4,10,5,28],[169,115]),([23,327,588],[7,0,2,4,6,10,23,25,28],[107,170]),([23,359,72],[7,0,1,4,23,9,10,32],[]),([23,359,76],[30,0,4,23,7,10,1,28],[171]),([23,375,72],[7,0,1,4,25,9,10,32],[]),([23,375,76],[34,0,4,25,7,10,1,28],[172]),([23,566,78],[7,15,1,13,4,10],[]),([23,566,1127],[7,15,4,30],[182,173]),([23,566,1135],[7,30,15],[183,184,174]),([23,566,1143],[7,15,4,34],[185,175])]
set_option maxRecDepth 100000 in
theorem v189_9_3 : ∀ e ∈ k189_9_3, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_3 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_4 : List Entry := [([23,566,1151],[7,34,15],[186,187,176]),([23,566,1663],[7,30,15],[177]),([23,574,52],[0,15,9,1,4,2,28,10,30,34,35],[148,188,189,190,191,192]),([23,574,70],[15,2,14,4,10,28],[154]),([23,574,1127],[15,4,30],[193,188,155]),([23,574,1135],[15,30],[194,195,189,156]),([23,574,1143],[15,4,34],[196,190,157]),([23,574,1151],[15,34],[197,198,191,158]),([23,574,1663],[15,30],[192,159]),([23,582,46],[7,5,9,1,10],[]),([23,582,78],[7,15,4,9,10],[]),([23,590,52],[0,14,15,4,28,5,6,30,10,34,23],[199,200]),([23,590,70],[15,2,7,4,3,9,10,28],[]),([23,590,326],[15,4,8,13,10,23,25,28],[]),([23,590,334],[15,4,13,10,9,23,25,28],[201]),([23,843,56],[15,4,23,9,28,10,34,13,25,35],[]),([23,843,60],[15,1,13,4,28,10,30,23,34,25,35],[]),([23,843,62],[15,4,13],[]),([23,843,88],[7,15,13,4,5,28,23,25,35,10],[]),([23,843,92],[15,7,4,9,5,28,13,23,25,35,10],[]),([23,847,48],[15,4,23,9,28,10,30,34,13,25,35],[]),([23,847,52],[15,1,13,7,0,4,28,10,30,23,25,34,35,36,9,6],[201]),([23,847,54],[0,15,4,35,36,13,7,9],[]),([23,879,48],[15,30,9,4,13,23,28,10,34,32,35],[]),([23,879,52],[15,30,7,0,4,23,28,10,34,32,35,36],[]),([23,879,54],[0,15,4,30,13],[]),([23,895,48],[15,34,9,4,13,25,28,10,30,32,35],[]),([23,895,52],[15,34,7,0,4,25,28,10,30,32,35,36],[]),([23,895,54],[0,15,4,34,13],[]),([23,1127,56],[30,23,14,15,28,10,34,25],[202,203,204,205]),([23,1127,60],[30,14,23,7,15,28,10,34,25,35,36],[206,207]),([23,1127,62],[30,5,23,1],[140]),([23,1127,74],[0,23,7,5],[58,77]),([23,1127,88],[7,14,5,30,1,25,9,10],[208]),([23,1127,92],[7,30,5,23,14,25,10,28],[209,210,161]),([23,1127,110],[15,4,9],[211,212]),([23,1135,48],[30,22,6,15,28,10,34,25,35,36],[213,214,215,216]),([23,1135,52],[30,14,7,0,23,15,22,28,10,34,25,35,36],[217]),([23,1135,54],[0,30,6,1],[141]),([23,1135,66],[0,22,6],[59,79]),([23,1135,102],[15,4],[218,219]),([23,1135,128],[34,30,22,23,7,0,15,28,10,35,36],[52,60,72,80,95,101,142,162,178,183,194]),([23,1135,132],[22,7,0,15,28,10,35,36],[53,61,73,81,96,102,143,163,179,184,195]),([23,1143,56],[34,23,14,15,28,10],[220,221,222,223]),([23,1143,60],[34,14,23,7,15,28,10,35,36],[224,225]),([23,1143,62],[34,5,23,1],[144]),([23,1143,74],[0,23,7,5],[62,83]),([23,1143,88],[7,14,5,34,1,23,9,10],[226]),([23,1143,92],[7,34,5,23,14,10,28],[227,228,164]),([23,1143,110],[15,4,9],[229,230])]
set_option maxRecDepth 100000 in
theorem v189_9_4 : ∀ e ∈ k189_9_4, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_4 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_5 : List Entry := [([23,1151,48],[34,23,14,15,28,10,30,6],[231,232,233,234]),([23,1151,52],[34,14,7,0,25,15,24,28,10,30,23,35,36],[235]),([23,1151,54],[0,34,6,1],[145]),([23,1151,66],[0,24,6],[63,85]),([23,1151,102],[15,4],[236,237]),([23,1151,128],[30,34,22,6,25,7,15,28,10,35,36],[56,64,74,86,97,105,146,165,180,186,197]),([23,1151,132],[23,34,7,0,15,28,10,35,36],[57,65,75,87,98,106,147,166,181,187,198]),([27,60,855],[0,30,5,3,4,7,28,10,34,25,35],[130]),([27,60,863],[0,30,5,3,4,7,28,10,6,34,25,35,23],[238,239,131]),([27,60,871],[0,34,5,3,4,7,28,10,30,23,35],[132]),([27,60,879],[0,34,5,3,4,7,28,10,6,30,23,35,25],[240,241,133]),([27,60,1391],[0,34,30,3,4,7,23,28,10,35],[134]),([27,62,1127],[0,3,4,30],[135]),([27,62,1135],[0,3,4,30],[242,243,136]),([27,62,1143],[0,3,4,34],[137]),([27,62,1151],[0,3,4,34],[244,245,138]),([27,62,1663],[0,3,4,30],[139]),([27,76,87],[0,30,5,7,15,4,28,10,34,25,35],[]),([27,76,95],[0,30,5,7,15,4,28,10,6,34,32,35,23],[246,247]),([27,76,103],[0,34,5,7,15,4,28,10,30,23,35],[]),([27,76,111],[0,34,5,7,15,4,28,10,6,30,32,35],[248,249]),([27,76,1391],[0,34,30,31,23,25,7,28],[]),([27,78,358],[0,5,30,7,15,4,28,10,34,25,35],[]),([27,78,366],[0,5,30,7,15,4,28,10,6,34,25,35],[250,251]),([27,78,374],[0,5,34,7,15,4,28,10,30,23,35],[]),([27,78,382],[0,5,34,7,15,4,28,10,6,30,23,35],[252,253]),([27,92,1111],[0,30,5,10,15,4,34,25,35],[]),([27,92,1119],[0,30,5,10,15,4,6,34,25,35,23],[254,255]),([27,92,1127],[0,34,5,10,15,4,30,23,35],[]),([27,92,1135],[0,34,5,10,15,4,6,30,23,35,25],[256,257]),([27,92,1391],[0,34,30,10,15,4,23,35],[]),([27,108,1135],[0,34,5,6,23,7,15,4,28,10,35],[258]),([27,124,1135],[0,30,5,6,25,7,15,4,28,10,35],[259]),([27,1127,60],[0,30,5,7,15,4,28,10,34,25,35],[]),([27,1135,52],[0,30,5,7,15,4,28,10,22,34,6,23],[]),([27,1135,128],[34,0,30,5,22,23,7,36,10,35],[260,250,238,242,254,142]),([27,1135,132],[0,22,23,7,36,10,35],[251,239,243,255,143]),([27,1143,60],[0,34,5,7,15,4,28,10,30,23,35],[]),([27,1151,52],[0,34,5,7,15,4,28,10,24,30,6,23],[]),([27,1151,128],[30,0,34,5,24,25,7,36,10,35],[261,252,240,244,256,146]),([27,1151,132],[0,23,25,7,36,10,35],[253,241,245,257,147]),([31,54,1127],[0,4,3,30],[]),([31,54,1135],[0,4,3,30],[262,263]),([31,54,1143],[0,4,3,34],[]),([31,54,1151],[0,4,3,34],[264,265]),([31,54,1663],[0,4,3,30],[]),([31,310,1127],[0,15,4,30],[]),([31,310,1135],[0,30],[266,267]),([31,310,1143],[0,15,4,34],[]),([31,310,1151],[0,34],[268,269])]
set_option maxRecDepth 100000 in
theorem v189_9_5 : ∀ e ∈ k189_9_5, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_5 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_6 : List Entry := [([31,310,1663],[0,30],[]),([31,1127,56],[30,0,7,14,15,4,28,10,34,25,35,36],[]),([31,1135,48],[0,30,7,14,15,4,28,10,34,22,6,35,36],[]),([31,1135,128],[34,30,5,6,23,15,28,10,35,36],[12,262,40,266]),([31,1135,132],[22,0,15,28,10,35,36],[13,263,41,267]),([31,1143,56],[34,0,7,14,15,4,28,10,30,23,35,36],[]),([31,1151,48],[0,34,7,14,15,4,28,10,30,23,35,36],[]),([31,1151,128],[30,34,5,6,25,15,28,10,35,36],[16,264,42,268]),([31,1151,132],[23,34,0,15,28,10,35,36],[17,265,43,269]),([39,50,74],[7,4,15,28,10,30,23,34,25,35],[]),([39,50,78],[7,4,28,10,30,23,34,25,35],[]),([39,50,110],[7,30,4,23,28,10,34,32,35],[]),([39,50,126],[7,34,4,25,28,10,30,32,35],[]),([39,50,1127],[7,23,15,4,30,35,36],[270]),([39,50,1135],[7,23,30,35,36],[271,272,273]),([39,50,1143],[7,23,15,4,34,35,36],[274]),([39,50,1151],[7,25,34,35,36],[275,276,277]),([39,50,1663],[7,31,23,30,35,36],[]),([39,58,60],[7,0,3,28,10,30,34,35],[148,278,279,280,281,282]),([39,58,72],[7,3,9,28,10,30,23,34,25,35],[]),([39,58,74],[7,3,9,28,10,30,23,34,25,35],[]),([39,58,76],[7,3,28,10,30,34,35],[283,284,285,286,287]),([39,58,78],[7,3,28,10,30,23,25,34,35],[288,289,290,291]),([39,58,92],[7,28,3,10,36,9,30,34],[292,293,294,295,296]),([39,58,104],[7,30,15,3,28,10,34,25,35],[]),([39,58,108],[7,3,23,28,10,34,33,35,9],[297]),([39,58,110],[7,3,23,28,10,34,32,35,30],[]),([39,58,120],[7,34,15,3,28,10,30,23,35],[]),([39,58,124],[7,3,25,28,10,30,32,35,9],[298]),([39,58,126],[7,3,25,28,10,30,32,35],[]),([39,58,316],[7,4,15,28,10,30,34,35],[299,300,301,302,303]),([39,58,1127],[7,23,15,9,30,36,25,35],[304,288,278,292,149,299]),([39,58,1135],[7,23,30,15,36,35],[305,306,307,289,279,293,298,150,300]),([39,58,1143],[7,23,15,9,34,25,36,35],[308,290,280,294,151,301]),([39,58,1151],[7,25,34,15,36,35],[309,310,311,291,281,295,297,152,302]),([39,58,1663],[7,31,23,30,25,15,36,35],[282,287,296,153,303]),([39,62,1127],[15,9,3,30,36],[]),([39,62,1135],[15,9,3,30,36],[312,313]),([39,62,1143],[15,9,3,34,36],[]),([39,62,1151],[15,9,3,34,36],[314,315]),([39,62,1663],[15,9,3,30,36],[]),([39,74,60],[15,3,5,6,28,9,30,21,34,23,35],[]),([39,74,78],[15,3,5,7,9,28,10,30,23,34,25,35],[]),([39,74,316],[15,4,3,28,9,30,21,34,23,35],[]),([39,78,70],[0,15,3,9,28,10,30,23,34,25,35,6],[]),([39,110,70],[0,15,3,30,23,28,10,34,32,35,36],[]),([39,126,70],[0,15,3,34,25,28,10,30,32,35,36],[]),([39,323,94],[0,4,3],[167]),([39,323,606],[0,3,2,9],[168]),([39,327,94],[0,4,3],[169])]
set_option maxRecDepth 100000 in
theorem v189_9_6 : ∀ e ∈ k189_9_6, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_6 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_7 : List Entry := [([39,327,598],[0,2,3,4],[]),([39,327,606],[0,3,2,9],[170]),([39,359,94],[0,30,3,2],[171]),([39,375,94],[0,34,3,2],[172]),([39,574,52],[0,15,3,7,2,28,10,30,34,35],[316,317,318,319,320]),([39,574,70],[15,2,3,7,4,8,10,28],[154]),([39,574,1127],[15,4,30],[321,278,316,299,155]),([39,574,1135],[15,30],[322,323,279,317,300,156]),([39,574,1143],[15,4,34],[324,280,318,301,157]),([39,574,1151],[15,34],[325,326,281,319,302,158]),([39,574,1663],[15,30],[282,320,303,159]),([39,590,52],[0,3,9,28,5,6,30,21,34,23,35],[327]),([39,843,60],[7,2,9,15,28,10,30,23,34,25,35,3],[]),([39,843,74],[0,15,2,4],[]),([39,847,52],[7,2,3,4,9,28,10,30,23,34,25,35,15],[160]),([39,847,53],[15,4,6,9,13],[]),([39,847,60],[15,2,6,28,10,30,23,34,25,35],[]),([39,847,66],[0,15,2,4],[]),([39,879,52],[7,30,9,15,0,3,23,28,10,34,32,35],[]),([39,879,66],[0,15,2],[]),([39,895,52],[7,34,9,15,0,3,25,28,10,30,32,35],[]),([39,895,66],[0,15,2],[]),([39,1127,56],[30,3,4,9,28,21,34,25,35],[]),([39,1127,60],[30,4,15,9,3,28,21,34,25,35,36],[328]),([39,1127,74],[0,15,4],[]),([39,1127,92],[15,4,23,9,21,25],[329]),([39,1127,110],[15,9],[330,331,161]),([39,1135,48],[30,3,4,9,28,21,34,25,35,15],[]),([39,1135,52],[30,4,15,3,9,28,21,34,25,35,6,36],[332]),([39,1135,66],[0,15,4],[]),([39,1135,102],[15,9,22],[333]),([39,1135,128],[34,30,22,23,15,0,28,29,36],[272,52,306,312,162,266,322]),([39,1135,132],[22,15,0,28,29,36],[273,53,307,313,163,267,323]),([39,1143,56],[34,3,4,9,28,21,30,23,35],[]),([39,1143,60],[34,4,15,9,3,28,21,30,23,35,36],[334]),([39,1143,74],[0,15,4],[]),([39,1143,92],[15,4,23,9,34,21],[335]),([39,1143,110],[15,9],[336,337,164]),([39,1151,48],[34,3,4,9,28,21,30,23,35,15],[]),([39,1151,52],[34,4,15,3,9,28,21,30,23,35,6,36],[338]),([39,1151,66],[0,15,4],[]),([39,1151,102],[15,9,24],[339]),([39,1151,128],[30,34,22,6,25,15,28,29,36],[276,56,310,314,165,268,325]),([39,1151,132],[23,34,15,0,28,29,36],[277,57,311,315,166,269,326]),([47,50,74],[0,7,2,15,9,28,10,30,23,34,25,35],[]),([47,50,78],[0,7,15,28,10,30,23,34,25,35],[]),([47,50,110],[0,7,15,23,28,10,34,32,35],[]),([47,50,126],[0,7,15,25,28,10,30,32,35],[]),([47,50,334],[0,7,2,15,10],[]),([47,50,1127],[0,7,5,30,35,36],[340,341])]
set_option maxRecDepth 100000 in
theorem v189_9_7 : ∀ e ∈ k189_9_7, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_7 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_8 : List Entry := [([47,50,1135],[0,7,6,30,35,36],[342,343,344]),([47,50,1143],[0,7,5,34,35,36],[345,346]),([47,50,1151],[0,7,6,34,35,36],[347,348,349]),([47,50,1663],[0,7,31,23,30,35,36],[]),([47,54,308],[0,7,1,28,10,30,34,35],[350,351,352,353,354]),([47,54,1127],[0,5,14,9,30],[5,350]),([47,54,1135],[0,14,9,30],[355,356,6,351]),([47,54,1143],[0,5,14,9,34],[7,352]),([47,54,1151],[0,14,9,34],[357,358,8,353]),([47,54,1663],[0,14,9,30],[9,354]),([47,66,78],[0,2,7,15,28,10,30,23,34,25,35],[]),([47,66,334],[0,2,1,15,9,10,28],[]),([47,70,70],[0,2,1,15,9,28,10,30,23,34,25,35],[]),([47,70,78],[0,2,7,15,28,10,30,23,34,25,35,5],[]),([47,70,326],[0,2,1,9,10,28],[]),([47,70,334],[0,2,9,6,10,28],[]),([47,70,842],[0,7,10],[]),([47,102,78],[0,2,7,15,23,28,10,34,32,35],[]),([47,118,78],[0,2,7,15,25,28,10,30,32,35],[]),([47,570,56],[7,1,28,10,30,34,35],[359,360,361,362,363]),([47,570,1127],[0,30],[364,5,359,350,173]),([47,570,1135],[0,30],[365,366,6,360,351,174]),([47,570,1143],[0,34],[367,7,361,352,175]),([47,570,1151],[0,34],[368,369,8,362,353,176]),([47,570,1663],[0,30],[9,363,354,177]),([47,843,56],[0,2,7,15,28,10,30,23,34,25,35],[]),([47,847,48],[0,2,7,15,28,10,30,23,34,25,35],[]),([47,879,48],[0,30,15,23,28,10,34,32,35,2],[]),([47,895,48],[0,34,15,25,28,10,30,32,35,2],[]),([47,1127,56],[30,0,15,9,5,28,21,34,25,35,29,36],[370,364]),([47,1127,110],[0,14,15,9],[371,341]),([47,1135,48],[0,30,15,9,22,6,35,36],[]),([47,1135,102],[0,14,15,9,30,23],[372]),([47,1135,128],[34,30,5,6,23,15,28,29,36],[343,355,178,365]),([47,1135,132],[22,0,15,28,29,36],[344,356,179,366]),([47,1143,56],[34,0,15,9,5,28,21,30,23,35,29,36],[373,367]),([47,1143,110],[0,14,15,9],[374,346]),([47,1151,48],[0,34,15,9,24,6,35,36],[]),([47,1151,102],[0,14,15,9,34,25],[375]),([47,1151,128],[30,34,5,6,25,15,28,29,36],[348,357,180,368]),([47,1151,132],[23,34,0,15,28,29,36],[349,358,181,369]),([51,26,50],[0,7,2,15,4,28,10,30,23,34,25,35,36],[]),([51,26,58],[0,7,2,15,4,28,10,30,23,25,35,36],[376]),([51,26,62],[0,2,7,15,4,28,10,30,23,34,25,35],[]),([51,26,574],[0,2,4,5,23,25,6,10,28],[376]),([51,58,78],[7,4,3,6,28,8],[]),([51,62,70],[0,15,2,4,3,6,10,30,23,34,25,35,28],[]),([51,62,71],[15,2,4],[]),([51,62,78],[15,2,6,28,10,30,23,34,25,35],[377]),([51,62,846],[15,4,6,9,23,25,28],[])]
set_option maxRecDepth 100000 in
theorem v189_9_8 : ∀ e ∈ k189_9_8, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_8 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_9 : List Entry := [([51,78,66],[7,15,4,22,28,10,23,25,35,36],[378]),([51,78,70],[0,15,4,9,28,10,30,23,34,25,35],[]),([51,78,846],[15,6,9,23,25,10,28],[378]),([51,300,20],[15,4,28,29,30,23,34,25,36],[379,380,381,382]),([51,574,37],[35,1,2,22,10,28],[383]),([51,574,70],[15,2,4,23,28],[]),([51,574,71],[15,4,9],[]),([51,574,78],[15,2,6,4,28],[384]),([51,590,70],[15,4,3,6,35,36,23],[]),([51,839,60],[7,15,4,28,10,30,23,34,25,35],[]),([51,839,92],[7,15,1,4,23,10],[]),([51,847,52],[7,15,4,28,8,10,30,23,34,25,35],[]),([51,847,64],[8,4,23,25,28],[]),([51,847,68],[0,23,7,2,15,4,25,28],[385]),([55,50,78],[7,15,4,28,8],[]),([55,51,56],[5,7,0,1,23,25,6,9,10],[]),([55,51,94],[7,15,4],[]),([55,51,300],[7,5,23,25,6,28],[386,387]),([55,51,840],[0,7,6,15,4,28,10,30,23,34,25,35,36],[388,389,387]),([55,55,56],[5,2,0,23,25,35,15,6,28],[390,391]),([55,55,88],[7,15,2,6,28,10,30,23,34,25,35],[392]),([55,55,92],[6,15,4,7,2,35,28,10,30,23,34,25],[393]),([55,55,94],[15,35,7,4],[]),([55,55,296],[7,6,23,25,5,28],[386,394]),([55,55,300],[35,7,2,5,6,28],[390,115]),([55,55,350],[15,8,4],[]),([55,55,840],[0,2,6,15,4,28,10,30,23,34,25,35],[395,396,392,393,394]),([55,55,1110],[15,4,5],[397,391]),([55,58,60],[7,0,15,4,28,5,6,30,10,34,23,35],[]),([55,58,62],[0,7,15,4,28,5,6],[]),([55,58,78],[7,4,5,3,28,8],[]),([55,58,316],[7,2,15,9,28,10,30,23,34,25,35],[398,107]),([55,58,318],[7,6,15,5,23,25,28],[]),([55,59,72],[7,1,2,9,5,10,23,25],[399]),([55,59,76],[0,7,5,4,15,28,6,23,25],[]),([55,59,94],[7,15,4],[]),([55,59,588],[7,6,23,25,15,5,28],[]),([55,59,840],[0,5,7,15,4,28,10,30,23,25,35,36],[400,394]),([55,62,54],[0,7,15,4,28,6,5],[]),([55,62,70],[0,15,2,4,5,3,10,30,23,34,25,35,28],[]),([55,62,71],[15,2,4],[]),([55,62,78],[15,2,5,28,10,30,23,34,25,35],[]),([55,62,310],[7,2,5,6,23,25,28],[]),([55,62,318],[35,7,2,5,6,23,25,28],[390]),([55,62,838],[15,4,5,9,28],[]),([55,62,846],[15,4,6,35,36],[]),([55,62,847],[15,8,5,4,6],[]),([55,63,86],[15,7,5,3,4],[]),([55,63,342],[15,8,4,6],[]),([55,63,588],[7,2,23,25,6,5,28],[])]
set_option maxRecDepth 100000 in
theorem v189_9_9 : ∀ e ∈ k189_9_9, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_9 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_10 : List Entry := [([55,63,840],[0,5,2,15,4,28,10,30,23,34,25,35],[401,387]),([55,63,1118],[5,15,4,6],[]),([55,71,56],[15,0,23,25,4,6,9,21,16,35,36],[]),([55,71,90],[15,6,35,36,4],[402,403]),([55,71,94],[15,7,3,6,36,4],[403]),([55,71,1110],[15,4,16],[404]),([55,78,66],[7,15,4,28,10,30,23,34,25,35,36],[405]),([55,78,70],[0,15,4,9,28,10,30,23,34,25,35],[]),([55,78,838],[15,5,9,10,28],[]),([55,78,846],[15,5,8,4,9,23,25,10,28],[]),([55,78,847],[15,8,4,6,5],[]),([55,79,82],[15,35,36,7,5,4],[406,407,408]),([55,79,86],[15,7,4,9,5],[]),([55,79,1118],[4,5,15],[]),([55,296,30],[0,6,5,15,4,28,29,30,23,34,25,36],[389,396,400,401]),([55,566,46],[35,1,2,22,23,25,28],[409]),([55,566,76],[7,2,15,5,4,10,30,23,34,25,35,28],[]),([55,566,78],[15,2,35,4,16,23,25,28],[]),([55,566,582],[15,4,23,7,10,6,35,36],[]),([55,571,76],[5,0,23,25,7,4,6,28],[]),([55,571,94],[7,15,4,6,3],[]),([55,574,37],[0,7,2,4,10,15,30,23,34,25,35],[]),([55,574,49],[35,0,2,6,23,25,28],[410]),([55,574,52],[0,7,2,15,4,28,6,5,30,10,34,23,35],[411]),([55,574,53],[0,2,6,23,25,15,4,28,10,30,34,35],[412,413]),([55,574,70],[15,2,4,3,23,25,28],[]),([55,574,71],[15,7,4,9],[410]),([55,574,78],[15,2,6,4,23,25,28],[414,415]),([55,574,582],[15,4,6,7,10,9,23,25,28],[416,417]),([55,575,68],[0,5,23,25,7,2,15,4,28,6],[]),([55,575,86],[15,7,4,6,3,23],[]),([55,582,78],[15,4,5,28,9,23,25,36],[]),([55,590,52],[0,15,4,6,5,28,9,21,30,23,34,25,35,36],[418]),([55,590,70],[15,4,9,16,23,25,28],[]),([55,591,68],[0,5,23,25,15,6,4,35,36],[]),([55,591,82],[15,23,35,36,6,4],[]),([55,591,86],[15,4,9,6,16],[]),([55,839,56],[7,15,4,28,10,30,23,34,25,35],[419]),([55,839,58],[7,4,15],[420]),([55,839,60],[7,15,4,28,10,30,23,34,25,35],[]),([55,839,62],[7,0,4],[]),([55,839,88],[7,15,4,16,10,23,25],[]),([55,839,92],[7,15,0,4,23,10,25],[421]),([55,839,94],[7,0,4,23,15],[420]),([55,847,48],[7,15,8,4,28,10,30,23,34,25,35],[]),([55,847,50],[15,2,23,4],[422]),([55,847,52],[7,15,4,28,8,10,30,23,34,25,35],[]),([55,847,54],[0,15,2,4,23],[]),([55,847,86],[15,2,4],[422]),([63,50,318],[0,7,2,4,10],[])]
set_option maxRecDepth 100000 in
theorem v189_9_10 : ∀ e ∈ k189_9_10, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_10 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_11 : List Entry := [([63,54,72],[0,15,7,1,28,10,30,23,34,25,35],[]),([63,54,76],[7,0,1,28,10,30,23,34,25,35],[]),([63,54,310],[0,7,2,1,4,23,25,28],[]),([63,54,318],[0,7,2,4,10,23,25,28],[]),([63,70,847],[0,4,3,9],[]),([63,571,72],[0,1,23,25,9,10],[]),([63,575,64],[0,7,2,23,25,4,6,15,28],[]),([87,58,78],[7,4,30,8,28],[]),([87,62,70],[0,15,2,4,30,23,10,34,32,35,28],[]),([87,62,71],[15,2],[]),([87,62,78],[15,2,30,23,28,10,34,32,35],[]),([87,78,66],[7,15,4,30,23,28,10,32,35,36],[]),([87,78,70],[0,15,4,30,23,28,10,34,32,35,36],[]),([87,839,60],[7,15,30,23,28,10,34,32,35,4],[]),([87,847,52],[7,15,30,0,4,8,23,28,10,34,32,35],[]),([87,847,64],[30,2,8,4,23,32,28],[]),([87,847,68],[0,23,30,32,7,2,15,4,28],[423,424]),([103,58,78],[7,4,34,8,28],[]),([103,62,70],[0,15,2,4,34,25,10,30,32,35,28],[]),([103,62,71],[15,2],[]),([103,62,78],[15,2,34,25,28,10,30,32,35],[]),([103,78,66],[7,15,4,34,25,28,10,32,35,36],[]),([103,78,70],[0,15,4,34,25,28,10,30,32,35,36],[]),([103,839,60],[7,15,34,25,28,10,30,32,35,4],[]),([103,847,52],[7,15,34,0,4,8,25,28,10,30,32,35],[]),([103,847,64],[34,2,8,4,25,32,28],[]),([103,847,68],[0,25,34,32,7,2,15,4,28],[425,426]),([295,58,66],[7,1,13,4,28,10,30,23,34,25,35],[]),([295,58,102],[0,7,1,13,4,23,28,10,34,32,35],[]),([295,58,118],[0,7,1,13,4,25,28,10,30,32,35],[]),([295,58,1127],[7,23,4,15,30],[427,5,359]),([295,58,1135],[7,4,23,30],[428,429,430,6,360]),([295,58,1143],[7,23,4,15,34],[431,7,361]),([295,58,1151],[7,4,25,34],[432,433,434,8,362]),([295,58,1663],[7,31,23,30],[9,363]),([295,62,66],[0,7,15,28,10,30,23,34,25,35],[]),([295,62,102],[0,7,15,23,28,10,34,32,35],[]),([295,62,118],[0,7,15,25,28,10,30,32,35],[]),([295,62,1127],[0,23,30,7],[435]),([295,62,1135],[0,23,30,7],[436,437,438]),([295,62,1143],[0,23,34,7],[439]),([295,62,1151],[0,25,34,7],[440,441,442]),([295,62,1663],[0,31,23,30,7],[]),([295,74,60],[7,15,4,28,10,30,16,22,34,23,35],[]),([295,74,74],[7,13,0,15,28,10,30,23,34,25,35,4],[]),([295,74,316],[7,4,8,28,10,30,13,22,34,23,35],[]),([295,78,66],[7,13,0,15,28,10,30,23,34,25,35,4],[420]),([295,78,67],[7,0,13],[421]),([295,110,66],[7,13,0,15,23,28,10,34,32,35],[]),([295,126,66],[7,13,0,15,25,28,10,30,32,35],[])]
set_option maxRecDepth 100000 in
theorem v189_9_11 : ∀ e ∈ k189_9_11, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_11 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_12 : List Entry := [([295,590,52],[7,15,9,4,28,10,30,16,23,34,25,35],[]),([295,1127,60],[7,30,15,4,28,10,34,25,35],[443,427,182]),([295,1127,92],[15,7,23,4,10,25],[444]),([295,1127,106],[7,15,4,35,36],[427,445]),([295,1135,52],[7,30,15,22,4,28,10,34,25,35,23],[446]),([295,1135,98],[7,22,15,4,35,36],[447]),([295,1135,128],[34,30,22,23,7,15,28,10,35,36],[429,437,183,365]),([295,1135,132],[7,22,15,28,10,35,36],[430,438,184,366]),([295,1143,60],[7,34,15,4,28,10,30,23,35],[448,431,185]),([295,1143,92],[15,7,23,4,34,10],[449]),([295,1143,106],[7,15,4,35,36],[431,450]),([295,1151,52],[7,34,15,24,4,28,10,30,23,35,25],[451]),([295,1151,98],[7,24,15,4,35,36],[452]),([295,1151,128],[30,34,22,7,24,25,15,28,10,35,36],[433,441,186,368]),([295,1151,132],[7,23,34,15,28,10,35,36],[434,442,187,369]),([303,50,1127],[15,8,4,23,30],[]),([303,50,1135],[15,8,4,30,23],[453,454,455]),([303,50,1143],[15,8,4,23,34],[]),([303,50,1151],[15,8,4,34,25],[456,457,458]),([303,50,1663],[15,8,4,23,30],[]),([303,54,72],[0,7,2,15,28,10,30,23,34,25,35],[]),([303,54,74],[0,7,2,15,28,10,30,23,34,25,35],[]),([303,54,76],[0,7,2,15,28,10,30,34,35],[385,459,460,461,462,423,425,463]),([303,54,78],[0,23,7,2,15,28,10,30,25,34,35],[385,464,465,466,467]),([303,54,92],[0,7,2,15,10,30,34,35],[468,469,470,471,472]),([303,54,104],[0,30,7,15,2,28,10,34,25,35],[]),([303,54,108],[0,7,2,15,23,28,10,34,33,35],[426,473]),([303,54,110],[0,7,2,15,23,28,10,34,32,35,30],[]),([303,54,120],[0,34,7,15,2,28,10,30,23,35],[]),([303,54,124],[0,7,2,15,25,28,10,30,32,35],[424,474]),([303,54,126],[0,7,2,15,25,28,10,30,32,35],[]),([303,54,1127],[0,23,30,15,36,25,35],[475,464,278,468,188,316]),([303,54,1135],[0,23,30,15,36,35],[476,477,478,479,465,279,469,474,189,317]),([303,54,1143],[0,23,34,25,15,36,35],[480,466,280,470,190,318]),([303,54,1151],[0,25,34,15,36,35],[481,482,483,484,467,281,471,473,191,319]),([303,54,1663],[0,31,23,30,25,15,36,35],[282,463,472,192,320]),([303,62,66],[0,7,2,15,28,10,30,23,34,25,35],[]),([303,62,70],[0,7,2,15,28,10,30,23,34,25,35],[]),([303,62,102],[0,7,2,15,23,28,10,34,32,35],[]),([303,62,118],[0,7,2,15,25,28,10,30,32,35],[]),([303,62,1127],[0,23,30],[485]),([303,62,1135],[0,23,30],[486,487,488]),([303,62,1143],[0,23,34],[489]),([303,62,1151],[0,25,34],[490,491,492]),([303,62,1663],[0,31,23,30],[]),([303,66,74],[15,8,2,4,28,10,30,23,34,25,35],[]),([303,70,74],[15,8,4,28,10,30,23,34,25,35],[422]),([303,78,64],[4,7,2,28,10,30,23,34,25,35],[]),([303,78,68],[0,4,7,2,28,10,30,23,34,25,35],[]),([303,102,74],[15,8,30,23,28,10,34,32,35],[])]
set_option maxRecDepth 100000 in
theorem v189_9_12 : ∀ e ∈ k189_9_12, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_12 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_13 : List Entry := [([303,118,74],[15,8,34,25,28,10,30,32,35],[]),([303,1127,56],[30,4,7,15,8,28,10,34,25,35],[493,193,321]),([303,1127,60],[30,8,4,9,28,10,34,25,35],[494,495]),([303,1127,106],[15,4],[496,497]),([303,1135,48],[30,4,7,15,8,28,10,34,25,35],[498]),([303,1135,52],[30,8,4,9,28,10,34,25,35],[]),([303,1135,98],[15,22,4],[499,453,477]),([303,1135,128],[34,30,22,23,15,7,28,10,35,36],[454,478,52,487,44,194,322]),([303,1135,132],[22,15,7,28,10,35,36],[455,479,53,488,45,195,323]),([303,1143,56],[34,4,7,15,8,28,10,30,23,35],[500,196,324]),([303,1143,60],[34,8,4,9,28,10,30,23,35],[501,502]),([303,1143,106],[15,4],[503,504]),([303,1151,48],[34,4,7,15,8,28,10,30,23,35],[505]),([303,1151,52],[34,8,4,9,28,10,30,23,35],[]),([303,1151,98],[15,24,4],[506,456,482]),([303,1151,128],[30,34,22,24,25,15,7,28,10,35,36],[457,483,56,491,46,197,325]),([303,1151,132],[23,34,15,7,28,10,35,36],[458,484,57,492,47,198,326]),([307,58,572],[1,2,15,9,28,10,30,23,34,25,35],[507,508,509,510,511]),([307,300,20],[15,9,28,10,30,23,34,25,35],[512,513,514,515]),([307,300,21],[7,2,15,9,28,10,30,23,34,25,35,14],[507,516,517,518,519,520]),([307,300,35],[7,0,2,15,9,28,10,30,23,34,25,35,14],[507,519,510]),([307,300,39],[0,2,7,14,9,10,25,23,36],[509,521,520,511]),([311,46,54],[0,7,5,14,9,10,25,23,36],[522,523]),([315,58,70],[0,15,2,4,7,5,3,10,30,23,34,25,35,9,28],[]),([315,58,71],[15,13,2,4],[]),([315,58,78],[15,2,5,28,10,30,23,34,25,35],[]),([315,58,846],[15,4,13,23,25,28],[]),([315,62,70],[0,7,2,4,3,9,28],[]),([315,76,51],[35,0,4,7,2,5,15,10,30,13,9,28],[]),([315,78,66],[15,4,9,28,10,30,13],[]),([315,590,66],[15,4,8,10,16,6,35,36],[]),([319,50,70],[0,15,2,4,7,3,6,10,30,23,34,25,35,9,28],[]),([319,50,71],[15,13,2,4],[]),([319,50,78],[15,2,6,28,10,30,23,34,25,35],[]),([319,50,838],[15,4,13,28],[]),([319,50,846],[15,4,6,9,28],[]),([319,51,64],[0,1,6,7,4,10,2],[]),([319,51,86],[15,3,4,13,9],[]),([319,51,342],[15,0,13,2,4,9],[410]),([319,51,1110],[4,8,5,13],[524]),([319,54,72],[0,7,15,2,28,5,6,30,10,34,23,35],[]),([319,54,76],[15,0,7,2,3,4,14,28,5,6,30,10,34,23,35],[199]),([319,54,78],[0,15,7,2,3,4,9,28],[200]),([319,54,92],[0,7,2,5,6,4,15,30,10,34,23,35],[]),([319,54,104],[0,7,30,2,15,4,28,5,6,34,10,35],[]),([319,54,108],[0,7,2,5,6,15,4,28,10,23,34,35],[]),([319,54,120],[0,7,34,2,15,4,28,5,6,30,10,35],[]),([319,54,124],[0,7,2,5,6,15,4,28,10,23,30,35,25],[]),([319,55,92],[3,4,15,0,2,7,28,10,30,23,34,25,35,14],[521]),([319,55,94],[0,15,4,13,9],[])]
set_option maxRecDepth 100000 in
theorem v189_9_13 : ∀ e ∈ k189_9_13, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_13 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_14 : List Entry := [([319,55,108],[10,0,2,15,4,30,23,34,25,35,14],[]),([319,55,120],[30,0,2,7,15,4,28,10,34,25,35],[]),([319,55,124],[23,0,7,15,4,28,10,34,25,35,36],[412]),([319,55,136],[34,0,2,7,15,4,28,10,30,23,35],[]),([319,55,140],[25,0,7,15,4,28,10,30,23,35,36],[413]),([319,62,70],[0,7,2,15,4,3,28],[]),([319,70,74],[15,4,9,28,10,30,13],[]),([319,582,74],[15,4,8,10,23,25,35,36],[524]),([319,590,48],[7,15,6,28,10,30,23,34,25,35],[525,526]),([319,590,66],[15,4,9,10,6,23,25,28],[]),([319,591,64],[7,6,23,25,15,28],[]),([319,591,68],[15,7,9,6,13,10,28],[]),([351,50,70],[0,15,2,4,7,30,23,10,34,32,35,9,28],[]),([351,50,78],[15,2,30,23,28,10,34,32,35],[]),([351,54,78],[0,7,2,30,3,4,9,28],[]),([351,70,74],[15,4,9,13,10,28],[]),([367,50,70],[0,15,2,4,7,34,25,10,30,32,35,9,28],[]),([367,50,78],[15,2,34,25,28,10,30,32,35],[]),([367,54,78],[0,7,2,34,3,4,9,28],[]),([367,70,74],[15,4,9,13,10,28],[]),([571,62,70],[0,15,4,5,6,28,10,30,23,34,25,35,36],[]),([571,74,74],[7,15,1,5,23,28,10,34,25,35],[]),([575,54,72],[0,7,15,5,6,28,9,30,10,34,23,35],[]),([575,54,76],[9,0,15,4,5,6,28,21,30,23,34,25,35,36],[327]),([575,54,78],[0,7,15,1,5,6,28,10,30,23,34,25,35,36,9,4,21],[]),([575,54,92],[0,15,5,6,9,10,30,21,23,34,25,36],[]),([575,54,104],[0,15,30,5,6,28,9,21,34,25,35,36],[]),([575,54,108],[0,15,5,6,9,23,28,21,34,25,35,36],[]),([575,54,120],[0,15,34,5,6,28,9,21,30,23,35,36],[]),([575,54,124],[0,15,5,6,9,25,28,21,30,23,35,36],[]),([575,62,54],[0,15,6,5,4,35,36],[]),([575,66,74],[7,15,1,16,6,28,10,30,23,34,25,35],[526]),([575,74,62],[7,15,4,28,10,30,23,34,25,35],[]),([607,54,78],[0,15,1,30,23,28,10,34,32,35,36],[]),([607,66,74],[7,15,1,30,23,28,10,34,32,35],[]),([623,54,78],[0,15,1,34,25,28,10,30,32,35,36],[]),([623,66,74],[7,15,1,34,25,28,10,30,32,35],[]),([855,58,66],[7,30,23,15,28,10,34,25,35,36],[527,528]),([855,58,74],[7,30,5,15,28,10,34,25,35,36],[529,530]),([855,58,78],[30,5,26,15,28,10,34,25,35,36],[531]),([855,58,94],[15,4,5,30,28,29,34,25,36],[532,533]),([855,62,66],[0,7,5,6,30,15,4,28,10,34,25,35,36],[]),([855,62,70],[0,5,6,30,15,4,1,28,10,34,25,35,36],[534,535]),([855,62,86],[0,4,3,35,36],[]),([855,74,74],[7,5,23,15,9,28,10,34,25,35],[]),([855,74,78],[7,0,5,30,15,9,28,10,34,25,35],[]),([855,74,94],[7,8,9,28],[208]),([855,78,66],[30,14,7,5,23,15,28,10,34,25,35,36],[536,537]),([855,78,67],[30,0,23,14],[]),([855,78,70],[0,30,7,23,36,10,25,35,14,15],[529,538,539,540,209])]
set_option maxRecDepth 100000 in
theorem v189_9_14 : ∀ e ∈ k189_9_14, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_14 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_15 : List Entry := [([855,78,71],[0,30,14,23,26,25,36],[202,341,541,542]),([855,78,78],[30,0,14,5,15,28,10,34,25],[543]),([855,78,86],[7,15,9,16,23,14,10,34,25,35,28],[544,210]),([855,78,87],[15,9],[]),([855,94,66],[15,4,9,16,21,35,36],[]),([855,94,70],[0,15,23,36,21,25,35,9,4],[545,546,547,329]),([855,94,78],[15,0,30,5,9,28,21,34,25,35],[]),([855,94,82],[7,15,16,30,4,28,10,34,25,35,36],[548]),([855,94,86],[7,15,4,23,16,9,28],[444]),([855,94,90],[7,15,30,23,4,28,10,34,25,35,36],[]),([863,50,74],[7,30,6,22,15,28,10,23,25,35,36],[549,550]),([863,50,78],[30,6,22,15,28,10,34,25,35,36],[551]),([863,50,94],[15,4,6,30,28,29,34,25,36],[552,553]),([863,54,74],[0,7,5,6,30,15,4,28,10,34,25,35,36],[]),([863,54,78],[0,5,6,30,15,4,28,10,34,25,35,36],[]),([863,54,94],[0,3,4,35,36],[]),([863,66,74],[7,22,15,9,28,10,34,25,35],[]),([863,66,78],[7,6,30,15,9,28,10,34,25,35],[]),([863,66,94],[7,8,9,28],[]),([863,70,74],[30,14,7,6,22,15,28,10,34,25,35,36],[554,555]),([863,70,78],[30,0,7,14,22,15,28,10,23,25,35,36],[556,557]),([863,70,94],[15,9,22,14,10,34,25,35,23,28],[558]),([863,86,74],[15,4,9,18,25,35,36],[]),([863,86,78],[15,0,6,30,9,28,21,23,25,35,36],[559,560]),([863,86,90],[7,15,22,4,28,10,23,25,35,36],[561,562]),([863,86,94],[15,4,9,18,25,30,28],[]),([871,58,66],[7,34,23,15,28,10,35,36],[563,564]),([871,58,74],[7,34,5,15,28,10,30,23,35,36],[529,565]),([871,58,78],[34,5,27,15,28,10,30,23,35,36],[566]),([871,58,94],[15,4,5,34,28,29,30,23,36],[567,568]),([871,62,70],[0,5,6,34,15,4,1,28,10,30,23,35,36],[534,569]),([871,62,86],[0,4,3,35,36],[]),([871,74,74],[7,5,23,34,15,9,28,10,35],[]),([871,74,94],[7,8,9,28],[226]),([871,78,66],[34,14,7,5,23,15,28,10,35,36],[570,571]),([871,78,67],[34,0,23,14],[]),([871,78,70],[0,34,7,23,25,36,10,35,14,15],[529,572,573,574,227]),([871,78,71],[0,34,14,23,27,25,36],[220,346,575,576]),([871,78,78],[34,0,14,5,15,28,10,30,23],[577]),([871,78,86],[7,15,9,16,23,34,14,10,35,28],[578,228]),([871,78,87],[15,9],[]),([871,94,66],[15,4,9,16,21,35,36],[]),([871,94,70],[0,15,23,25,36,21,35,9,4],[579,580,581,335]),([871,94,78],[15,0,34,5,9,28,21,30,23,35],[]),([871,94,82],[7,15,16,34,4,28,10,30,23,35,36],[582]),([871,94,86],[7,15,4,23,34,16,9,28],[449]),([871,94,90],[7,15,34,23,4,28,10,35,36],[]),([879,50,74],[7,34,6,24,15,28,10,25,23,35,36],[583,584]),([879,50,78],[34,6,24,15,28,10,30,23,35,36],[585]),([879,50,94],[15,4,6,34,28,29,30,23,36],[586,587])]
set_option maxRecDepth 100000 in
theorem v189_9_15 : ∀ e ∈ k189_9_15, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_15 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def k189_9_16 : List Entry := [([879,54,74],[0,7,5,6,34,15,4,28,10,30,23,35,36],[]),([879,54,78],[0,5,6,34,15,4,28,10,30,23,35,36],[]),([879,54,94],[0,3,4,35,36],[]),([879,66,74],[7,23,6,34,15,9,28,10,30,35],[]),([879,66,78],[7,6,34,15,9,28,10,30,23,35],[]),([879,66,94],[7,8,9,28],[]),([879,70,74],[34,14,7,6,23,15,28,10,30,35,36],[588,589]),([879,70,78],[34,0,7,14,24,15,28,10,25,23,35,36],[590,591]),([879,70,94],[15,9,23,19,34,14,10,30,35,25,28],[592]),([879,86,74],[15,4,9,20,23,35,36],[]),([879,86,78],[15,0,6,34,9,28,21,25,23,35,36],[593,594]),([879,86,90],[7,15,24,4,28,10,25,23,35,36],[595,596]),([879,86,94],[15,4,9,20,23,34,28],[])]
set_option maxRecDepth 100000 in
theorem v189_9_16 : ∀ e ∈ k189_9_16, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := level_sound hR189 9 k189_9_16 (D189_8.map (wsOf c189.2)) (map_dead w189_8) (by decide +kernel)
def D189_9 : List Entry := k189_9_0 ++ (k189_9_1 ++ (k189_9_2 ++ (k189_9_3 ++ (k189_9_4 ++ (k189_9_5 ++ (k189_9_6 ++ (k189_9_7 ++ (k189_9_8 ++ (k189_9_9 ++ (k189_9_10 ++ (k189_9_11 ++ (k189_9_12 ++ (k189_9_13 ++ (k189_9_14 ++ (k189_9_15 ++ (k189_9_16))))))))))))))))
theorem w189_9 : ∀ e ∈ D189_9, ¬ Live516.live basicOps goal 9 (wsOf c189.2 e).toFinset := (app_dead v189_9_0 (app_dead v189_9_1 (app_dead v189_9_2 (app_dead v189_9_3 (app_dead v189_9_4 (app_dead v189_9_5 (app_dead v189_9_6 (app_dead v189_9_7 (app_dead v189_9_8 (app_dead v189_9_9 (app_dead v189_9_10 (app_dead v189_9_11 (app_dead v189_9_12 (app_dead v189_9_13 (app_dead v189_9_14 (app_dead v189_9_15 v189_9_16))))))))))))))))
def k189_10_0 : List Entry := [([19,26],[7,0,15,4,1,14,28,10,30,34,9],[0,1,2,3,4,5,6,7,8,9,10]),([19,62],[7,15,4,8,28,10,30,34,35],[11,12,13,14,15]),([19,74],[7,23,0,15,9,28,10,34,25,35],[16,17,18,19]),([19,78],[7,2,0,15,9,28,10,30,23,34,25,35,6],[20,21,22,23]),([19,110],[7,30,23,15,9,28,10,34,32,35],[]),([19,126],[7,34,25,15,9,28,10,30,32,35],[]),([19,300],[0,7,15,4,28,10,30,34,35],[24,25,26,27,28,29]),([19,323],[0,23,7,15,4,28,10,34,25,35,36],[20,30,22,31]),([19,327],[0,23,7,6,5,15,4,28,10,30,34,25,35,36],[21,16,32,19,23,33]),([19,359],[0,30,23,7,15,4,28,10,34,32,35,36],[34]),([19,375],[0,34,25,7,15,4,28,10,30,32,35,36],[35]),([19,574],[7,4,8,28,10,30,34,35],[36,37,38,39,40]),([19,590],[7,2,0,15,9,28,10,30,23,34,25,35,6,14],[41,31,33]),([19,1127],[7,30,23,0,15,9,28,10,34,25,35,36],[42,43,44,6,11,25,36]),([19,1135],[7,30,23,0,15,9,28,10,34,25,35,32,36],[45,46,47,48,7,12,26,37]),([19,1143],[7,34,23,0,15,9,28,10,35,36],[49,50,51,8,13,27,38]),([19,1151],[7,34,23,24,25,0,15,9,28,10,30,35,32,36],[52,53,54,55,9,14,28,39]),([19,1663],[7,34,30,31,23,15,28,10,35,36,0],[10,15,29,40]),([23,54],[0,15,4,9,28,10,30,34,35],[1,56,57,58,59,60,61,62,63,64]),([23,56],[7,0,15,1,28,10,30,34,35,14,36],[65,66,67,68,69,70,71,72,73]),([23,57],[0,15,1,14,10,28,30,34],[1,74,75,76,77,78,79]),([23,60],[1,28,10,30,34,35,14,36],[80,81,82,83,84,85,86,87,88,89,90,91,92]),([23,61],[35,15,1,14,10,28,30,34],[93,94,95,96,97,98]),([23,62],[15,4,35,28,10,30,34,9],[99,100,101,102,103,104,105,106,107]),([23,63],[15,1,7,0,13,4,9,10,28],[]),([23,66],[35,14,23,15,28,10,34,25],[16,108,109,110,111,112]),([23,70],[0,35,14,15,28,10,30,23,34,25,6],[3,20,113,114,115,116,117,118]),([23,74],[35,14,7,0,1,23,15,28,10,34,25,36],[119,120,121,122,123,124]),([23,75],[0,35,1,2,14,15,28,10,30,23,34,25,36],[3,125,126,127,128]),([23,78],[35,14,1,0,7,15,28,10,30,23,34,25,6,36],[129,130,131,132,133,134,135]),([23,79],[35,23,1,2,0,15,28,10,30,34,25,14],[125,136,137,138]),([23,102],[0,30,14,15,23,28,10,34,32],[139,140,141,142,143]),([23,110],[30,14,7,15,23,28,10,34,32,35,0,36],[144,145]),([23,111],[30,1,15,23,28,10,34,32,35,14],[146,147,148]),([23,118],[0,34,14,15,25,28,10,30,32],[149,150,151,152,153]),([23,126],[34,14,7,15,25,28,10,30,32,35,0,36],[154,155]),([23,127],[34,1,15,25,28,10,30,32,35,14],[156,157,158]),([23,296],[0,15,4,14,28,10,30,34,35],[24,159,160,161,74,93,127,137,147,157,162,163,164,165,166]),([23,310],[0,15,7,4,3,9,10,13,28,30,34,35],[167,168,128,138,148,158,169,170,171,172,173,174]),([23,311],[15,0,7,2,3,4,28,10,30,34,35,9],[175,176,177,178,112,118,124,135,143,145,153,155,179]),([23,318],[0,15,8,10,1,2,9,14,28,30,34],[180,181,182,183,184,185]),([23,323],[0,23,2,1,15,4,28,10,34,25,35],[21,129,186,187,175,133,188,65,84]),([23,327],[0,23,6,2,7,5,1,15,4,28,10,30,34,25,35],[21,119,189,190,176,122,134,191,66,85]),([23,359],[0,30,7,2,23,15,4,28,10,34,32,35,1],[192,193,177,67,86]),([23,375],[0,34,7,2,25,15,4,28,10,30,32,35,1],[194,195,178,68,87]),([23,566],[0,7,15,3,1,4,13,10,30,34,35],[196,180,197,198,199,200,201]),([23,574],[15,7,0,4,2,14,10,28,30,34],[202,203,168,204,205,206,207,208]),([23,582],[0,7,14,23,1,6,25,15,9,28,10,30,34,35],[209,210]),([23,590],[35,7,14,0,23,6,10,25,30,34,28],[120,211,212,123,188,191,213,214,169,179]),([23,843],[0,15,4,13,7,28,10,30,23,34,25,35],[215,216,217,218,219,116,213])]
set_option maxRecDepth 100000 in
theorem v189_10_0 : ∀ e ∈ k189_10_0, ¬ Live516.live basicOps goal 10 (wsOf c189.2 e).toFinset := level_sound hR189 10 k189_10_0 (D189_9.map (wsOf c189.2)) (map_dead w189_9) (by decide +kernel)
def k189_10_1 : List Entry := [([23,847],[15,4,13,7,28,10,30,23,34,25,35,9,6],[220,221,222,111,117,214]),([23,879],[15,30,4,13,7,23,28,10,34,32,35],[223,224,225]),([23,895],[15,34,4,13,7,25,28,10,30,32,35],[226,227,228]),([23,1127],[30,23,14,0,7,15,28,10,34,25,35,36],[229,230,231,232,233,234,235,60,69,75,88,94,103,162,170,181,197,204]),([23,1135],[30,23,14,0,7,15,28,10,34,25,35,32,36],[236,237,238,239,240,241,242,61,70,76,89,95,104,163,171,182,198,205]),([23,1143],[34,23,14,0,7,15,28,10,35,36],[243,244,245,246,247,248,249,62,71,77,90,96,105,164,172,183,199,206]),([23,1151],[34,23,24,14,25,0,7,15,28,10,30,35,32,36],[250,251,252,253,254,255,256,63,72,78,91,97,106,165,173,184,200,207]),([23,1663],[30,34,31,23,7,0,15,28,10,35,36],[64,73,79,92,98,107,166,174,185,201,208]),([27,60],[0,7,3,4,28,10,30,34,35],[160,257,258,259,260,261]),([27,62],[0,7,3,4,28,10,30,34,35],[161,262,263,264,265,266]),([27,72],[0,7,15,4,28,10,30,23,34,25,35],[]),([27,74],[0,7,15,4,28,10,30,23,34,25,35],[]),([27,76],[0,7,15,4,28,10,30,34,35],[267,268,269,270,271]),([27,78],[0,7,15,4,28,10,30,23,25,34,35],[272,273,274,275]),([27,92],[0,7,15,4,10,30,34,35],[276,277,278,279,280]),([27,104],[0,7,15,30,4,28,10,34,25,35],[]),([27,108],[0,7,15,4,23,28,10,34,33,35],[281]),([27,110],[0,7,15,30,4,23,28,10,34,32,35],[]),([27,120],[0,7,15,34,4,28,10,30,23,35],[]),([27,124],[0,7,15,4,25,28,10,30,32,35],[282]),([27,126],[0,7,15,34,4,25,28,10,30,32,35],[]),([27,1127],[0,30,5,23,7,15,4,28,10,34,25,35,36],[283,272,257,262,276,162]),([27,1135],[0,30,5,6,23,7,15,4,28,10,34,25,35,36],[284,285,286,273,258,263,277,282,163]),([27,1143],[0,34,5,23,7,15,4,28,10,35,25,36],[287,274,259,264,278,164]),([27,1151],[0,34,5,6,25,7,15,4,28,10,30,23,35,36],[288,289,290,275,260,265,279,281,165]),([27,1663],[0,34,30,31,23,25,7,36,10,35],[261,266,271,280,166]),([31,54],[0,7,4,15,3,9,28,10,30,34,35],[291,292,293,294,295]),([31,66],[0,7,14,15,4,28,10,30,23,34,25,35,36],[]),([31,70],[0,7,14,15,4,28,10,30,23,34,25,35,36],[]),([31,102],[0,7,14,15,4,23,28,10,34,32,35,36],[]),([31,118],[0,7,14,15,4,25,28,10,30,32,35,36],[]),([31,310],[0,3,7,4,9,28,10,30,34,35],[296,297,298,299,300]),([31,1127],[0,30,5,23,7,14,15,4,28,10,34,25,35,36],[301,6,291,25,296]),([31,1135],[0,30,5,6,23,7,14,15,4,28,10,34,25,35,36],[302,303,304,7,292,26,297]),([31,1143],[0,34,5,23,7,14,15,4,28,10,35,36],[305,8,293,27,298]),([31,1151],[0,34,5,6,25,7,14,15,4,28,10,30,23,35,36],[306,307,308,9,294,28,299]),([31,1663],[0,34,30,31,23,15,28,10,35,36],[10,295,29,300]),([39,50],[7,15,4,28,10,30,34,35,36],[309,310,311,312,313,314,315,316,317]),([39,58],[7,15,0,36,10,30,34,35,3,9],[318,319,320,321,322,323,324,325,326,327,328,329,167,330,331,332,333,334,335]),([39,62],[15,3,4,9,28,36,10,30,34],[336,337,338,339,340]),([39,66],[15,3,4,9,28,21,30,23,34,25,35],[]),([39,70],[0,15,3,4,9,28,21,30,23,34,25,35],[]),([39,74],[15,3,4,9,28,21,30,23,34,25,35,36],[341,342,343]),([39,78],[15,3,4,9,28,21,30,23,34,25,35,6,36],[344]),([39,102],[0,15,3,4,9,23,28,21,34,32,35],[]),([39,110],[15,3,30,9,23,28,21,34,32,35,36],[345]),([39,118],[0,15,3,4,9,25,28,21,30,32,35],[]),([39,126],[15,3,34,9,25,28,21,30,32,35,36],[346]),([39,323],[0,23,4,15,9,28,21,34,25,35,3,36],[347,175,348]),([39,327],[0,23,15,4,9,28,21,30,34,25,35,3,36],[118,349,176,350,351])]
set_option maxRecDepth 100000 in
theorem v189_10_1 : ∀ e ∈ k189_10_1, ¬ Live516.live basicOps goal 10 (wsOf c189.2 e).toFinset := level_sound hR189 10 k189_10_1 (D189_9.map (wsOf c189.2)) (map_dead w189_9) (by decide +kernel)
def k189_10_2 : List Entry := [([39,359],[0,30,15,4,9,23,28,21,34,32,35,3,36],[352,177]),([39,375],[0,34,15,4,9,25,28,21,30,32,35,3,36],[353,178]),([39,574],[15,7,4,9,10,28,30,34,35],[318,354,355,330,168,356,357,358,359,360]),([39,590],[15,4,9,23,28,6,21,25,30,34],[341,361,343]),([39,843],[0,15,23,9,28,10,34,25,35],[362,363,350]),([39,847],[15,23,7,9,2,0,28,10,30,34,25,35,6],[364,365,366,367,118,169,179,348,351]),([39,879],[15,30,7,9,23,0,28,10,34,32,35],[368,369]),([39,895],[15,34,7,9,25,0,28,10,30,32,35],[370,371]),([39,1127],[15,30,23,4,3,9,28,21,34,25,35,0,29,36],[372,373,374,375,376,313,60,331,336,170,296,356]),([39,1135],[15,30,23,4,3,9,28,21,34,25,35,32,0,29,36],[377,378,379,380,381,382,314,61,332,337,171,297,357]),([39,1143],[15,34,23,4,3,9,28,21,35,0,29,36],[383,384,385,386,387,315,62,333,338,172,298,358]),([39,1151],[15,34,23,24,4,3,25,9,28,21,30,35,32,0,29,36],[388,389,390,391,392,393,316,63,334,339,173,299,359]),([39,1663],[15,34,30,31,23,0,28,29,36],[317,64,335,340,174,300,360]),([47,50],[0,7,15,28,10,30,34,35,36],[394,395,396,397,398,399,400,401,402,403]),([47,54],[0,15,1,14,9,28,10,30,34],[1,404,405,406,407,408,409]),([47,66],[0,15,9,23,28,21,34,25,35,36],[410,411]),([47,70],[0,15,9,6,5,28,21,30,23,34,25,35,29,36],[412,413,414,415,416]),([47,102],[0,15,9,23,28,21,34,32,35,30,36],[417]),([47,118],[0,15,9,25,28,21,30,32,35,34,36],[418]),([47,570],[0,7,10,30,34,35],[1,419,404,180,416,420,421,422,423,424]),([47,843],[0,2,7,14,15,9,28,10,30,23,34,25],[425,414]),([47,847],[0,2,7,14,15,9,28,10,30,23,34,25,6],[426,398,411,415]),([47,879],[0,30,7,2,14,15,9,23,28,10,34,32],[427]),([47,895],[0,34,7,2,14,15,9,25,28,10,30,32],[428]),([47,1127],[0,30,5,23,15,9,28,21,34,25,35,29,36],[429,430,399,405,181,420]),([47,1135],[0,30,5,6,23,15,9,28,21,34,25,35,29,36],[431,432,433,434,400,406,182,421]),([47,1143],[0,34,5,23,15,9,28,21,35,29,36],[435,436,401,407,183,422]),([47,1151],[0,34,5,6,25,15,9,28,21,30,23,35,29,36],[437,438,439,440,402,408,184,423]),([47,1663],[0,34,30,31,23,15,28,29,36],[403,409,185,424]),([51,26],[0,22,6,5,15,4,28,29,23,34,25,36],[441,21,442,443,444]),([51,58],[7,35,0,23,15,28,10,34,25,36,9],[129,445,186]),([51,62],[35,22,2,0,7,23,15,28,10,34,25],[20,21,446,447,448,30,187,347,449]),([51,78],[15,4,28,29,30,23,34,25,36],[450,451,452]),([51,300],[0,23,15,4,28,29,34,25,36],[453]),([51,574],[35,22,23,2,0,15,28,10,34,25],[454,455,456,457,31,188,444,452,348]),([51,590],[15,4,3,23,28,9,21,34,25,35,36],[458,449]),([51,839],[7,15,23,4,28,10,34,25,35,36],[459,460]),([51,847],[15,7,23,4,28,10,34,25,35,2],[461,462,463]),([55,50],[7,35,15,28,10,30,23,34,25,36,6,9],[129,395,464]),([55,51],[7,6,35,15,28,10,30,23,34,25,36,9],[21,465,23,466,467,468]),([55,55],[35,7,5,6,15,28,10,30,23,34,25,2],[469,134,470,471,472,473,474,475,476,477]),([55,58],[7,35,0,23,15,28,10,30,34,25,36,5,9],[119,478,479,480,189,481,482]),([55,59],[0,7,35,5,15,28,10,30,23,34,25,36,9],[443,483,484,485,473,486,487]),([55,62],[35,2,0,23,5,15,28,10,30,34,25],[474,21,16,488,489,490,491,32,190,492,493,349,494,495,496]),([55,63],[35,7,5,6,0,15,28,10,30,23,34,25,2],[483,497,467,474,498,499,500,501]),([55,71],[15,4,3,28,29,30,23,34,25,6,9,36],[502,503,504,498,505]),([55,78],[15,4,28,29,30,23,34,25,9,36],[506,507,508,509,510]),([55,79],[15,4,28,29,30,23,34,25,9,5,36],[511,512,475,513]),([55,296],[0,15,4,28,29,30,23,34,25,36],[453,514,468,476,487,500]),([55,566],[0,35,23,7,2,15,5,28,10,34,25],[444,515,516,517,518,505,508,350])]
set_option maxRecDepth 100000 in
theorem v189_10_2 : ∀ e ∈ k189_10_2, ¬ Live516.live basicOps goal 10 (wsOf c189.2 e).toFinset := level_sound hR189 10 k189_10_2 (D189_9.map (wsOf c189.2)) (map_dead w189_9) (by decide +kernel)
def k189_10_3 : List Entry := [([55,571],[0,7,35,6,15,28,10,30,23,34,25,36,9],[444,21,488,465,519,520,492]),([55,574],[35,23,7,6,0,15,28,10,30,34,25,2],[478,521,484,522,523,524,525,526,527,481,486,499,33,191,528,509,513,351]),([55,575],[35,7,5,6,0,15,28,10,30,23,34,25,2],[479,21,469,529,530,482,493,510]),([55,582],[0,15,4,3,22,9,5,28,21,23,34,25,35,36],[531,116,477,494]),([55,590],[15,4,23,6,9,28,21,30,34,25,35,36],[532,533,117,495,501]),([55,591],[15,4,28,29,30,23,34,25,6,9,36],[502,534,535,536,496]),([55,839],[7,15,4,23,28,10,30,34,25,35,36],[537,538,539,540,541,542,543]),([55,847],[15,7,4,23,28,10,30,34,25,35,2],[544,545,546,547,548]),([59,56],[0,7,22,23,15,4,28,10,34,25,35,36],[]),([59,58],[0,7,22,23,15,4,28,10,34,25,35,36],[]),([59,60],[0,22,23,15,4,28,29,34,25,36],[]),([59,62],[0,22,7,23,15,4,28,10,34,25,35,36,29],[]),([59,72],[0,15,22,23,28,29,34,25,36],[]),([59,76],[0,3,4,22,23,28,29,34,25,36],[]),([59,78],[0,15,4,3,9,16,23,28,21,34,25,35,36],[]),([59,92],[0,22,28,10,15,4,23,34,25,35,36],[]),([59,104],[0,30,22,23,15,4,28,29,34,25,36],[]),([59,108],[0,22,23,15,4,28,29,34,25,36],[]),([59,120],[0,34,22,23,15,4,28,29,36],[]),([59,124],[0,22,34,23,24,25,15,4,28,29,36],[]),([63,50],[0,7,23,15,4,28,10,30,34,25,35,36],[395,549]),([63,54],[0,23,2,1,15,4,28,10,30,34,25,35],[21,3,550,551,552,553]),([63,70],[0,15,4,3,9,23,28,21,34,25,35,30,36],[554]),([63,571],[0,7,2,15,4,28,10,30,23,34,25,35,36,9],[3,555,552]),([63,575],[0,7,2,15,4,28,10,30,23,34,25,35],[395,21,556,444,549,553,554]),([87,58],[7,30,0,23,28,10,34,32,35,36,15,9],[557,192]),([87,62],[30,23,0,15,2,28,10,34,32,35],[558,559,560,34,193,352]),([87,78],[15,4,23,28,29,34,32,30,36],[561,562]),([87,839],[7,15,23,4,30,28,10,34,32,35,36],[563]),([87,847],[15,7,23,4,28,10,34,32,35,2],[564,565,566]),([95,50],[0,7,30,15,4,23,28,10,34,32,35,36],[]),([95,54],[0,30,15,4,23,28,10,34,32,35,36],[]),([95,70],[0,15,30,4,3,9,23,28,21,34,32,35,36],[]),([95,112],[0,34,30,15,4,23,28,29,36],[]),([95,116],[0,30,25,32,23,15,4,28,29,36],[]),([103,58],[7,34,0,25,28,10,30,32,35,36,15,9],[567,194]),([103,62],[34,25,0,15,2,28,10,30,32,35],[568,569,570,35,195,353]),([103,78],[15,4,25,28,29,30,32,34,36],[571,572]),([103,839],[7,15,25,4,34,28,10,30,32,35,36],[573]),([103,847],[15,7,25,4,28,10,30,32,35,2],[574,575,576]),([111,50],[0,7,34,15,4,25,28,10,30,32,35,36],[]),([111,54],[0,34,15,4,25,28,10,30,32,35,36],[]),([111,70],[0,15,34,4,3,9,25,28,21,30,32,35,36],[]),([111,112],[0,30,34,15,4,25,28,29,36],[]),([111,116],[0,34,23,32,25,15,4,28,29,36],[]),([295,58],[7,15,1,4,28,10,30,34,35],[1,577,537,578,579,419,580,581,582,583,584]),([295,62],[7,0,15,28,10,30,34,35],[585,488,586,587,588,589,590,591,592]),([295,74],[7,15,23,4,28,10,34,25,35],[593,594,595,541]),([295,78],[7,15,4,13,28,10,30,23,34,25,35],[596,597,537,460,542,543,196]),([295,110],[7,15,23,4,28,10,34,32,35,30],[598])]
set_option maxRecDepth 100000 in
theorem v189_10_3 : ∀ e ∈ k189_10_3, ¬ Live516.live basicOps goal 10 (wsOf c189.2 e).toFinset := level_sound hR189 10 k189_10_3 (D189_9.map (wsOf c189.2)) (map_dead w189_9) (by decide +kernel)
def k189_10_4 : List Entry := [([295,126],[7,15,25,4,28,10,30,32,35,34],[599]),([295,590],[7,15,4,23,28,10,34,25,35],[593,600,595]),([295,1127],[7,30,23,15,4,28,10,34,25,35,36],[601,602,603,580,588,197,420]),([295,1135],[7,30,23,15,4,28,10,34,25,35,32,36],[604,605,606,607,581,589,198,421]),([295,1143],[7,34,23,15,4,28,10,35,36],[608,609,610,582,590,199,422]),([295,1151],[7,34,23,24,25,15,4,28,10,30,35,32,36],[611,612,613,614,583,591,200,423]),([295,1663],[7,34,30,31,23,15,28,10,35,36],[584,592,201,424]),([303,50],[15,4,8,28,10,30,34,35],[462,565,575,615,616,617,618,619]),([303,54],[0,15,7,36,10,30,34,35,8,28],[318,620,621,622,623,624,625,626,627,628,629,630,202,354,463,566,576,631,632,633,634,635]),([303,62],[15,0,9,28,10,30,34,35],[636,637,638,639,640,641,642,643,644]),([303,66],[15,4,7,8,28,10,30,23,34,25,35],[645]),([303,70],[7,15,4,8,28,10,30,23,34,25,35],[646,548,203,355]),([303,74],[15,4,8,9,28,10,30,23,34,25,35],[593]),([303,78],[15,4,8,9,28,10,30,23,34,25,35],[647,648]),([303,102],[7,15,4,8,23,28,10,34,32,35],[649]),([303,110],[15,4,30,9,23,28,10,34,32,35],[]),([303,118],[7,15,4,8,25,28,10,30,32,35],[650]),([303,126],[15,4,34,9,25,28,10,30,32,35],[]),([303,1127],[15,30,23,8,4,14,28,10,34,25,35,36],[651,652,653,615,631,60,640,36,204,356]),([303,1135],[15,30,23,8,4,14,28,10,34,25,35,32,36],[654,655,656,657,658,616,632,61,641,37,205,357]),([303,1143],[15,34,23,8,4,14,28,10,35,36],[659,660,661,617,633,62,642,38,206,358]),([303,1151],[15,34,23,24,8,4,25,14,28,10,30,35,32,36],[662,663,664,665,666,618,634,63,643,39,207,359]),([303,1663],[15,34,30,31,23,7,28,10,35,36],[619,635,64,644,40,208,360]),([307,58],[7,22,23,15,9,28,10,34,25,35],[667]),([307,62],[7,22,23,15,9,28,10,34,25,35],[]),([307,78],[7,15,9,8,16,23,28,10,34,25,35],[]),([307,300],[7,14,15,9,28,10,30,23,34,25,35],[668,669,670,671,667]),([311,46],[7,14,15,9,28,10,30,23,34,25],[20,672,444]),([311,58],[7,23,6,15,9,28,10,30,34,25,35],[21,3,465,555]),([311,62],[7,0,23,15,9,28,10,30,34,25,35],[488,519]),([311,78],[7,15,9,8,23,4,28,10,34,25,35,30],[210,520]),([311,296],[7,23,15,9,28,10,34,25,35],[668]),([315,58],[35,14,7,23,15,2,28,10,34,25],[673,674,675,363,676]),([315,62],[35,0,7,14,23,15,28,10,34,25,36],[677]),([315,72],[7,15,14,35,36,22,23,28,10,34,25],[]),([315,76],[7,9,22,15,14,10,23,34,25,35,36,28],[678,516]),([315,78],[15,9,35,14,10,30,23,34,25,28],[679,517]),([315,590],[15,9,8,10,23,28,34,25,35],[680,676]),([319,50],[35,14,7,23,2,15,28,10,30,34,25,6],[395,681,682,683,469,556,367,684,685]),([319,51],[35,0,2,14,6,7,10,30,23,34,25,15,28],[398,686,687,688,522,670,689]),([319,54],[0,35,7,14,23,15,36,10,30,34,25,4,28],[120,478,479,690,691,692,693,694,695,696,697,211,523,529]),([319,55],[0,2,35,14,6,10,30,23,34,25,36,15,4,28],[20,398,686,521,698,699,700,701,702,703,704,524,671]),([319,62],[35,0,14,15,28,10,30,23,34,25,4],[488,705]),([319,70],[7,15,9,14,10,30,23,34,25,35,4,28],[706,212,455,525,530]),([319,71],[15,2,7,9,13,4,28,10,30,23,34,25,35],[688,456,526]),([319,582],[7,15,9,8,10,22,4,13,28,23,34,25,35],[707,684,689,116,213]),([319,590],[15,9,10,23,6,28,30,34,25,35],[708,709,685,117,214]),([319,591],[15,6,7,9,28,10,30,23,34,25,35],[710,711]),([343,58],[7,30,15,9,23,28,10,34,32,35],[]),([343,62],[7,30,15,9,23,28,10,34,32,35],[])]
set_option maxRecDepth 100000 in
theorem v189_10_4 : ∀ e ∈ k189_10_4, ¬ Live516.live basicOps goal 10 (wsOf c189.2 e).toFinset := level_sound hR189 10 k189_10_4 (D189_9.map (wsOf c189.2)) (map_dead w189_9) (by decide +kernel)
def k189_10_5 : List Entry := [([343,78],[7,15,30,8,9,23,28,10,34,32,35],[]),([351,50],[30,14,0,15,11,2,23,28,10,34,32,35],[712,713,369]),([351,54],[0,30,7,23,28,10,34,32,35,14,36],[714]),([351,70],[7,15,9,14,23,10,34,32,35,30,28],[715]),([359,58],[7,34,15,9,25,28,10,30,32,35],[]),([359,62],[7,34,15,9,25,28,10,30,32,35],[]),([359,78],[7,15,34,8,9,25,28,10,30,32,35],[]),([367,50],[34,14,0,15,12,2,25,28,10,30,32,35],[716,717,371]),([367,54],[0,34,7,25,28,10,30,32,35,14,36],[718]),([367,70],[7,15,9,14,25,10,30,32,35,34,28],[719]),([571,58],[15,4,9,28,21,30,23,34,25,35,36],[215,707]),([571,62],[15,0,23,9,28,21,34,25,35,36],[720]),([571,74],[7,15,23,4,28,10,34,25,35,36],[721,218]),([571,78],[15,4,7,9,28,10,30,23,34,25,35,36],[215,219,531]),([575,50],[15,4,9,28,21,30,23,34,25,35,6,36],[220,502,680,709]),([575,54],[0,15,23,9,36,21,30,34,25,35,4,6,28],[341,722,723,724,725,726,727,728,729,361,532,534]),([575,62],[15,0,9,28,21,30,23,34,25,35],[730]),([575,66],[7,15,23,4,28,10,30,34,25,35,36],[731,708,710,535]),([575,70],[7,15,4,9,28,10,30,23,34,25,35],[593,220,600,711,458,533,536]),([575,74],[7,15,4,28,10,30,23,34,25,35,36],[732]),([607,50],[15,4,9,17,23,28,21,34,32,35,36],[]),([607,54],[0,15,30,23,28,21,34,32,35,36],[733]),([607,66],[7,15,30,23,28,10,34,32,35,36],[734]),([607,70],[7,15,4,17,9,23,28,10,34,32,35],[]),([623,50],[15,4,9,19,25,28,21,30,32,35,36],[]),([623,54],[0,15,34,25,28,21,30,32,35,36],[735]),([623,66],[7,15,34,25,28,10,30,32,35,36],[736]),([623,70],[7,15,4,19,9,25,28,10,30,32,35],[]),([855,58],[30,22,0,26,5,15,28,29,34,25,36],[737,229,738,739,372,740,43,232,374,603,653]),([855,62],[30,0,23,15,28,29,34,25,4,36],[741,742,743]),([855,74],[7,30,23,15,28,10,34,25,35,36,9],[744,745,746,233]),([855,78],[30,22,7,14,15,28,10,34,25,35,36],[747,748,749,750,229,751,752,753,652,44,234,376,430]),([855,94],[15,22,30,4,9,28,29,34,25,36],[754,755,372,756,757,758,759,652,375,602,235]),([863,50],[30,22,23,15,28,29,34,25,0,36],[760,761,762,46,239,379,605,656]),([863,54],[0,30,22,23,15,28,29,34,25,4,36],[763,764,765]),([863,66],[7,30,22,15,28,10,34,25,35,36,9],[766,767,768]),([863,70],[7,30,22,23,15,28,10,34,25,35,14,36],[769,770,771,380,432]),([863,86],[15,22,28,29,34,25,23,9,4,36],[772,773,774,775,240]),([863,112],[30,34,22,23,15,28,29,36],[47,241,285,303,381,433,606,657]),([863,116],[30,34,22,15,28,29,36],[48,242,286,304,382,434,607,658]),([871,58],[34,22,0,27,5,15,28,29,23,36],[776,243,777,778,383,779,50,246,385,610,661]),([871,62],[34,0,23,15,28,29,4,36],[741,780,781]),([871,74],[7,34,23,15,28,10,35,36,9],[782,745,783,247]),([871,78],[34,22,7,14,15,28,10,23,35,36],[784,785,786,787,243,788,789,790,660,51,248,387,436]),([871,94],[15,22,34,4,9,28,29,23,36],[791,792,383,793,794,795,796,660,386,609,249]),([879,50],[34,24,25,15,28,29,30,23,0,36],[797,798,799,53,253,390,612,664]),([879,54],[0,34,23,25,15,28,29,30,4,36],[800,801,802]),([879,66],[7,34,23,15,28,10,30,35,36,24,9],[803,804,805]),([879,70],[7,34,24,25,15,28,10,30,23,35,14,36],[806,807,808,391,438]),([879,86],[15,24,28,29,30,23,25,9,4,36],[809,810,811,812,254])]
set_option maxRecDepth 100000 in
theorem v189_10_5 : ∀ e ∈ k189_10_5, ¬ Live516.live basicOps goal 10 (wsOf c189.2 e).toFinset := level_sound hR189 10 k189_10_5 (D189_9.map (wsOf c189.2)) (map_dead w189_9) (by decide +kernel)
def k189_10_6 : List Entry := [([879,112],[30,34,22,24,25,15,28,29,36],[54,255,289,307,392,439,613,665]),([879,116],[34,30,23,15,28,29,36],[55,256,290,308,393,440,614,666])]
set_option maxRecDepth 100000 in
theorem v189_10_6 : ∀ e ∈ k189_10_6, ¬ Live516.live basicOps goal 10 (wsOf c189.2 e).toFinset := level_sound hR189 10 k189_10_6 (D189_9.map (wsOf c189.2)) (map_dead w189_9) (by decide +kernel)
def D189_10 : List Entry := k189_10_0 ++ (k189_10_1 ++ (k189_10_2 ++ (k189_10_3 ++ (k189_10_4 ++ (k189_10_5 ++ (k189_10_6))))))
theorem w189_10 : ∀ e ∈ D189_10, ¬ Live516.live basicOps goal 10 (wsOf c189.2 e).toFinset := (app_dead v189_10_0 (app_dead v189_10_1 (app_dead v189_10_2 (app_dead v189_10_3 (app_dead v189_10_4 (app_dead v189_10_5 v189_10_6))))))
def k189_11_0 : List Entry := [([19],[7,35,15,28,10,30,34,36,0,9],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]),([23],[35,7,0,15,14,28,10,30,34,36],[18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57]),([27],[0,35,7,36,10,30,34,15,4],[58,59,60,61,62,63,64,65,66,67,68,69,70,37,71,72,73,74,75]),([31],[35,0,15,28,10,30,34,4,14,36],[0,76,77,78,79,80,6,81,82,83,84,85,86]),([39],[15,0,4,3,28,29,30,34,9,36],[87,18,88,89,90,91,92,93,94,95,96,97,38,39,81,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112]),([47],[15,0,28,29,30,34,9,36],[113,114,115,116,117,118,40,119,120,121,122,123,124,125,126,127,128]),([51],[35,23,15,28,29,34,25,0,36],[129,130,131,132,133,7,41,98,134,135,136,137]),([55],[35,23,0,15,28,29,30,34,25,36],[138,139,26,140,141,142,143,144,91,145,146,147,148,8,42,99,149,150,151,152,153,154,155,156,157]),([59],[0,35,23,15,36,29,34,25,4],[158,159,160,161,162,163,164,165,166,167,168,169,148]),([63],[35,0,15,28,29,30,23,34,25,4,36],[129,170,171,172,133,173,174]),([87],[30,0,23,15,28,29,34,32,36],[175,176,177,9,43,100,178,179]),([95],[30,0,15,23,28,29,34,32,4,36],[180,181,182,183,184]),([103],[34,0,25,15,28,29,30,32,36],[185,186,187,10,44,101,188,189]),([111],[34,0,15,25,28,29,30,32,4,36],[190,191,192,193,194]),([295],[7,15,28,10,30,34,35,36,4],[195,196,197,198,199,200,45,119,201,136,156,178,188,202,203,204,205,206]),([303],[15,7,4,8,28,10,30,34,35,14,36],[207,208,18,209,210,211,212,213,214,215,216,217,11,46,102,137,157,179,189,218,219,220,221,222]),([307],[7,35,23,15,28,10,34,25,36,9],[223,224,225,226]),([311],[7,35,15,28,10,30,23,34,25,36,9],[227,228,229,230,231,47,150,173]),([315],[7,35,23,15,28,10,34,25,14,36],[227,232,233,234,235,236,231,149,237,104,120]),([319],[35,23,7,14,15,28,10,30,34,25,36],[238,239,240,241,26,242,243,244,213,226,12,48,134,151,152,174,245,246,247,105,121]),([343],[7,30,15,23,28,10,34,32,35,36,9],[248,249,250]),([351],[30,7,23,15,28,10,34,32,35,14,36],[251,252,253,106,122]),([359],[7,34,15,25,28,10,30,32,35,36,9],[254,255,256]),([367],[34,7,25,15,28,10,30,32,35,14,36],[257,258,259,107,123]),([571],[15,23,28,29,34,25,9,4,36],[260,261,262,263,153,245,49]),([575],[15,23,4,9,28,29,30,34,25,36],[264,265,91,266,267,268,269,213,103,201,135,154,155,237,246,247,50]),([607],[15,30,4,23,28,29,34,32,9,36],[270,271,272,273,51]),([623],[15,34,4,25,28,29,30,32,9,36],[274,275,276,277,52]),([855],[30,23,15,28,29,34,25,36],[278,279,280,281,282,13,53,71,82,108,124,202,218]),([863],[30,23,15,28,29,34,25,32,36],[283,284,285,286,287,288,289,14,54,72,83,109,125,203,219]),([871],[34,23,15,28,29,36],[290,291,292,293,294,15,55,73,84,110,126,204,220]),([879],[34,23,24,25,15,28,29,30,32,36],[295,296,297,298,299,300,301,16,56,74,85,111,127,205,221]),([1391],[30,34,31,23,15,28,29,36],[17,57,75,86,112,128,206,222])]
set_option maxRecDepth 100000 in
theorem v189_11_0 : ∀ e ∈ k189_11_0, ¬ Live516.live basicOps goal 11 (wsOf c189.2 e).toFinset := level_sound hR189 11 k189_11_0 (D189_10.map (wsOf c189.2)) (map_dead w189_10) (by decide +kernel)
def D189_11 : List Entry := k189_11_0
theorem w189_11 : ∀ e ∈ D189_11, ¬ Live516.live basicOps goal 11 (wsOf c189.2 e).toFinset := v189_11_0
def k189_12_0 : List Entry := [([],[15,28,29,30,34,36],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32])]
set_option maxRecDepth 100000 in
theorem v189_12_0 : ∀ e ∈ k189_12_0, ¬ Live516.live basicOps goal 12 (wsOf c189.2 e).toFinset := level_sound hR189 12 k189_12_0 (D189_11.map (wsOf c189.2)) (map_dead w189_11) (by decide +kernel)
def D189_12 : List Entry := k189_12_0
theorem w189_12 : ∀ e ∈ D189_12, ¬ Live516.live basicOps goal 12 (wsOf c189.2 e).toFinset := v189_12_0
theorem g189 : GoodC c189 := claim_sound2 D189_12 c189 w189_12 (by decide +kernel)

end Check516

end PEqualNP.Outside.L_meta_8507

theorem PEqualNP.Outside.L_meta_8507 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6)) t → 13 ≤ t :=
  fun t h => PEqualNP.Outside.L_meta_8507.Check516.final_bound 12 PEqualNP.Outside.L_meta_8507.Check516.g189 t h
