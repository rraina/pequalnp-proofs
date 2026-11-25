import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8519


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
  [0x9f087e021111f810888fc1111111fc0849148a9f0f003e000000f8000007c0000000fc000000000f,
   0x7117c205f02f082f8178422222220497c2f179717007c001f00f000f8078000000000007c0f07870,
   0xa2f8843e20f211f107908f0f0f0f0878872391a280f8003e00f001f007800f0f0f0f007807038180,
   0x421087fff00204212211ff00ff0107ff803fe040000003fff00000000000ff00ff0007ff803fe00,
   0x8421088424443fff8020ffff000207ffffc000800000000000001fff8000ffff000007ffffc0000,
   0x408421108488848424442fffffffff8100402040000000000000000000000fffffffff8000000000,
   0xffffe1080001fffffff444444441221002440000ffffc0000001fffffff0000000000000000000,
   0xffffffffffff0840000888888882442488000000fffffffffffe00000000000000000000000000]

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
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)

def assignment (k : Fin 320) (i : Fin 8) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live516.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 160) := [4, 0, 1, 2, 3, 6, 10, 19]
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
  have ht : (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7) =
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

def c0 : Claim := (4, available 0xe001f80ec007c076003ccccccc0360340a0400 10 inputs)
def r0 : List RE := []
def d0 : List Entry := [([4096],[],[]),([],[],[])]
def e0 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g0 : GoodC c0 := claim_sound [] gnil r0 d0 e0 c0 (by decide +kernel)
def c1 : Claim := (4, available 0x1c00e000600700030c0c0c0030030080400 10 inputs)
def r1 : List RE := []
def d1 : List Entry := [([],[],[])]
def e1 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g1 : GoodC c1 := claim_sound [] gnil r1 d1 e1 c1 (by decide +kernel)
def c2 : Claim := (3, available 0x40000000000c060000000000a000028000c80040 6 inputs)
def r2 : List RE := []
def d2 : List Entry := [([],[],[])]
def e2 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g2 : GoodC c2 := claim_sound [] gnil r2 d2 e2 c2 (by decide +kernel)
def c3 : Claim := (4, available 0x1ce000000000000e000e0000730006400 10 inputs)
def r3 : List RE := []
def d3 : List Entry := [([],[],[])]
def e3 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g3 : GoodC c3 := claim_sound [] gnil r3 d3 e3 c3 (by decide +kernel)
def c4 : Claim := (3, available 0x4000000000000000006030000060018000006440 6 inputs)
def r4 : List RE := []
def d4 : List Entry := [([],[],[])]
def e4 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g4 : GoodC c4 := claim_sound [] gnil r4 d4 e4 c4 (by decide +kernel)
def c5 : Claim := (4, available 0xe700000e0e000000730c80000 19 inputs)
def r5 : List RE := []
def d5 : List Entry := [([],[],[])]
def e5 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g5 : GoodC c5 := claim_sound [] gnil r5 d5 e5 c5 (by decide +kernel)
def c6 : Claim := (6, available 0x400701c1ce0c060e706030e0e0e0038730c86440 6 inputs)
def r6 : List RE := [(0x1c00e000600700030c0c0c0030030080400,10,0),(0x40000000000c060000000000a000028000c80040,6,1),(0x1ce000000000000e000e0000730006400,10,2),(0x4000000000000000006030000060018000006440,6,3),(0xe700000e0e000000730c80000,19,4)]
def d6 : List Entry := [([],[0,1,3,2,4],[0])]
def e6 : List (List Entry) := [[([50],[],[])]]
set_option maxRecDepth 100000 in
theorem g6 : GoodC c6 := claim_sound [c1,c2,c3,c4,c5] (gcons g1 (gcons g2 (gcons g3 (gcons g4 (gcons g5 gnil))))) r6 d6 e6 c6 (by decide +kernel)
def c7 : Claim := (7, available 0x60f781fdeeee07ef77703eeeeeee03f7b6eb7560 5 inputs)
def r7 : List RE := [(0xe001f80ec007c076003ccccccc0360340a0400,10,0),(0x400701c1ce0c060e706030e0e0e0038730c86440,6,1)]
def d7 : List Entry := [([],[0,1],[])]
def e7 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g7 : GoodC c7 := claim_sound [c0,c6] (gcons g0 (gcons g6 gnil)) r7 d7 e7 c7 (by decide +kernel)
def c8 : Claim := (3, available 0xc0018000c007806400200cc00c030004080000 19 inputs)
def r8 : List RE := []
def d8 : List Entry := [([4096],[],[]),([],[],[])]
def e8 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g8 : GoodC c8 := claim_sound [] gnil r8 d8 e8 c8 (by decide +kernel)
def c9 : Claim := (3, available 0x1800000060060002000c000030000080000 19 inputs)
def r9 : List RE := []
def d9 : List Entry := [([],[],[])]
def e9 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g9 : GoodC c9 := claim_sound [] gnil r9 d9 e9 c9 (by decide +kernel)
def c10 : Claim := (4, available 0xd0000000e001a00500000e000e000006000100 8 inputs)
def r10 : List RE := []
def d10 : List Entry := [([],[],[])]
def e10 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g10 : GoodC c10 := claim_sound [] gnil r10 d10 e10 c10 (by decide +kernel)
def c11 : Claim := (3, available 0x6000000000aa040000000000000a028000000160 5 inputs)
def r11 : List RE := []
def d11 : List Entry := [([],[],[])]
def e11 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g11 : GoodC c11 := claim_sound [] gnil r11 d11 e11 c11 (by decide +kernel)
def c12 : Claim := (4, available 0x6094810000aa040005502000000e038000000160 5 inputs)
def r12 : List RE := [(0x6000000000aa040000000000000a028000000160,5,0)]
def d12 : List Entry := [([],[0],[])]
def e12 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g12 : GoodC c12 := claim_sound [c11] (gcons g11 gnil) r12 d12 e12 c12 (by decide +kernel)
def c13 : Claim := (3, available 0x6000000000000000055020000006018000000160 5 inputs)
def r13 : List RE := []
def d13 : List Entry := [([],[],[])]
def e13 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g13 : GoodC c13 := claim_sound [] gnil r13 d13 e13 c13 (by decide +kernel)
def c14 : Claim := (4, available 0x1ad6000000ee000000006e80000 19 inputs)
def r14 : List RE := []
def d14 : List Entry := [([],[],[])]
def e14 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g14 : GoodC c14 := claim_sound [] gnil r14 d14 e14 c14 (by decide +kernel)
def c15 : Claim := (4, available 0x6000000000ee06000000000aa00a028006e80160 5 inputs)
def r15 : List RE := []
def d15 : List Entry := [([],[],[])]
def e15 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g15 : GoodC c15 := claim_sound [] gnil r15 d15 e15 c15 (by decide +kernel)
def c16 : Claim := (6, available 0x60d6818000ee07ad6550200ee00e038006e80160 5 inputs)
def r16 : List RE := [(0xc0018000c007806400200cc00c030004080000,19,0),(0x1800000060060002000c000030000080000,19,1),(0xd0000000e001a00500000e000e000006000100,8,2),(0x6094810000aa040005502000000e038000000160,5,3),(0x6000000000000000055020000006018000000160,5,4),(0x1ad6000000ee000000006e80000,19,5),(0x6000000000ee06000000000aa00a028006e80160,5,6)]
def d16 : List Entry := [([],[0,6,1,2,3,5,4],[0])]
def e16 : List (List Entry) := [[([837],[],[])]]
set_option maxRecDepth 100000 in
theorem g16 : GoodC c16 := claim_sound [c8,c9,c10,c12,c13,c14,c15] (gcons g8 (gcons g9 (gcons g10 (gcons g12 (gcons g13 (gcons g14 (gcons g15 gnil))))))) r16 d16 e16 c16 (by decide +kernel)
def c17 : Claim := (5, available 0x3dee00000000000ee00ee00077b0037400 10 inputs)
def r17 : List RE := []
def d17 : List Entry := [([],[],[])]
def e17 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g17 : GoodC c17 := claim_sound [] gnil r17 d17 e17 c17 (by decide +kernel)
def c18 : Claim := (3, available 0xa001700c800400060030000ccc030000020400 10 inputs)
def r18 : List RE := []
def d18 : List Entry := [([4096],[],[]),([],[],[])]
def e18 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g18 : GoodC c18 := claim_sound [] gnil r18 d18 e18 c18 (by decide +kernel)
def c19 : Claim := (3, available 0x1400c0004000000300000c0030000000400 10 inputs)
def r19 : List RE := []
def d19 : List Entry := [([],[],[])]
def e19 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g19 : GoodC c19 := claim_sound [] gnil r19 d19 e19 c19 (by decide +kernel)
def c20 : Claim := (4, available 0xb0003400a00000070000000e0e000000030100 8 inputs)
def r20 : List RE := []
def d20 : List Entry := [([],[],[])]
def e20 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g20 : GoodC c20 := claim_sound [] gnil r20 d20 e20 c20 (by decide +kernel)
def c21 : Claim := (4, available 0x35ac000000000000000ee0000000037400 10 inputs)
def r21 : List RE := []
def d21 : List Entry := [([],[],[])]
def e21 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g21 : GoodC c21 := claim_sound [] gnil r21 d21 e21 c21 (by decide +kernel)
def c22 : Claim := (4, available 0x6000000000000000077030000666018000037560 5 inputs)
def r22 : List RE := []
def d22 : List Entry := [([],[],[])]
def e22 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g22 : GoodC c22 := claim_sound [] gnil r22 d22 e22 c22 (by decide +kernel)
def c23 : Claim := (6, available 0x60b58175acaa0400077030000eee038000037560 5 inputs)
def r23 : List RE := [(0xa001700c800400060030000ccc030000020400,10,0),(0x1400c0004000000300000c0030000000400,10,1),(0xb0003400a00000070000000e0e000000030100,8,2),(0x6094810000aa040005502000000e038000000160,5,3),(0x6000000000aa040000000000000a028000000160,5,4),(0x35ac000000000000000ee0000000037400,10,5),(0x6000000000000000077030000666018000037560,5,6)]
def d23 : List Entry := [([],[0,6,1,2,3,5,4],[0])]
def e23 : List (List Entry) := [[([853],[],[])]]
set_option maxRecDepth 100000 in
theorem g23 : GoodC c23 := claim_sound [c18,c19,c20,c12,c11,c21,c22] (gcons g18 (gcons g19 (gcons g20 (gcons g12 (gcons g11 (gcons g21 (gcons g22 gnil))))))) r23 d23 e23 c23 (by decide +kernel)
def c24 : Claim := (5, available 0x1ef70000eeee0000077b6e80000 19 inputs)
def r24 : List RE := []
def d24 : List Entry := [([],[],[])]
def e24 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g24 : GoodC c24 := claim_sound [] gnil r24 d24 e24 c24 (by decide +kernel)
def c25 : Claim := (4, available 0x80031800000c60068062000d000e300000c0008 3 inputs)
def r25 : List RE := []
def d25 : List Entry := [([],[],[])]
def e25 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g25 : GoodC c25 := claim_sound [] gnil r25 d25 e25 c25 (by decide +kernel)
def c26 : Claim := (3, available 0x80000000000c600000000009000a200000c0008 3 inputs)
def r26 : List RE := []
def d26 : List Entry := [([],[],[])]
def e26 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g26 : GoodC c26 := claim_sound [] gnil r26 d26 e26 c26 (by decide +kernel)
def c27 : Claim := (4, available 0x40029400d00a4000005300000d0d30000000604 2 inputs)
def r27 : List RE := []
def d27 : List Entry := [([],[],[])]
def e27 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g27 : GoodC c27 := claim_sound [] gnil r27 d27 e27 c27 (by decide +kernel)
def c28 : Claim := (3, available 0x400000000000000000530000050510000000604 2 inputs)
def r28 : List RE := []
def d28 : List Entry := [([],[],[])]
def e28 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g28 : GoodC c28 := claim_sound [] gnil r28 d28 e28 c28 (by decide +kernel)
def c29 : Claim := (4, available 0xc0018c00b0062005803100000000000380c060c 2 inputs)
def r29 : List RE := []
def d29 : List Entry := [([],[],[])]
def e29 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g29 : GoodC c29 := claim_sound [] gnil r29 d29 e29 c29 (by decide +kernel)
def c30 : Claim := (3, available 0xc000000030062000000000000000000280c020c 2 inputs)
def r30 : List RE := []
def d30 : List Entry := [([],[],[])]
def e30 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g30 : GoodC c30 := claim_sound [] gnil r30 d30 e30 c30 (by decide +kernel)
def c31 : Claim := (3, available 0xc0000000000000018031000000000001804060c 2 inputs)
def r31 : List RE := []
def d31 : List Entry := [([],[],[])]
def e31 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g31 : GoodC c31 := claim_sound [] gnil r31 d31 e31 c31 (by decide +kernel)
def c32 : Claim := (4, available 0xc0000000700e600000000909090b200280c020c 2 inputs)
def r32 : List RE := []
def d32 : List Entry := [([],[],[])]
def e32 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g32 : GoodC c32 := claim_sound [] gnil r32 d32 e32 c32 (by decide +kernel)
def c33 : Claim := (4, available 0xc0000000000000038073050505071001804060c 2 inputs)
def r33 : List RE := []
def d33 : List Entry := [([],[],[])]
def e33 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g33 : GoodC c33 := claim_sound [] gnil r33 d33 e33 c33 (by decide +kernel)
def c34 : Claim := (7, available 0xc0039c00f00e600780730d0d0d0f300380c060c 2 inputs)
def r34 : List RE := [(0x1800000060060002000c000030000080000,19,0),(0x1400c0004000000300000c0030000000400,10,1),(0x80031800000c60068062000d000e300000c0008,3,2),(0x80000000000c600000000009000a200000c0008,3,3),(0x40029400d00a4000005300000d0d30000000604,2,4),(0x400000000000000000530000050510000000604,2,5),(0xc0018c00b0062005803100000000000380c060c,2,6),(0xc000000030062000000000000000000280c020c,2,7),(0xc0000000000000018031000000000001804060c,2,8),(0xc0000000700e600000000909090b200280c020c,2,9),(0xc0000000000000038073050505071001804060c,2,10)]
def d34 : List Entry := [([],[2,0,4,1,6,9,10,3,5,7,8],[0,1,2,3,4,5,6,7,8])]
def e34 : List (List Entry) := [[([55],[6],[]),([71],[9,0],[0]),([87],[10,1],[1]),([303],[2,0],[2]),([319],[2,3],[3]),([351],[2],[]),([575],[4,5],[4]),([591],[4],[]),([1119],[9,7],[5])],[([71,60],[],[]),([87,76],[],[]),([303,48],[],[]),([319,84],[],[]),([575,100],[],[]),([1119,100],[],[])]]
set_option maxRecDepth 100000 in
theorem g34 : GoodC c34 := claim_sound [c9,c19,c25,c26,c27,c28,c29,c30,c31,c32,c33] (gcons g9 (gcons g19 (gcons g25 (gcons g26 (gcons g27 (gcons g28 (gcons g29 (gcons g30 (gcons g31 (gcons g32 (gcons g33 gnil))))))))))) r34 d34 e34 c34 (by decide +kernel)
def c35 : Claim := (8, available 0x8ee83dfa0fd0f7d07e87bdddddddfb683d0e868e 1 inputs)
def r35 : List RE := [(0xc0039c00f00e600780730d0d0d0f300380c060c,2,0)]
def d35 : List Entry := [([],[0],[])]
def e35 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g35 : GoodC c35 := claim_sound [c34] (gcons g34 gnil) r35 d35 e35 c35 (by decide +kernel)
def c36 : Claim := (4, available 0x80c8000000d001900480000d000d000005000080 7 inputs)
def r36 : List RE := []
def d36 : List Entry := [([],[],[])]
def e36 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g36 : GoodC c36 := claim_sound [] gnil r36 d36 e36 c36 (by decide +kernel)
def c37 : Claim := (3, available 0x8a481480005053104882800000000000050c008a 1 inputs)
def r37 : List RE := []
def d37 : List Entry := [([4099],[],[]),([],[],[])]
def e37 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g37 : GoodC c37 := claim_sound [] gnil r37 d37 e37 c37 (by decide +kernel)
def c38 : Claim := (4, available 0x8a00000000d0d600000000099009aa00050c008a 1 inputs)
def r38 : List RE := []
def d38 : List Entry := [([],[],[])]
def e38 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g38 : GoodC c38 := claim_sound [] gnil r38 d38 e38 c38 (by decide +kernel)
def c39 : Claim := (4, available 0xc83580000001906c86a0000000000000000000 77 inputs)
def r39 : List RE := []
def d39 : List Entry := [([],[],[])]
def e39 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g39 : GoodC c39 := claim_sound [] gnil r39 d39 e39 c39 (by decide +kernel)
def c40 : Claim := (6, available 0x8ac8358000d0d7906c86a00dd00deb00050c008a 1 inputs)
def r40 : List RE := [(0xc0018000c007806400200cc00c030004080000,19,0),(0x80031800000c60068062000d000e300000c0008,3,1),(0x80c8000000d001900480000d000d000005000080,7,2),(0x8a481480005053104882800000000000050c008a,1,3),(0x8a00000000d0d600000000099009aa00050c008a,1,4),(0xc83580000001906c86a0000000000000000000,77,5)]
def d40 : List Entry := [([],[0,1,2,3,4,5],[])]
def e40 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g40 : GoodC c40 := claim_sound [c8,c25,c36,c37,c38,c39] (gcons g8 (gcons g25 (gcons g36 (gcons g37 (gcons g38 (gcons g39 gnil)))))) r40 d40 e40 c40 (by decide +kernel)
def c41 : Claim := (4, available 0x80a8003200900000068000000d0d000000028080 7 inputs)
def r41 : List RE := []
def d41 : List Entry := [([],[],[])]
def e41 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g41 : GoodC c41 := claim_sound [] gnil r41 d41 e41 c41 (by decide +kernel)
def c42 : Claim := (3, available 0x86280c6209103000028190000000000000028686 1 inputs)
def r42 : List RE := []
def d42 : List Entry := [([4100],[],[]),([],[],[])]
def e42 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g42 : GoodC c42 := claim_sound [] gnil r42 d42 e42 c42 (by decide +kernel)
def c43 : Claim := (4, available 0x86000000000000000685b0000555590000028686 1 inputs)
def r43 : List RE := []
def d43 : List Entry := [([],[],[])]
def e43 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g43 : GoodC c43 := claim_sound [] gnil r43 d43 e43 c43 (by decide +kernel)
def c44 : Claim := (4, available 0xa82d720d90b400000000000000000000000000 106 inputs)
def r44 : List RE := []
def d44 : List Entry := [([],[],[])]
def e44 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g44 : GoodC c44 := claim_sound [] gnil r44 d44 e44 c44 (by decide +kernel)
def c45 : Claim := (6, available 0x86a82d720d90b4000685b0000ddddb0000028686 1 inputs)
def r45 : List RE := [(0xa001700c800400060030000ccc030000020400,10,0),(0x40029400d00a4000005300000d0d30000000604,2,1),(0x80a8003200900000068000000d0d000000028080,7,2),(0x86280c6209103000028190000000000000028686,1,3),(0x86000000000000000685b0000555590000028686,1,4),(0xa82d720d90b400000000000000000000000000,106,5)]
def d45 : List Entry := [([],[0,1,2,3,4,5],[])]
def e45 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g45 : GoodC c45 := claim_sound [c18,c27,c41,c42,c43,c44] (gcons g18 (gcons g27 (gcons g41 (gcons g42 (gcons g43 (gcons g44 gnil)))))) r45 d45 e45 c45 (by decide +kernel)
def c46 : Claim := (3, available 0x8a000000005052000000000000000000050c008a 1 inputs)
def r46 : List RE := []
def d46 : List Entry := [([],[],[])]
def e46 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g46 : GoodC c46 := claim_sound [] gnil r46 d46 e46 c46 (by decide +kernel)
def c47 : Claim := (3, available 0x8600000000000000028190000000000000028686 1 inputs)
def r47 : List RE := []
def d47 : List Entry := [([],[],[])]
def e47 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g47 : GoodC c47 := claim_sound [] gnil r47 d47 e47 c47 (by decide +kernel)
def c48 : Claim := (4, available 0x8e00000a0350720000000000000000482d0c828e 1 inputs)
def r48 : List RE := [(0xc000000030062000000000000000000280c020c,2,0)]
def d48 : List Entry := [([],[0],[])]
def e48 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g48 : GoodC c48 := claim_sound [c30] (gcons g30 gnil) r48 d48 e48 c48 (by decide +kernel)
def c49 : Claim := (4, available 0x681cc0000001505a8390000000000000000000 76 inputs)
def r49 : List RE := []
def d49 : List Entry := [([],[],[])]
def e49 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g49 : GoodC c49 := claim_sound [] gnil r49 d49 e49 c49 (by decide +kernel)
def c50 : Claim := (4, available 0x8e000000000000501a839000000000281906868e 1 inputs)
def r50 : List RE := [(0xc0000000000000018031000000000001804060c,2,0)]
def d50 : List Entry := [([],[0],[])]
def e50 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g50 : GoodC c50 := claim_sound [c31] (gcons g31 gnil) r50 d50 e50 c50 (by decide +kernel)
def c51 : Claim := (4, available 0x681cea0b507200000000000000000000000000 105 inputs)
def r51 : List RE := []
def d51 : List Entry := [([],[],[])]
def e51 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g51 : GoodC c51 := claim_sound [] gnil r51 d51 e51 c51 (by decide +kernel)
def c52 : Claim := (6, available 0x8e681cea0b5073505a839000000000683d0e868e 1 inputs)
def r52 : List RE := [(0xc0018c00b0062005803100000000000380c060c,2,0),(0x8a000000005052000000000000000000050c008a,1,1),(0x8600000000000000028190000000000000028686,1,2),(0x8e00000a0350720000000000000000482d0c828e,1,3),(0x681cc0000001505a8390000000000000000000,76,4),(0x8e000000000000501a839000000000281906868e,1,5),(0x681cea0b507200000000000000000000000000,105,6)]
def d52 : List Entry := [([],[0,3,4,5,6,1,2],[0])]
def e52 : List (List Entry) := [[([29],[],[])]]
set_option maxRecDepth 100000 in
theorem g52 : GoodC c52 := claim_sound [c29,c46,c47,c48,c49,c50,c51] (gcons g29 (gcons g46 (gcons g47 (gcons g48 (gcons g49 (gcons g50 (gcons g51 gnil))))))) r52 d52 e52 c52 (by decide +kernel)
def c53 : Claim := (5, available 0x8e00001a07d0f600000009999999ba482d0c828e 1 inputs)
def r53 : List RE := [(0xc0000000700e600000000909090b200280c020c,2,0)]
def d53 : List Entry := [([],[0],[])]
def e53 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g53 : GoodC c53 := claim_sound [c32] (gcons g32 gnil) r53 d53 e53 c53 (by decide +kernel)
def c54 : Claim := (5, available 0xe83dc0000001d07e87b0000000000000000000 76 inputs)
def r54 : List RE := [(0xc83580000001906c86a0000000000000000000,77,0)]
def d54 : List Entry := [([],[0],[])]
def e54 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g54 : GoodC c54 := claim_sound [c39] (gcons g39 gnil) r54 d54 e54 c54 (by decide +kernel)
def c55 : Claim := (5, available 0x8e000000000000d03e87b555555579281906868e 1 inputs)
def r55 : List RE := [(0xc0000000000000038073050505071001804060c,2,0)]
def d55 : List Entry := [([],[0],[])]
def e55 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g55 : GoodC c55 := claim_sound [c33] (gcons g33 gnil) r55 d55 e55 c55 (by decide +kernel)
def c56 : Claim := (5, available 0xe83dfa0fd0f600000000000000000000000000 105 inputs)
def r56 : List RE := [(0xa82d720d90b400000000000000000000000000,106,0)]
def d56 : List Entry := [([],[0],[])]
def e56 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g56 : GoodC c56 := claim_sound [c44] (gcons g44 gnil) r56 d56 e56 c56 (by decide +kernel)
def c57 : Claim := (4, available 0x40060180000c060c60402000e000038000c80040 6 inputs)
def r57 : List RE := [(0x1800000060060002000c000030000080000,19,0)]
def d57 : List Entry := [([],[0],[])]
def e57 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g57 : GoodC c57 := claim_sound [c9] (gcons g9 gnil) r57 d57 e57 c57 (by decide +kernel)
def c58 : Claim := (4, available 0x400501418c0804000060300000e0038000006440 6 inputs)
def r58 : List RE := [(0x1400c0004000000300000c0030000000400,10,0)]
def d58 : List Entry := [([],[0],[])]
def e58 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g58 : GoodC c58 := claim_sound [c19] (gcons g19 gnil) r58 d58 e58 c58 (by decide +kernel)
def c59 : Claim := (3, available 0x40000000c60c0600000000a0a0a0028520c82040 6 inputs)
def r59 : List RE := []
def d59 : List Entry := [([4097],[],[]),([],[],[])]
def e59 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g59 : GoodC c59 := claim_sound [] gnil r59 d59 e59 c59 (by decide +kernel)
def c60 : Claim := (3, available 0x4000000000000006306030606060018310406440 6 inputs)
def r60 : List RE := []
def d60 : List Entry := [([4098],[],[]),([],[],[])]
def e60 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g60 : GoodC c60 := claim_sound [] gnil r60 d60 e60 c60 (by decide +kernel)
def c61 : Claim := (3, available 0x5100000000098c00000000000000868000000051 0 inputs)
def r61 : List RE := []
def d61 : List Entry := [([],[],[])]
def e61 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g61 : GoodC c61 := claim_sound [] gnil r61 d61 e61 c61 (by decide +kernel)
def c62 : Claim := (3, available 0x1900000000054a000000000000000000009c0019 0 inputs)
def r62 : List RE := []
def d62 : List Entry := [([],[],[])]
def e62 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g62 : GoodC c62 := claim_sound [] gnil r62 d62 e62 c62 (by decide +kernel)
def c63 : Claim := (3, available 0x5900000000000000000000003000248000540059 0 inputs)
def r63 : List RE := []
def d63 : List Entry := [([],[],[])]
def e63 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g63 : GoodC c63 := claim_sound [] gnil r63 d63 e63 c63 (by decide +kernel)
def c64 : Claim := (6, available 0x59000000000dce0000000000b000a68000dc0059 0 inputs)
def r64 : List RE := [(0x40000000000c060000000000a000028000c80040,6,0),(0x80000000000c600000000009000a200000c0008,3,1),(0x5100000000098c00000000000000868000000051,0,2),(0x1900000000054a000000000000000000009c0019,0,3),(0x5900000000000000000000003000248000540059,0,4)]
def d64 : List Entry := [([],[1,0,2,3,4],[0,1,2,3,4,5,6,7,8,9])]
def e64 : List (List Entry) := [[([23],[1],[]),([39],[0],[]),([55],[0],[0,1]),([71],[0],[2,3]),([303],[1],[4,5]),([319],[1],[]),([335],[1],[6,7]),([575],[2],[8,9]),([591],[2],[]),([847],[3],[])],[([55,56],[],[]),([55,60],[],[]),([71,72],[],[]),([71,76],[],[]),([303,48],[],[]),([303,52],[],[]),([335,80],[],[]),([335,84],[],[]),([575,80],[],[]),([575,84],[],[])]]
set_option maxRecDepth 100000 in
theorem g64 : GoodC c64 := claim_sound [c2,c26,c61,c62,c63] (gcons g2 (gcons g26 (gcons g61 (gcons g62 (gcons g63 gnil))))) r64 d64 e64 c64 (by decide +kernel)
def c65 : Claim := (7, available 0x59067380000dce0ce84e6000f000e78000dc0059 0 inputs)
def r65 : List RE := [(0x80031800000c60068062000d000e300000c0008,3,0),(0x59000000000dce0000000000b000a68000dc0059,0,1)]
def d65 : List Entry := [([],[0,1],[])]
def e65 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g65 : GoodC c65 := claim_sound [c25,c64] (gcons g25 (gcons g64 gnil)) r65 d65 e65 c65 (by decide +kernel)
def c66 : Claim := (4, available 0x5104630000098c00004c60000000c78000000051 0 inputs)
def r66 : List RE := [(0x5100000000098c00000000000000868000000051,0,0)]
def d66 : List Entry := [([],[0],[])]
def e66 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g66 : GoodC c66 := claim_sound [c61] (gcons g61 gnil) r66 d66 e66 c66 (by decide +kernel)
def c67 : Claim := (3, available 0x1902528000054a08c80a400000000000009c0019 0 inputs)
def r67 : List RE := []
def d67 : List Entry := [([4099],[],[]),([],[],[])]
def e67 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g67 : GoodC c67 := claim_sound [] gnil r67 d67 e67 c67 (by decide +kernel)
def c68 : Claim := (4, available 0x673800000000ce84e60000000000000000000 77 inputs)
def r68 : List RE := []
def d68 : List Entry := [([],[],[])]
def e68 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g68 : GoodC c68 := claim_sound [] gnil r68 d68 e68 c68 (by decide +kernel)
def c69 : Claim := (4, available 0x5900000000000004a84e60007000658000540059 0 inputs)
def r69 : List RE := []
def d69 : List Entry := [([],[],[])]
def e69 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g69 : GoodC c69 := claim_sound [] gnil r69 d69 e69 c69 (by decide +kernel)
def c70 : Claim := (4, available 0xd7000000000000b000b0000568002a00 9 inputs)
def r70 : List RE := []
def d70 : List Entry := [([],[],[])]
def e70 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g70 : GoodC c70 := claim_sound [] gnil r70 d70 e70 c70 (by decide +kernel)
def c71 : Claim := (3, available 0x5100000000000000004c60000000458000000051 0 inputs)
def r71 : List RE := []
def d71 : List Entry := [([],[],[])]
def e71 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g71 : GoodC c71 := claim_sound [] gnil r71 d71 e71 c71 (by decide +kernel)
def c72 : Claim := (3, available 0x1500000000000000002950000000000000004e15 0 inputs)
def r72 : List RE := []
def d72 : List Entry := [([],[],[])]
def e72 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g72 : GoodC c72 := claim_sound [] gnil r72 d72 e72 c72 (by decide +kernel)
def c73 : Claim := (3, available 0x5500000000000000000000000030148000002a55 0 inputs)
def r73 : List RE := []
def d73 : List Entry := [([],[],[])]
def e73 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g73 : GoodC c73 := claim_sound [] gnil r73 d73 e73 c73 (by decide +kernel)
def c74 : Claim := (6, available 0x5500000000000000006d70000070558000006e55 0 inputs)
def r74 : List RE := [(0x4000000000000000006030000060018000006440,6,0),(0x400000000000000000530000050510000000604,2,1),(0x5100000000000000004c60000000458000000051,0,2),(0x1500000000000000002950000000000000004e15,0,3),(0x5500000000000000000000000030148000002a55,0,4)]
def d74 : List Entry := [([],[1,0,2,3,4],[0,1,2,3,4,5,6,7,8,9])]
def e74 : List (List Entry) := [[([23],[1],[]),([39],[0],[]),([55],[0],[0,1]),([71],[0],[2,3]),([303],[1],[4,5]),([319],[1],[]),([335],[1],[6,7]),([575],[2],[8,9]),([591],[2],[]),([847],[3],[])],[([55,56],[],[]),([55,60],[],[]),([71,72],[],[]),([71,76],[],[]),([303,48],[],[]),([303,52],[],[]),([335,80],[],[]),([335,84],[],[]),([575,80],[],[]),([575,84],[],[])]]
set_option maxRecDepth 100000 in
theorem g74 : GoodC c74 := claim_sound [c4,c28,c71,c72,c73] (gcons g4 (gcons g28 (gcons g71 (gcons g72 (gcons g73 gnil))))) r74 d74 e74 c74 (by decide +kernel)
def c75 : Claim := (7, available 0x55056b419d09ac00006d700000f0d78000006e55 0 inputs)
def r75 : List RE := [(0x40029400d00a4000005300000d0d30000000604,2,0),(0x5500000000000000006d70000070558000006e55,0,1)]
def d75 : List Entry := [([],[0,1],[])]
def e75 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g75 : GoodC c75 := claim_sound [c27,c74] (gcons g27 (gcons g74 gnil)) r75 d75 e75 c75 (by decide +kernel)
def c76 : Claim := (3, available 0x15014a4119012800002950000000000000004e15 0 inputs)
def r76 : List RE := []
def d76 : List Entry := [([4100],[],[]),([],[],[])]
def e76 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g76 : GoodC c76 := claim_sound [] gnil r76 d76 e76 c76 (by decide +kernel)
def c77 : Claim := (4, available 0x550000009509ac000000000000b0968000002a55 0 inputs)
def r77 : List RE := []
def d77 : List Entry := [([],[],[])]
def e77 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g77 : GoodC c77 := claim_sound [] gnil r77 d77 e77 c77 (by decide +kernel)
def c78 : Claim := (4, available 0x56b419d09ac00000000000000000000000000 106 inputs)
def r78 : List RE := []
def d78 : List Entry := [([],[],[])]
def e78 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g78 : GoodC c78 := claim_sound [] gnil r78 d78 e78 c78 (by decide +kernel)
def c79 : Claim := (4, available 0x6b80000707000000358540000 18 inputs)
def r79 : List RE := []
def d79 : List Entry := [([],[],[])]
def e79 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g79 : GoodC c79 := claim_sound [] gnil r79 d79 e79 c79 (by decide +kernel)
def c80 : Claim := (4, available 0x1d00000053056a000000000000000004689c0a1d 0 inputs)
def r80 : List RE := [(0xc000000030062000000000000000000280c020c,2,0)]
def d80 : List Entry := [([],[0],[])]
def e80 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g80 : GoodC c80 := claim_sound [c30] (gcons g30 gnil) r80 d80 e80 c80 (by decide +kernel)
def c81 : Claim := (4, available 0x35ac00000000ad82b50000000000000000000 76 inputs)
def r81 : List RE := []
def d81 : List Entry := [([],[],[])]
def e81 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g81 : GoodC c81 := claim_sound [] gnil r81 d81 e81 c81 (by decide +kernel)
def c82 : Claim := (4, available 0x1d00000000000002982b50000000000258144e1d 0 inputs)
def r82 : List RE := [(0xc0000000000000018031000000000001804060c,2,0)]
def d82 : List Entry := [([],[0],[])]
def e82 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g82 : GoodC c82 := claim_sound [c31] (gcons g31 gnil) r82 d82 e82 c82 (by decide +kernel)
def c83 : Claim := (4, available 0x35ac15b056a00000000000000000000000000 105 inputs)
def r83 : List RE := []
def d83 : List Entry := [([],[],[])]
def e83 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g83 : GoodC c83 := claim_sound [] gnil r83 d83 e83 c83 (by decide +kernel)
def c84 : Claim := (6, available 0x1d035ac15b056a0ad82b500000000006789c4e1d 0 inputs)
def r84 : List RE := [(0xc0018c00b0062005803100000000000380c060c,2,0),(0x1900000000054a000000000000000000009c0019,0,1),(0x1500000000000000002950000000000000004e15,0,2),(0x1d00000053056a000000000000000004689c0a1d,0,3),(0x35ac00000000ad82b50000000000000000000,76,4),(0x1d00000000000002982b50000000000258144e1d,0,5),(0x35ac15b056a00000000000000000000000000,105,6)]
def d84 : List Entry := [([],[0,3,4,5,6,1,2],[0])]
def e84 : List (List Entry) := [[([29],[],[])]]
set_option maxRecDepth 100000 in
theorem g84 : GoodC c84 := claim_sound [c29,c62,c72,c80,c81,c82,c83] (gcons g29 (gcons g62 (gcons g72 (gcons g80 (gcons g81 (gcons g82 (gcons g83 gnil))))))) r84 d84 e84 c84 (by decide +kernel)
def c85 : Claim := (7, available 0x5d000000d70dee00000000b0b0b0b68568dc2a5d 0 inputs)
def r85 : List RE := [(0xc0000000700e600000000909090b200280c020c,2,0),(0x59000000000dce0000000000b000a68000dc0059,0,1)]
def d85 : List Entry := [([],[0,1],[])]
def e85 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g85 : GoodC c85 := claim_sound [c32,c64] (gcons g32 (gcons g64 gnil)) r85 d85 e85 c85 (by decide +kernel)
def c86 : Claim := (4, available 0x5d00000000000000000000303030348148542a5d 0 inputs)
def r86 : List RE := [(0x5900000000000000000000003000248000540059,0,0)]
def d86 : List Entry := [([],[0],[])]
def e86 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g86 : GoodC c86 := claim_sound [c63] (gcons g63 gnil) r86 d86 e86 c86 (by decide +kernel)
def c87 : Claim := (7, available 0x5d00000000000006b86f70707070758358546e5d 0 inputs)
def r87 : List RE := [(0xc0000000000000038073050505071001804060c,2,0),(0x5500000000000000006d70000070558000006e55,0,1)]
def d87 : List Entry := [([],[0,1],[])]
def e87 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g87 : GoodC c87 := claim_sound [c33,c74] (gcons g33 (gcons g74 gnil)) r87 d87 e87 c87 (by decide +kernel)
def c88 : Claim := (10, available 0x5d077bc1df0dee0ef86f70f0f0f0f78778dc6e5d 0 inputs)
def r88 : List RE := [(0x400701c1ce0c060e706030e0e0e0038730c86440,6,0),(0x1c00e000600700030c0c0c0030030080400,10,1),(0x40060180000c060c60402000e000038000c80040,6,2),(0x1ce000000000000e000e0000730006400,10,3),(0x400501418c0804000060300000e0038000006440,6,4),(0xe700000e0e000000730c80000,19,5),(0x40000000c60c0600000000a0a0a0028520c82040,6,6),(0x4000000000000006306030606060018310406440,6,7),(0xc0039c00f00e600780730d0d0d0f300380c060c,2,8),(0x80031800000c60068062000d000e300000c0008,3,9),(0x40029400d00a4000005300000d0d30000000604,2,10),(0xc0018c00b0062005803100000000000380c060c,2,11),(0xc0000000700e600000000909090b200280c020c,2,12),(0xc0000000000000038073050505071001804060c,2,13),(0x59067380000dce0ce84e6000f000e78000dc0059,0,14),(0x5104630000098c00004c60000000c78000000051,0,15),(0x1902528000054a08c80a400000000000009c0019,0,16),(0x59000000000dce0000000000b000a68000dc0059,0,17),(0x673800000000ce84e60000000000000000000,77,18),(0x5900000000000004a84e60007000658000540059,0,19),(0xd7000000000000b000b0000568002a00,9,20),(0x55056b419d09ac00006d700000f0d78000006e55,0,21),(0x15014a4119012800002950000000000000004e15,0,22),(0x550000009509ac000000000000b0968000002a55,0,23),(0x5500000000000000006d70000070558000006e55,0,24),(0x56b419d09ac00000000000000000000000000,106,25),(0x6b80000707000000358540000,18,26),(0x1d035ac15b056a0ad82b500000000006789c4e1d,0,27),(0x1d00000053056a000000000000000004689c0a1d,0,28),(0x35ac00000000ad82b50000000000000000000,76,29),(0x1d00000000000002982b50000000000258144e1d,0,30),(0x35ac15b056a00000000000000000000000000,105,31),(0x5d000000d70dee00000000b0b0b0b68568dc2a5d,0,32),(0x5d00000000000000000000303030348148542a5d,0,33),(0x5d00000000000006b86f70707070758358546e5d,0,34)]
def R88 : List RR := r88.map (resolve [c6,c1,c57,c3,c58,c5,c59,c60,c34,c25,c27,c29,c32,c33,c65,c66,c67,c64,c68,c69,c70,c75,c76,c77,c74,c78,c79,c84,c80,c81,c82,c83,c85,c86,c87] c88.2)
theorem hR88 : ∀ y ∈ R88, RInv c88.2.toFinset y := res_inv [c6,c1,c57,c3,c58,c5,c59,c60,c34,c25,c27,c29,c32,c33,c65,c66,c67,c64,c68,c69,c70,c75,c76,c77,c74,c78,c79,c84,c80,c81,c82,c83,c85,c86,c87] (gcons g6 (gcons g1 (gcons g57 (gcons g3 (gcons g58 (gcons g5 (gcons g59 (gcons g60 (gcons g34 (gcons g25 (gcons g27 (gcons g29 (gcons g32 (gcons g33 (gcons g65 (gcons g66 (gcons g67 (gcons g64 (gcons g68 (gcons g69 (gcons g70 (gcons g75 (gcons g76 (gcons g77 (gcons g74 (gcons g78 (gcons g79 (gcons g84 (gcons g80 (gcons g81 (gcons g82 (gcons g83 (gcons g85 (gcons g86 (gcons g87 gnil))))))))))))))))))))))))))))))))))) r88 c88.2
def k88_5_0 : List Entry := [([71,55,840,44,300],[],[]),([71,56,847,68,60],[],[]),([71,56,1391,80,60],[],[]),([87,574,350,68,76],[17],[]),([87,574,350,68,92],[],[]),([103,574,334,68,76],[24],[]),([103,574,334,68,92],[],[]),([303,382,98,88,332],[],[]),([303,382,98,124,332],[17],[]),([319,366,98,88,332],[],[]),([319,366,98,124,332],[24],[])]
set_option maxRecDepth 100000 in
theorem v88_5_0 : ∀ e ∈ k88_5_0, ¬ Live516.live basicOps goal 5 (wsOf c88.2 e).toFinset := level_sound hR88 5 k88_5_0 [] nil_dead (by decide +kernel)
def D88_5 : List Entry := k88_5_0
theorem w88_5 : ∀ e ∈ D88_5, ¬ Live516.live basicOps goal 5 (wsOf c88.2 e).toFinset := v88_5_0
def k88_6_0 : List Entry := [([23,62,82,88],[],[]),([23,62,82,92],[],[]),([23,62,86,76],[],[]),([23,62,118,92],[],[]),([23,78,82,88],[],[]),([23,78,82,92],[],[]),([23,78,86,76],[],[]),([23,78,102,92],[],[]),([23,83,24,60],[],[]),([23,86,70,76],[],[]),([23,86,70,108],[],[]),([23,86,86,76],[],[]),([23,86,86,124],[],[]),([23,86,102,76],[],[]),([23,86,102,92],[],[]),([23,86,118,76],[],[]),([23,86,118,108],[],[]),([23,90,296,29],[8],[]),([23,90,296,45],[],[]),([23,90,296,574],[],[]),([23,90,296,590],[],[]),([23,102,86,92],[],[]),([23,102,98,92],[],[]),([23,102,98,104],[],[]),([23,102,98,108],[],[]),([23,102,106,56],[],[]),([23,102,106,312],[],[]),([23,102,118,92],[],[]),([23,102,118,108],[],[]),([23,102,118,120],[],[]),([23,102,118,124],[],[]),([23,102,862,68],[],[]),([23,110,98,92],[],[]),([23,110,98,104],[],[]),([23,110,98,108],[],[]),([23,118,70,92],[],[]),([23,118,98,88],[],[]),([23,118,98,92],[],[]),([23,118,98,108],[],[]),([23,118,106,56],[],[]),([23,118,106,312],[],[]),([23,118,846,68],[],[]),([23,126,98,88],[],[]),([23,126,98,92],[],[]),([23,126,98,108],[],[]),([23,342,334,52],[3],[]),([23,342,350,52],[5],[]),([23,342,846,36],[3],[]),([23,342,862,36],[5],[]),([23,1383,56,76],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_0 : ∀ e ∈ k88_6_0, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_0 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_1 : List Entry := [([23,1399,56,76],[],[]),([23,1663,48,76],[],[]),([31,86,102,92],[],[]),([31,86,118,108],[],[]),([31,102,98,92],[],[]),([31,102,98,104],[],[]),([31,102,98,108],[],[]),([31,102,106,312],[],[]),([31,102,110,292],[],[]),([31,102,118,92],[],[]),([31,102,118,108],[],[]),([31,118,98,88],[],[]),([31,118,98,92],[],[]),([31,118,98,108],[],[]),([31,118,106,312],[],[]),([31,118,110,292],[],[]),([31,342,878,36],[],[]),([31,342,894,36],[],[]),([31,622,98,72],[],[]),([31,622,98,124],[],[]),([31,622,98,300],[],[]),([31,622,106,72],[],[]),([31,622,126,64],[],[]),([31,622,126,112],[],[]),([31,622,366,48],[],[]),([31,638,98,72],[],[]),([31,638,98,124],[],[]),([31,638,98,300],[],[]),([31,638,106,72],[],[]),([31,638,366,48],[],[]),([31,1391,84,72],[],[]),([31,1407,84,72],[],[]),([39,62,82,76],[],[]),([39,62,82,88],[],[]),([39,62,82,92],[],[]),([39,62,86,292],[],[]),([39,62,118,92],[],[]),([39,78,82,76],[],[]),([39,78,86,88],[],[]),([39,78,86,92],[],[]),([39,126,98,76],[],[]),([39,126,98,108],[],[]),([39,574,52,330],[],[]),([39,574,52,366],[],[]),([39,574,346,60],[],[]),([39,574,382,52],[],[]),([39,859,56,108],[],[]),([39,895,48,124],[],[]),([39,1399,56,88],[],[]),([39,1399,56,92],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_1 : ∀ e ∈ k88_6_1, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_1 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_2 : List Entry := [([39,1399,56,124],[],[]),([39,1407,56,88],[],[]),([39,1407,56,92],[],[]),([39,1407,56,108],[],[]),([39,1407,56,124],[],[]),([47,54,82,76],[],[]),([47,54,82,88],[],[]),([47,54,82,92],[],[]),([47,54,118,92],[],[]),([47,86,118,88],[],[]),([47,86,118,92],[],[]),([47,86,118,108],[],[]),([47,118,92,862],[],[]),([47,118,98,76],[],[]),([47,118,98,108],[],[]),([47,118,110,292],[],[]),([47,118,362,76],[],[]),([47,859,92,64],[],[]),([47,1399,56,88],[],[]),([47,1399,56,92],[],[]),([47,1399,92,64],[],[]),([55,62,82,76],[],[]),([55,62,82,88],[],[]),([55,62,82,92],[],[]),([55,62,86,292],[],[]),([55,62,102,92],[],[]),([55,78,82,76],[],[]),([55,78,86,88],[],[]),([55,78,86,92],[],[]),([55,110,98,76],[],[]),([55,110,98,108],[],[]),([55,574,52,330],[],[]),([55,574,52,350],[],[]),([55,574,346,60],[],[]),([55,574,366,52],[],[]),([55,859,56,124],[],[]),([55,879,48,124],[],[]),([55,1383,56,88],[],[]),([55,1383,56,92],[],[]),([55,1383,56,124],[],[]),([55,1391,56,88],[],[]),([55,1391,56,92],[],[]),([55,1391,56,108],[],[]),([55,1391,56,124],[],[]),([63,54,82,76],[],[]),([63,54,82,88],[],[]),([63,54,82,92],[],[]),([63,54,102,92],[],[]),([63,86,102,88],[],[]),([63,86,102,92],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_2 : ∀ e ∈ k88_6_2, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_2 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_3 : List Entry := [([63,86,102,108],[],[]),([63,102,92,862],[],[]),([63,102,98,76],[],[]),([63,102,98,108],[],[]),([63,102,110,292],[],[]),([63,102,362,76],[],[]),([63,859,92,64],[],[]),([63,1383,56,88],[],[]),([63,1383,56,92],[],[]),([63,1383,92,64],[],[]),([67,300,20,23],[0,8],[]),([67,300,20,31],[0,8],[]),([67,1119,52,88],[],[]),([67,1119,52,92],[],[]),([71,55,840,28],[0,8],[]),([71,55,840,44],[0],[0]),([71,55,840,316],[],[0]),([71,56,343,92],[],[]),([71,56,359,108],[],[]),([71,56,575,100],[],[]),([71,56,591,116],[],[]),([71,56,847,64],[],[]),([71,56,847,68],[],[1]),([71,56,1391,80],[],[2]),([71,56,1391,84],[],[]),([71,57,326,44],[],[]),([71,57,326,108],[],[]),([71,57,342,44],[],[]),([71,57,342,124],[],[]),([71,57,358,44],[],[]),([71,57,358,92],[],[]),([71,57,374,44],[],[]),([71,57,374,108],[],[]),([71,57,568,44],[0,8],[]),([71,57,568,46],[0],[0]),([71,57,614,72],[],[]),([71,57,630,72],[],[]),([71,57,846,68],[],[]),([71,57,862,68],[],[]),([71,60,55,108],[],[]),([71,60,71,124],[],[]),([71,60,87,92],[],[]),([71,60,103,108],[],[]),([71,60,343,92],[],[]),([71,60,359,108],[],[]),([71,60,575,100],[],[]),([71,60,591,116],[],[]),([71,61,326,40],[],[]),([71,61,326,108],[],[]),([71,61,342,40],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_3 : ∀ e ∈ k88_6_3, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_3 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_4 : List Entry := [([71,61,342,124],[],[]),([71,61,358,40],[],[]),([71,61,358,92],[],[]),([71,61,374,40],[],[]),([71,61,374,108],[],[]),([71,61,568,30],[1],[]),([71,61,568,44],[],[]),([71,61,568,46],[0,8],[]),([71,61,614,72],[],[]),([71,61,630,72],[],[]),([71,61,846,68],[],[]),([71,61,862,68],[],[]),([71,62,70,108],[],[]),([71,62,86,124],[],[]),([71,62,102,92],[],[]),([71,62,118,108],[],[]),([71,63,588,52],[],[]),([71,63,840,28],[8],[]),([71,63,840,44],[0],[]),([71,63,840,60],[8],[]),([71,78,118,108],[],[]),([71,94,102,108],[],[]),([71,110,102,124],[],[]),([71,126,86,124],[],[]),([71,296,30,38],[0,8],[]),([71,358,56,46],[],[]),([71,358,56,62],[],[]),([71,358,846,36],[29],[]),([71,358,878,36],[5],[]),([71,374,56,46],[],[]),([71,374,56,62],[],[]),([71,374,846,36],[31],[]),([71,374,862,36],[3],[]),([71,566,78,68],[],[]),([71,566,94,68],[],[]),([71,566,334,52],[],[]),([71,566,350,52],[],[]),([71,574,52,46],[8],[]),([71,574,52,350],[],[]),([71,574,52,366],[],[]),([71,574,78,52],[],[]),([71,574,78,68],[],[]),([71,574,94,52],[],[]),([71,574,94,68],[],[]),([71,574,366,52],[29],[]),([71,574,382,52],[31],[]),([71,590,52,46],[],[]),([71,590,52,62],[],[]),([71,606,52,46],[],[]),([71,606,52,62],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_4 : ∀ e ∈ k88_6_4, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_4 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_5 : List Entry := [([71,847,52,88],[],[]),([71,847,52,92],[],[]),([71,863,52,88],[],[]),([71,863,52,92],[],[]),([71,879,52,120],[],[]),([71,879,52,124],[],[]),([71,895,52,120],[],[]),([71,895,52,124],[],[]),([71,1119,48,88],[],[]),([71,1119,48,92],[],[]),([71,1119,68,72],[],[]),([71,1119,68,92],[3,5],[1]),([71,1119,68,108],[3,5],[]),([71,1119,68,124],[3,5],[]),([71,1151,48,88],[],[]),([71,1151,48,92],[],[]),([71,1391,48,88],[],[]),([71,1391,48,92],[],[]),([71,1663,48,88],[],[]),([71,1663,48,92],[],[]),([71,1663,80,76],[],[]),([71,1663,80,92],[29,31],[2]),([71,1663,80,108],[29,31],[]),([71,1663,80,124],[29,31],[]),([79,1663,48,88],[],[]),([79,1663,48,92],[],[]),([87,62,118,108],[],[]),([87,76,359,108],[],[]),([87,76,1119,116],[],[]),([87,94,102,88],[],[]),([87,94,102,92],[],[]),([87,98,42,72],[],[]),([87,110,110,116],[],[]),([87,126,298,60],[],[]),([87,574,86,124],[],[]),([87,574,350,52],[],[]),([87,574,350,68],[17],[3,4]),([87,618,110,116],[],[]),([87,863,48,92],[],[]),([87,863,68,92],[17],[3]),([87,863,68,108],[],[4]),([87,895,48,92],[],[]),([87,895,52,76],[],[]),([87,895,92,68],[],[]),([87,895,92,112],[17],[]),([103,62,118,92],[],[]),([103,78,102,88],[],[]),([103,78,102,92],[],[]),([103,92,1119,116],[],[]),([103,98,42,72],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_5 : ∀ e ∈ k88_6_5, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_5 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_6 : List Entry := [([103,110,94,116],[],[]),([103,574,70,124],[],[]),([103,574,334,52],[],[]),([103,574,334,68],[24],[5,6]),([103,618,94,116],[],[]),([103,847,48,92],[],[]),([103,847,68,92],[24],[5]),([103,847,68,108],[],[6]),([103,895,48,108],[],[]),([103,895,52,76],[],[]),([103,895,92,68],[],[]),([103,895,92,112],[24],[]),([303,54,76,586],[],[]),([303,54,76,622],[],[5]),([303,54,92,37],[],[]),([303,54,92,622],[],[6]),([303,54,94,308],[],[]),([303,62,82,88],[],[]),([303,62,82,92],[],[]),([303,62,86,308],[],[]),([303,62,118,92],[],[]),([303,78,68,334],[24],[]),([303,78,68,586],[],[]),([303,78,82,44],[],[]),([303,78,82,300],[],[]),([303,78,86,60],[],[]),([303,78,86,308],[],[]),([303,94,638,48],[],[]),([303,118,92,862],[],[]),([303,126,98,108],[],[]),([303,382,98,88],[],[7]),([303,382,98,124],[],[8]),([303,382,98,300],[],[]),([303,382,98,332],[17],[7,8]),([303,382,366,48],[],[]),([303,382,878,32],[],[]),([303,1119,56,124],[],[]),([303,1119,60,80],[],[]),([303,1119,60,84],[],[]),([303,1119,60,100],[],[]),([303,1119,60,116],[],[]),([303,1399,60,116],[],[]),([303,1407,56,108],[],[]),([303,1407,60,116],[],[]),([319,54,76,586],[],[]),([319,54,76,606],[],[3]),([319,54,92,37],[],[]),([319,54,92,606],[],[4]),([319,54,94,308],[],[]),([319,62,82,88],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_6 : ∀ e ∈ k88_6_6, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_6 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_7 : List Entry := [([319,62,82,92],[],[]),([319,62,86,308],[],[]),([319,62,102,92],[],[]),([319,94,622,48],[],[]),([319,102,92,862],[],[]),([319,110,98,108],[],[]),([319,366,98,88],[],[9]),([319,366,98,124],[],[10]),([319,366,98,300],[],[]),([319,366,98,332],[24],[9,10]),([319,366,366,48],[],[]),([319,366,878,32],[],[]),([319,1119,48,28],[],[]),([319,1119,56,108],[],[]),([319,1119,316,32],[],[]),([319,1119,316,84],[17],[]),([319,1383,60,116],[],[]),([319,1391,56,108],[],[]),([319,1391,60,116],[],[]),([331,78,78,100],[],[]),([331,78,78,112],[],[]),([331,78,78,116],[],[]),([331,78,94,100],[],[]),([331,78,94,116],[],[]),([331,94,78,96],[],[]),([331,94,78,100],[],[]),([331,94,78,116],[],[]),([335,70,78,100],[],[]),([335,70,78,112],[],[]),([335,70,78,116],[],[]),([335,86,78,96],[],[]),([335,86,78,100],[],[]),([335,86,78,116],[],[]),([335,102,78,112],[],[]),([335,102,78,116],[],[]),([335,102,110,116],[],[]),([335,118,78,112],[],[]),([335,118,78,116],[],[]),([335,118,94,116],[],[]),([351,98,72,45],[],[]),([351,98,72,350],[],[9]),([351,98,124,366],[24],[10]),([351,106,78,112],[],[]),([351,106,78,116],[],[]),([351,106,110,116],[],[]),([351,1391,56,124],[],[]),([367,98,72,45],[],[]),([367,98,72,334],[],[7]),([367,98,124,350],[17],[8]),([367,106,78,112],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_7 : ∀ e ∈ k88_6_7, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_7 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_8 : List Entry := [([367,106,78,116],[],[]),([367,106,94,116],[],[]),([367,1135,56,124],[],[]),([575,62,86,88],[],[]),([575,62,86,92],[],[]),([575,70,90,88],[],[]),([575,70,90,92],[],[]),([591,50,118,108],[],[]),([591,62,54,72],[],[]),([591,70,94,116],[],[]),([591,86,318,52],[],[]),([591,100,607,116],[],[]),([591,118,74,88],[],[]),([591,118,74,92],[],[]),([847,50,102,108],[],[]),([847,62,54,72],[],[]),([847,70,94,100],[],[]),([847,102,74,88],[],[]),([847,102,74,92],[],[]),([1111,78,78,68],[],[]),([1111,78,78,112],[],[]),([1111,78,78,116],[],[]),([1111,110,78,68],[],[]),([1111,110,78,116],[],[]),([1119,70,78,68],[],[]),([1119,70,78,112],[],[]),([1119,70,78,116],[],[]),([1119,70,110,116],[],[]),([1119,102,78,68],[],[]),([1119,102,78,116],[],[]),([1119,118,74,88],[],[]),([1119,118,74,92],[],[]),([1119,118,78,68],[],[]),([1127,78,78,68],[],[]),([1127,78,78,112],[],[]),([1127,78,78,116],[],[]),([1127,94,78,68],[],[]),([1127,94,78,116],[],[]),([1135,70,78,68],[],[]),([1135,70,78,112],[],[]),([1135,70,78,116],[],[]),([1135,70,94,116],[],[]),([1135,86,78,68],[],[]),([1135,86,78,116],[],[]),([1135,118,74,88],[],[]),([1135,118,74,92],[],[]),([1135,118,78,68],[],[]),([1391,70,78,112],[],[]),([1391,70,78,116],[],[]),([1391,122,74,88],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_8 : ∀ e ∈ k88_6_8, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_8 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def k88_6_9 : List Entry := [([1391,122,74,92],[],[])]
set_option maxRecDepth 100000 in
theorem v88_6_9 : ∀ e ∈ k88_6_9, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := level_sound hR88 6 k88_6_9 (D88_5.map (wsOf c88.2)) (map_dead w88_5) (by decide +kernel)
def D88_6 : List Entry := k88_6_0 ++ (k88_6_1 ++ (k88_6_2 ++ (k88_6_3 ++ (k88_6_4 ++ (k88_6_5 ++ (k88_6_6 ++ (k88_6_7 ++ (k88_6_8 ++ (k88_6_9)))))))))
theorem w88_6 : ∀ e ∈ D88_6, ¬ Live516.live basicOps goal 6 (wsOf c88.2 e).toFinset := (app_dead v88_6_0 (app_dead v88_6_1 (app_dead v88_6_2 (app_dead v88_6_3 (app_dead v88_6_4 (app_dead v88_6_5 (app_dead v88_6_6 (app_dead v88_6_7 (app_dead v88_6_8 v88_6_9)))))))))
def k88_7_0 : List Entry := [([23,54,78],[8],[]),([23,54,90],[8],[]),([23,54,94],[8],[]),([23,54,126],[8],[]),([23,62,70],[8],[]),([23,62,82],[8,3],[0,1]),([23,62,86],[8],[2]),([23,62,118],[8,24],[3]),([23,70,78],[8],[]),([23,70,90],[8],[]),([23,70,94],[8],[]),([23,70,110],[8],[]),([23,78,70],[8],[]),([23,78,82],[8,5],[4,5]),([23,78,86],[8],[6]),([23,78,102],[8,17],[7]),([23,82,42],[0],[]),([23,82,72],[8,14],[]),([23,82,76],[],[]),([23,82,78],[8],[]),([23,82,88],[8,21],[]),([23,82,92],[],[]),([23,82,94],[8],[]),([23,82,110],[8],[]),([23,82,126],[8],[]),([23,82,846],[14],[]),([23,82,862],[21],[]),([23,83,24],[8],[8]),([23,83,56],[0,27],[]),([23,83,76],[8,27],[]),([23,83,88],[8],[]),([23,83,92],[8],[]),([23,83,104],[8],[]),([23,83,108],[8],[]),([23,86,60],[],[]),([23,86,61],[8,1,11],[]),([23,86,70],[8,17],[9,10]),([23,86,78],[8],[]),([23,86,86],[8,24],[11,12]),([23,86,94],[8],[]),([23,86,102],[8,17],[13,14]),([23,86,110],[8],[]),([23,86,118],[8,24],[15,16]),([23,86,126],[8],[]),([23,87,76],[8,1],[]),([23,90,78],[8],[]),([23,90,94],[8],[]),([23,90,110],[8],[]),([23,90,126],[8],[]),([23,90,296],[8,27],[17,18,19,20])]
set_option maxRecDepth 100000 in
theorem v88_7_0 : ∀ e ∈ k88_7_0, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_0 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_1 : List Entry := [([23,90,846],[14,8],[19]),([23,90,862],[21,8],[20]),([23,94,70],[8],[]),([23,94,86],[8],[]),([23,94,102],[8],[]),([23,94,118],[8],[]),([23,102,61],[8,1,12],[]),([23,102,76],[],[]),([23,102,77],[14,8],[]),([23,102,86],[8,17],[21]),([23,102,94],[8],[]),([23,102,98],[8,17],[22,23,24]),([23,102,106],[8],[25,26]),([23,102,110],[8],[]),([23,102,118],[8,17,24],[27,28,29,30]),([23,102,126],[8],[]),([23,102,614],[],[25,26]),([23,102,622],[],[]),([23,102,862],[21],[31]),([23,103,76],[8,1],[]),([23,103,92],[8],[]),([23,110,86],[8],[]),([23,110,98],[8,32,17],[32,33,34]),([23,110,102],[8],[]),([23,110,118],[8],[]),([23,110,614],[],[]),([23,110,862],[1],[]),([23,118,61],[8,1,13],[]),([23,118,70],[8,24],[35]),([23,118,78],[8],[]),([23,118,92],[],[]),([23,118,93],[21,8],[]),([23,118,98],[8,24],[36,37,38]),([23,118,106],[8],[39,40]),([23,118,110],[8],[]),([23,118,126],[8],[]),([23,118,614],[],[39,40]),([23,118,622],[],[]),([23,118,846],[14],[41]),([23,119,76],[8,1],[]),([23,119,108],[8],[]),([23,126,70],[8],[]),([23,126,98],[8,34,24],[42,43,44]),([23,126,102],[8],[]),([23,126,118],[8],[]),([23,126,614],[],[]),([23,126,846],[1],[]),([23,339,24],[8,27],[]),([23,339,88],[0],[]),([23,339,92],[0],[])]
set_option maxRecDepth 100000 in
theorem v88_7_1 : ∀ e ∈ k88_7_1, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_1 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_2 : List Entry := [([23,339,104],[0],[]),([23,339,108],[0],[]),([23,342,61],[8],[18]),([23,342,326],[],[]),([23,342,334],[3],[45]),([23,342,342],[],[]),([23,342,350],[5],[46]),([23,342,846],[3,8],[47,19]),([23,342,862],[5,8],[48,20]),([23,359,92],[0],[]),([23,375,108],[0],[]),([23,574,52],[0,1,14,3],[41]),([23,574,70],[],[]),([23,590,52],[0,1,21,5],[31]),([23,590,70],[],[]),([23,847,48],[8],[]),([23,847,52],[3],[]),([23,859,56],[8],[]),([23,859,60],[],[]),([23,859,72],[8],[]),([23,859,76],[],[]),([23,863,48],[3],[]),([23,863,52],[3],[45]),([23,863,116],[8],[]),([23,895,48],[8],[]),([23,895,52],[],[]),([23,1115,56],[8],[]),([23,1115,60],[],[]),([23,1115,72],[8],[]),([23,1115,76],[],[]),([23,1119,48],[5],[]),([23,1119,52],[5],[46]),([23,1119,132],[8],[]),([23,1135,48],[8],[]),([23,1135,52],[],[]),([23,1383,56],[8],[49]),([23,1383,60],[],[]),([23,1383,72],[8],[]),([23,1383,76],[],[]),([23,1391,48],[8],[]),([23,1391,52],[],[]),([23,1391,60],[8],[]),([23,1399,56],[8],[50]),([23,1399,60],[],[]),([23,1399,72],[8],[]),([23,1399,76],[],[]),([23,1407,48],[8],[]),([23,1407,52],[],[]),([23,1407,60],[8],[]),([23,1663,48],[8],[51])]
set_option maxRecDepth 100000 in
theorem v88_7_2 : ∀ e ∈ k88_7_2, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_2 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_3 : List Entry := [([23,1663,52],[],[]),([23,1663,60],[8],[]),([31,54,858],[],[]),([31,54,894],[],[]),([31,70,858],[],[]),([31,70,878],[],[]),([31,82,72],[0,14],[]),([31,82,76],[],[]),([31,82,88],[0,21],[]),([31,82,92],[],[]),([31,82,110],[0],[]),([31,82,126],[0],[]),([31,86,61],[0],[]),([31,86,102],[0,17],[13,52]),([31,86,110],[0],[]),([31,86,118],[0,24],[15,53]),([31,86,126],[0],[]),([31,86,308],[0,27,1],[]),([31,86,878],[32],[]),([31,86,894],[34],[]),([31,102,76],[],[]),([31,102,98],[0,17],[54,55,56]),([31,102,106],[0,32],[57]),([31,102,110],[0],[58]),([31,102,118],[0,17,24],[59,60]),([31,102,126],[0],[]),([31,102,362],[0,17],[58]),([31,102,382],[0,34,17],[]),([31,102,614],[],[57]),([31,118,92],[],[]),([31,118,98],[0,24],[61,62,63]),([31,118,106],[0,34],[64]),([31,118,110],[0],[65]),([31,118,126],[0],[]),([31,118,362],[0,24],[65]),([31,118,382],[0,32,24],[]),([31,118,614],[],[64]),([31,342,61],[8,11,0],[]),([31,342,308],[0,27,1,11],[]),([31,342,878],[],[66]),([31,342,894],[],[67]),([31,602,56],[0,11],[]),([31,602,110],[],[]),([31,602,126],[],[]),([31,622,48],[0,12],[]),([31,622,98],[8],[68,69,70]),([31,622,106],[],[49,71]),([31,622,118],[],[]),([31,622,126],[],[51,72,73]),([31,622,366],[8],[74,70])]
set_option maxRecDepth 100000 in
theorem v88_7_3 : ∀ e ∈ k88_7_3, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_3 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_4 : List Entry := [([31,638,48],[0,13],[]),([31,638,98],[8],[75,76,77]),([31,638,106],[],[50,78]),([31,638,118],[],[]),([31,638,366],[8],[79,77]),([31,1383,56],[27],[]),([31,1383,72],[8],[]),([31,1391,48],[],[74]),([31,1391,84],[],[13,80]),([31,1399,56],[27],[]),([31,1399,72],[8],[]),([31,1407,48],[],[79]),([31,1407,84],[],[15,81]),([31,1663,48],[],[51]),([39,62,70],[8],[]),([39,62,82],[8],[82,83,84]),([39,62,86],[8],[9,85]),([39,62,118],[8,24],[86]),([39,62,346],[],[9,85]),([39,62,382],[34],[]),([39,70,78],[8],[]),([39,70,90],[14],[]),([39,70,94],[14],[]),([39,78,70],[8],[]),([39,78,82],[14,5],[87]),([39,78,86],[14],[88,89]),([39,82,60],[],[]),([39,82,78],[8],[]),([39,82,88],[],[]),([39,82,92],[],[]),([39,82,94],[14],[]),([39,82,126],[14],[]),([39,86,72],[8],[]),([39,86,76],[],[]),([39,86,78],[8,14],[]),([39,86,94],[14],[]),([39,86,108],[],[]),([39,86,126],[14],[]),([39,90,78],[8],[]),([39,90,94],[14],[]),([39,90,126],[14],[]),([39,94,70],[8],[]),([39,94,86],[14],[]),([39,94,118],[14],[]),([39,94,846],[8],[]),([39,94,862],[2],[]),([39,118,78],[8],[]),([39,118,92],[],[]),([39,118,106],[14],[]),([39,118,110],[14],[])]
set_option maxRecDepth 100000 in
theorem v88_7_4 : ∀ e ∈ k88_7_4, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_4 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_5 : List Entry := [([39,126,70],[8],[]),([39,126,98],[14,34,24],[90,91]),([39,126,102],[14],[]),([39,339,104],[0],[]),([39,339,108],[0],[]),([39,343,88],[0],[]),([39,343,92],[0],[]),([39,375,108],[0],[]),([39,574,52],[0,2,8,17],[92,93]),([39,574,70],[],[]),([39,574,346],[8],[94,92]),([39,574,382],[8],[95,93]),([39,590,52],[0,2,21,5,3],[]),([39,590,70],[],[]),([39,847,48],[8],[]),([39,847,52],[5],[]),([39,859,56],[8,17],[9,96]),([39,859,60],[],[94]),([39,863,48],[8],[]),([39,863,52],[],[]),([39,863,60],[8],[]),([39,895,48],[34,17],[97]),([39,895,52],[],[95]),([39,895,60],[8],[]),([39,1115,56],[14],[]),([39,1115,60],[14],[]),([39,1119,48],[5],[]),([39,1119,52],[5],[]),([39,1119,132],[14],[]),([39,1399,56],[14,17],[98,99,100]),([39,1399,60],[],[]),([39,1407,48],[14],[]),([39,1407,52],[],[]),([39,1407,56],[14,24,17],[101,102,103,104]),([39,1407,60],[14],[]),([47,54,82],[0],[105,106,107]),([47,54,86],[0],[2]),([47,54,118],[0,24],[108]),([47,54,862],[17],[]),([47,70,862],[17],[]),([47,82,78],[0],[]),([47,82,88],[0,21],[]),([47,82,92],[14,27],[]),([47,82,126],[0],[]),([47,82,316],[0,2,3,27,17],[]),([47,82,334],[],[]),([47,86,72],[8],[]),([47,86,73],[0],[2]),([47,86,76],[],[]),([47,86,77],[8,0],[])]
set_option maxRecDepth 100000 in
theorem v88_7_5 : ∀ e ∈ k88_7_5, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_5 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_6 : List Entry := [([47,86,78],[0],[]),([47,86,118],[0,24],[109,110,111]),([47,86,126],[0],[]),([47,86,326],[8],[]),([47,86,334],[0,8],[]),([47,118,78],[0],[]),([47,118,92],[14],[112]),([47,118,98],[0,24],[113,114]),([47,118,106],[0,34],[]),([47,118,110],[0],[115]),([47,118,334],[0,8,24],[]),([47,118,362],[0,24],[116,115]),([47,118,878],[],[112]),([47,606,48],[0,3],[]),([47,859,56],[0],[]),([47,859,92],[27,17],[117]),([47,863,48],[],[]),([47,895,48],[0],[]),([47,1399,56],[],[118,119]),([47,1399,92],[27,17],[120,116]),([47,1407,48],[],[]),([55,62,70],[8],[]),([55,62,82],[8],[121,122,123]),([55,62,86],[8],[11,124]),([55,62,102],[8,17],[125]),([55,62,346],[],[11,124]),([55,62,366],[32],[]),([55,78,70],[8],[]),([55,78,82],[14,3],[126]),([55,78,86],[14],[127,128]),([55,82,60],[],[]),([55,82,78],[8],[]),([55,82,88],[],[]),([55,82,92],[],[]),([55,82,94],[14,21],[]),([55,82,110],[21],[]),([55,86,72],[8],[]),([55,86,76],[],[]),([55,86,78],[8,21],[]),([55,86,94],[14],[]),([55,86,110],[21],[]),([55,86,124],[],[]),([55,90,78],[8],[]),([55,90,94],[14],[]),([55,90,110],[21],[]),([55,94,70],[8],[]),([55,94,86],[14],[]),([55,94,102],[21],[]),([55,94,846],[8],[]),([55,94,862],[4],[])]
set_option maxRecDepth 100000 in
theorem v88_7_6 : ∀ e ∈ k88_7_6, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_6 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_7 : List Entry := [([55,102,78],[8],[]),([55,102,92],[],[]),([55,102,106],[21],[]),([55,102,110],[21],[]),([55,110,70],[8],[]),([55,110,98],[21,32,17],[129,130]),([55,110,102],[21],[]),([55,339,104],[0],[]),([55,339,108],[0],[]),([55,343,88],[0],[]),([55,343,92],[0],[]),([55,359,108],[0],[]),([55,574,52],[0,4,8,24],[131,132]),([55,574,70],[],[]),([55,574,346],[8],[133,131]),([55,574,366],[8],[134,132]),([55,590,52],[0,4,14,3,5],[]),([55,590,70],[],[]),([55,847,48],[8],[]),([55,847,52],[3],[]),([55,859,56],[8,24],[11,135]),([55,859,60],[],[133]),([55,863,48],[8],[]),([55,863,52],[],[]),([55,863,60],[8],[]),([55,879,48],[32,24],[136]),([55,879,52],[],[134]),([55,879,60],[8],[]),([55,1115,56],[14,21],[]),([55,1115,60],[21],[]),([55,1119,48],[3],[]),([55,1119,52],[3],[]),([55,1119,116],[14,21],[]),([55,1383,56],[21,24],[137,138,139]),([55,1383,60],[],[]),([55,1391,48],[21],[]),([55,1391,52],[],[]),([55,1391,56],[21,17,24],[140,141,142,143]),([55,1391,60],[21],[]),([63,54,82],[0],[144,145,146]),([63,54,86],[0],[6]),([63,54,102],[0,17],[147]),([63,54,862],[24],[]),([63,70,862],[24],[]),([63,82,78],[0],[]),([63,82,88],[0,14],[]),([63,82,92],[21,27],[]),([63,82,110],[0],[]),([63,82,316],[0,4,5,27,24],[]),([63,82,334],[],[])]
set_option maxRecDepth 100000 in
theorem v88_7_7 : ∀ e ∈ k88_7_7, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_7 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_8 : List Entry := [([63,86,72],[8],[]),([63,86,73],[0],[6]),([63,86,76],[],[]),([63,86,77],[8,0],[]),([63,86,78],[0],[]),([63,86,102],[0,17],[148,149,150]),([63,86,110],[0],[]),([63,86,326],[8],[]),([63,86,334],[0,8],[]),([63,102,78],[0],[]),([63,102,92],[21],[151]),([63,102,98],[0,17],[152,153]),([63,102,106],[0,32],[]),([63,102,110],[0],[154]),([63,102,334],[0,8,17],[]),([63,102,362],[0,17],[155,154]),([63,102,878],[],[151]),([63,606,48],[0,5],[]),([63,859,56],[0],[]),([63,859,92],[27,24],[156]),([63,863,48],[],[]),([63,879,48],[0],[]),([63,1383,56],[],[157,158]),([63,1383,92],[27,24],[159,155]),([63,1391,48],[],[]),([67,26,56],[8],[]),([67,26,57],[0],[8]),([67,26,61],[8,0],[]),([67,26,62],[0],[]),([67,26,574],[0,8],[]),([67,62,78],[8],[]),([67,62,94],[8],[]),([67,72,847],[8],[]),([67,76,55],[8],[]),([67,76,71],[21],[]),([67,76,847],[8],[]),([67,78,70],[8],[]),([67,78,86],[14,21],[]),([67,88,847],[8],[]),([67,92,55],[8],[]),([67,92,71],[14],[]),([67,92,847],[8],[]),([67,94,70],[8],[]),([67,94,86],[14],[]),([67,300,20],[8,14,3,21,5,32,29,34,31],[160,161]),([67,574,78],[],[]),([67,574,94],[],[]),([67,590,70],[],[]),([67,590,86],[],[]),([67,606,70],[],[])]
set_option maxRecDepth 100000 in
theorem v88_7_8 : ∀ e ∈ k88_7_8, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_8 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_9 : List Entry := [([67,606,86],[],[]),([67,847,52],[14,27,3],[]),([67,863,52],[21,27,5],[]),([67,1119,52],[14,27,3,5],[162,163]),([71,55,840],[0,8],[164,165,166]),([71,56,343],[0,17],[167]),([71,56,359],[0,24],[168]),([71,56,575],[8,17],[169]),([71,56,591],[8,24],[170]),([71,56,607],[8,27],[]),([71,56,623],[8,27],[]),([71,56,847],[8,14],[171,172]),([71,56,879],[8,14],[]),([71,56,1119],[8,21],[]),([71,56,1391],[8,32],[173,174]),([71,57,326],[8,17],[175,176]),([71,57,334],[8],[]),([71,57,342],[8,24],[177,178]),([71,57,350],[8],[]),([71,57,358],[8,17],[179,180]),([71,57,366],[8],[]),([71,57,374],[8,24],[181,182]),([71,57,382],[8],[]),([71,57,568],[0,8],[183,184,166]),([71,57,614],[32],[185]),([71,57,622],[],[]),([71,57,630],[34],[186]),([71,57,638],[],[]),([71,57,838],[],[]),([71,57,846],[14],[187]),([71,57,854],[],[]),([71,57,862],[21],[188]),([71,60,19],[0],[]),([71,60,55],[14,17],[189]),([71,60,63],[14],[]),([71,60,71],[21,24],[190]),([71,60,79],[21],[]),([71,60,87],[32,17],[191]),([71,60,95],[32],[]),([71,60,103],[34,24],[192]),([71,60,111],[34],[]),([71,60,343],[0,17],[193]),([71,60,359],[0,24],[194]),([71,60,575],[14,17],[195]),([71,60,591],[21,24],[196]),([71,60,607],[27],[]),([71,60,623],[27],[]),([71,60,847],[14],[]),([71,60,879],[14],[]),([71,60,1119],[21],[])]
set_option maxRecDepth 100000 in
theorem v88_7_9 : ∀ e ∈ k88_7_9, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_9 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_10 : List Entry := [([71,60,1391],[32],[]),([71,61,57],[1,0],[]),([71,61,326],[14,17],[197,198]),([71,61,334],[14],[]),([71,61,342],[21,24],[199,200]),([71,61,350],[21],[]),([71,61,358],[32,17],[201,202]),([71,61,366],[32],[]),([71,61,374],[34,24],[203,204]),([71,61,382],[34],[]),([71,61,568],[0,8],[205,206,207]),([71,61,614],[32],[208]),([71,61,622],[],[]),([71,61,630],[34],[209]),([71,61,638],[],[]),([71,61,838],[],[]),([71,61,846],[14],[210]),([71,61,854],[],[]),([71,61,862],[21],[211]),([71,62,70],[8,14,17],[212]),([71,62,78],[8],[]),([71,62,86],[8,21,24],[213]),([71,62,94],[8],[]),([71,62,102],[8,32,17],[214]),([71,62,110],[8],[]),([71,62,118],[8,34,24],[215]),([71,62,126],[8],[]),([71,62,318],[8,11],[]),([71,62,334],[8,14],[]),([71,62,350],[8,21],[]),([71,62,366],[8,32],[]),([71,62,382],[8,34],[]),([71,63,588],[8],[216]),([71,63,840],[0,8],[217,218,219]),([71,71,56],[0,3],[]),([71,71,88],[8,3],[8]),([71,71,92],[8,14,3],[]),([71,71,124],[14,3],[176,198]),([71,78,70],[8],[]),([71,78,86],[14],[]),([71,78,118],[14,24],[220]),([71,87,56],[0,5],[]),([71,87,88],[8,5],[8]),([71,87,92],[8,21,5],[]),([71,87,140],[21,5],[178,200]),([71,94,70],[8],[]),([71,94,86],[14],[]),([71,94,102],[21,17],[221]),([71,102,72],[8],[]),([71,102,76],[],[])]
set_option maxRecDepth 100000 in
theorem v88_7_10 : ∀ e ∈ k88_7_10, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_10 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_11 : List Entry := [([71,102,78],[8,32],[]),([71,102,92],[],[]),([71,102,110],[21],[]),([71,102,126],[32],[]),([71,103,76],[27,29],[]),([71,103,88],[8,29],[8]),([71,103,92],[8,32,29],[]),([71,103,108],[32,29],[180,202]),([71,110,70],[8],[]),([71,110,102],[21,24],[222]),([71,110,118],[32],[]),([71,118,72],[8],[]),([71,118,76],[],[]),([71,118,78],[8,34],[]),([71,118,94],[14],[]),([71,118,108],[],[]),([71,118,126],[32],[]),([71,119,76],[27,31],[]),([71,119,88],[8,31],[8]),([71,119,92],[8,34,31],[]),([71,119,124],[34,31],[182,204]),([71,126,70],[8],[]),([71,126,86],[14,17],[223]),([71,126,118],[32],[]),([71,296,30],[0,8,14,3,21,5,32,29,34,31],[224,217,165,183,184,206,207,218]),([71,296,46],[0,8,3,5,29,31],[217,219]),([71,358,56],[27],[225,226,185,208]),([71,358,78],[29],[]),([71,358,126],[],[]),([71,358,846],[29],[227]),([71,358,878],[5],[228]),([71,359,72],[0,27],[]),([71,359,108],[0],[167,193]),([71,366,70],[],[]),([71,366,118],[],[]),([71,366,846],[],[]),([71,374,56],[27],[229,230,186,209]),([71,374,78],[31],[]),([71,374,126],[],[]),([71,374,846],[31],[231]),([71,374,862],[3],[232]),([71,375,72],[0,27],[]),([71,375,124],[0],[168,194]),([71,382,70],[],[]),([71,382,118],[],[]),([71,382,846],[],[]),([71,566,78],[],[233]),([71,566,94],[],[234]),([71,566,334],[],[235]),([71,566,350],[],[236])]
set_option maxRecDepth 100000 in
theorem v88_7_11 : ∀ e ∈ k88_7_11, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_11 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_12 : List Entry := [([71,574,52],[0,8],[237,216,238,239]),([71,574,70],[],[]),([71,574,78],[],[240,241]),([71,574,86],[],[]),([71,574,94],[],[242,243]),([71,574,366],[29,8],[244,238]),([71,574,382],[31,8],[245,239]),([71,582,78],[],[]),([71,582,94],[],[]),([71,590,52],[0],[246,247,187,210]),([71,590,70],[3],[]),([71,590,86],[],[]),([71,591,68],[0],[]),([71,591,116],[14,27],[169,195]),([71,598,78],[],[]),([71,598,94],[],[]),([71,606,52],[0],[248,249,188,211]),([71,606,70],[5],[]),([71,606,86],[],[]),([71,607,68],[0],[]),([71,607,132],[21,27],[170,196]),([71,847,48],[8,14],[]),([71,847,52],[8,3],[250,251,47,235]),([71,863,48],[8,21],[]),([71,863,52],[8,5],[252,253,48,236]),([71,879,48],[8,32],[]),([71,879,52],[8,29],[254,255,66,244]),([71,895,48],[8,34],[]),([71,895,52],[8,31],[256,257,67,245]),([71,1119,48],[14],[258,259]),([71,1119,52],[21,14,3,5],[]),([71,1119,64],[3],[171]),([71,1119,68],[3,5],[260,261,262,263,172]),([71,1151,48],[14],[264,265]),([71,1151,52],[3,31],[]),([71,1391,48],[21],[266,267]),([71,1391,52],[5,29],[]),([71,1663,48],[32],[268,269]),([71,1663,52],[34,32,29,31],[]),([71,1663,80],[29,31],[270,271,272,273,173]),([71,1663,84],[29],[174]),([79,54,102],[0],[]),([79,54,118],[0],[]),([79,54,318],[0,8],[]),([79,96,575],[0,8],[]),([79,96,623],[0,27],[]),([79,96,879],[0,8],[]),([79,100,63],[0,8],[]),([79,100,111],[0,34],[]),([79,100,575],[0,8],[])]
set_option maxRecDepth 100000 in
theorem v88_7_12 : ∀ e ∈ k88_7_12, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_12 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_13 : List Entry := [([79,100,623],[0,27],[]),([79,100,879],[0,8],[]),([79,102,78],[0,8],[]),([79,102,126],[0,34],[]),([79,112,575],[0,8],[]),([79,112,623],[0,27],[]),([79,112,879],[0,8],[]),([79,116,63],[0,8],[]),([79,116,111],[0,32],[]),([79,116,575],[0,8],[]),([79,116,623],[0,27],[]),([79,116,879],[0,8],[]),([79,118,78],[0,8],[]),([79,118,126],[0,32],[]),([79,358,78],[],[]),([79,358,126],[],[]),([79,374,78],[],[]),([79,374,126],[],[]),([79,879,48],[0,29],[]),([79,895,48],[0,31],[]),([79,1663,48],[0,32,29,31],[274,275]),([87,62,86],[8],[]),([87,62,94],[8,32],[]),([87,62,102],[8,29],[]),([87,62,110],[8,29],[]),([87,62,118],[8,24],[276]),([87,62,126],[8],[]),([87,62,382],[34],[]),([87,76,359],[0,24],[277]),([87,76,847],[8],[]),([87,76,863],[8],[]),([87,76,879],[8],[]),([87,76,1119],[21,24],[278]),([87,76,1391],[32,34],[]),([87,94,70],[8],[]),([87,94,102],[21],[279,280]),([87,98,42],[0],[281,49]),([87,98,78],[8],[]),([87,98,92],[],[]),([87,98,104],[21],[]),([87,98,108],[],[]),([87,98,110],[21,27],[]),([87,98,126],[27],[]),([87,106,78],[8],[226]),([87,106,110],[21],[]),([87,106,126],[27],[]),([87,110,52],[],[]),([87,110,110],[21,29,24],[282]),([87,110,126],[32,29],[]),([87,110,308],[27,29],[])]
set_option maxRecDepth 100000 in
theorem v88_7_13 : ∀ e ∈ k88_7_13, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_13 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_14 : List Entry := [([87,118,78],[8],[]),([87,118,92],[],[]),([87,118,108],[],[]),([87,126,70],[8],[]),([87,126,118],[32],[]),([87,126,298],[0],[283]),([87,375,76],[0],[283]),([87,375,124],[0,17],[277]),([87,375,588],[0,32,24,17],[]),([87,574,52],[0,18],[]),([87,574,86],[],[284]),([87,574,118],[17],[]),([87,574,350],[17],[285,286]),([87,606,52],[0,18,21,5],[]),([87,606,70],[],[]),([87,618,60],[0,18],[]),([87,618,78],[17],[]),([87,618,110],[],[287]),([87,618,126],[17],[]),([87,638,52],[0,18],[]),([87,638,70],[17],[]),([87,863,48],[8,17],[288]),([87,863,52],[21,5],[285]),([87,863,64],[32,17],[]),([87,863,68],[32,17],[289,290,31,286]),([87,879,52],[29],[227]),([87,895,48],[34,17],[291]),([87,895,52],[],[292]),([87,895,92],[17],[292,293,294]),([87,1391,52],[5],[228]),([87,1391,132],[21,17],[278]),([87,1663,52],[29],[]),([95,54,102],[0],[]),([95,54,118],[0],[]),([95,98,78],[0],[]),([95,98,92],[32,3],[]),([95,98,108],[0],[]),([95,98,126],[0,27],[]),([95,98,334],[],[]),([95,102,118],[0,34],[]),([95,102,334],[0,8],[]),([95,118,78],[0],[]),([95,118,126],[0,29],[]),([95,118,334],[0,8],[]),([95,879,48],[],[]),([95,895,48],[],[]),([95,1663,48],[34],[]),([103,62,70],[8],[]),([103,62,78],[8,34],[]),([103,62,102],[8,31],[])]
set_option maxRecDepth 100000 in
theorem v88_7_14 : ∀ e ∈ k88_7_14, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_14 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_15 : List Entry := [([103,62,110],[8,31],[]),([103,62,118],[8,17],[295]),([103,62,126],[8],[]),([103,62,382],[32],[]),([103,78,70],[8],[]),([103,78,102],[14],[296,297]),([103,92,847],[8],[]),([103,92,863],[8],[]),([103,92,879],[8],[]),([103,92,1119],[14,17],[298]),([103,92,1391],[32],[]),([103,98,42],[0],[299,50]),([103,98,78],[8],[]),([103,98,88],[14],[]),([103,98,92],[],[]),([103,98,94],[14,27],[]),([103,98,108],[],[]),([103,98,126],[27],[]),([103,106,78],[8],[230]),([103,106,94],[14],[]),([103,106,126],[27],[]),([103,110,52],[],[]),([103,110,94],[14,31,17],[300]),([103,110,126],[32,31],[]),([103,110,308],[27,31],[]),([103,126,70],[8],[]),([103,126,118],[32],[]),([103,574,52],[0,25],[]),([103,574,70],[],[301]),([103,574,118],[24],[]),([103,574,334],[24],[302,303]),([103,590,52],[0,25,14,3],[]),([103,590,70],[],[]),([103,618,60],[0,25],[]),([103,618,78],[24],[]),([103,618,94],[],[304]),([103,618,126],[24],[]),([103,638,52],[0,25],[]),([103,638,70],[24],[]),([103,847,48],[8,24],[305]),([103,847,52],[14,3],[302]),([103,847,64],[34,24],[]),([103,847,68],[34,24],[306,307,41,303]),([103,879,52],[31],[231]),([103,895,48],[32,24],[308]),([103,895,52],[],[309]),([103,895,92],[24],[309,310,311]),([103,1135,52],[3],[232]),([103,1135,132],[14,24],[298]),([103,1663,52],[31],[])]
set_option maxRecDepth 100000 in
theorem v88_7_15 : ∀ e ∈ k88_7_15, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_15 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_16 : List Entry := [([111,54,102],[0],[]),([111,54,118],[0],[]),([111,98,78],[0],[]),([111,98,92],[0],[]),([111,98,108],[34,5],[]),([111,98,126],[0,27],[]),([111,98,334],[],[]),([111,102,118],[0,32],[]),([111,102,334],[0,8],[]),([111,118,78],[0],[]),([111,118,126],[0,31],[]),([111,118,334],[0,8],[]),([111,879,48],[],[]),([111,895,48],[],[]),([111,1663,48],[32],[]),([303,54,72],[],[]),([303,54,76],[21,0,8,17,3],[306,312,313]),([303,54,78],[0,21],[]),([303,54,88],[14,3],[]),([303,54,90],[0,14,3],[]),([303,54,92],[8,0,17],[314,307,315]),([303,54,94],[0,8],[316]),([303,54,108],[14,3],[]),([303,54,120],[34],[]),([303,54,124],[14,3],[]),([303,54,126],[0],[]),([303,54,602],[8],[316,312,92]),([303,54,638],[34,8],[41,303,313,315,93]),([303,62,70],[0],[]),([303,62,82],[0,3],[317,318]),([303,62,86],[0],[2,319]),([303,62,118],[0,24],[320]),([303,62,602],[],[2,319]),([303,62,638],[34],[]),([303,70,74],[8],[]),([303,70,90],[8,14],[]),([303,70,94],[8],[]),([303,70,602],[],[]),([303,70,862],[17],[]),([303,78,64],[],[]),([303,78,68],[21,3,34,8,17,24],[321,322]),([303,78,82],[8,3],[323,324]),([303,78,86],[8],[325,326]),([303,78,350],[24],[323,324,321]),([303,78,602],[],[325,326,322]),([303,82,74],[8],[]),([303,82,88],[8,21],[]),([303,82,92],[14,27],[]),([303,82,94],[8],[]),([303,82,126],[8],[])]
set_option maxRecDepth 100000 in
theorem v88_7_16 : ∀ e ∈ k88_7_16, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_16 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_17 : List Entry := [([303,82,316],[8,3,27,17],[]),([303,86,74],[8,14],[]),([303,86,94],[8],[]),([303,86,126],[8],[]),([303,86,292],[8,27,9],[]),([303,86,638],[34],[]),([303,90,94],[8],[]),([303,90,126],[8],[]),([303,94,86],[8],[]),([303,94,100],[],[]),([303,94,118],[8],[]),([303,94,638],[34],[327]),([303,118,74],[8],[]),([303,118,92],[14],[328]),([303,118,106],[8,14],[]),([303,118,110],[8],[]),([303,118,878],[],[328]),([303,126,98],[8,3,24],[329]),([303,126,102],[8],[]),([303,346,74],[14],[]),([303,346,126],[],[]),([303,382,66],[14],[]),([303,382,98],[8,14],[330,331,332,327,333]),([303,382,106],[14],[]),([303,382,366],[8],[334,332]),([303,382,878],[17],[335,333]),([303,1115,56],[],[]),([303,1115,60],[8],[]),([303,1115,92],[8],[]),([303,1119,48],[],[323]),([303,1119,52],[8],[]),([303,1119,56],[8,14,24],[336]),([303,1119,60],[8,17,24],[337,338,339,340]),([303,1119,68],[14],[]),([303,1119,132],[8],[]),([303,1399,56],[14],[]),([303,1399,60],[8,17],[341]),([303,1399,92],[8,17],[]),([303,1407,48],[],[334]),([303,1407,52],[8],[]),([303,1407,56],[8,14,24],[342]),([303,1407,60],[8,17],[343]),([303,1407,68],[14],[]),([319,54,72],[],[]),([319,54,76],[14,0,8,24,5],[289,344,345]),([319,54,78],[0,14],[]),([319,54,88],[21,5],[]),([319,54,90],[0,21,5],[]),([319,54,92],[8,0,24],[346,290,347]),([319,54,94],[0,8],[348])]
set_option maxRecDepth 100000 in
theorem v88_7_17 : ∀ e ∈ k88_7_17, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_17 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_18 : List Entry := [([319,54,104],[32],[]),([319,54,108],[21,5],[]),([319,54,110],[0],[]),([319,54,124],[21,5],[]),([319,54,602],[8],[348,344,131]),([319,54,622],[32,8],[31,286,345,347,132]),([319,62,70],[0],[]),([319,62,82],[0,5],[349,350]),([319,62,86],[0],[6,351]),([319,62,102],[0,17],[352]),([319,62,602],[],[6,351]),([319,62,622],[32],[]),([319,70,74],[8],[]),([319,70,90],[8,14],[]),([319,70,94],[8],[]),([319,70,602],[],[]),([319,70,862],[24],[]),([319,82,74],[8],[]),([319,82,88],[8,14],[]),([319,82,92],[21,27],[]),([319,82,94],[8],[]),([319,82,110],[8],[]),([319,82,316],[8,5,27,24],[]),([319,86,74],[8,21],[]),([319,86,94],[8],[]),([319,86,110],[8],[]),([319,86,292],[8,27,10],[]),([319,86,622],[32],[]),([319,90,94],[8],[]),([319,90,110],[8],[]),([319,94,86],[8],[]),([319,94,102],[8],[]),([319,94,116],[],[]),([319,94,622],[32],[353]),([319,102,74],[8],[]),([319,102,92],[21],[354]),([319,102,106],[8,21],[]),([319,102,110],[8],[]),([319,102,878],[],[354]),([319,110,98],[8,5,17],[355]),([319,110,102],[8],[]),([319,346,74],[21],[]),([319,346,110],[],[]),([319,366,66],[21],[]),([319,366,98],[8,21],[356,357,358,353,359]),([319,366,106],[21],[]),([319,366,366],[8],[360,358]),([319,366,878],[24],[361,359]),([319,1115,56],[],[]),([319,1115,60],[8],[])]
set_option maxRecDepth 100000 in
theorem v88_7_18 : ∀ e ∈ k88_7_18, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_18 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_19 : List Entry := [([319,1115,92],[8],[]),([319,1119,48],[],[362]),([319,1119,52],[8],[]),([319,1119,56],[8,21,17],[363]),([319,1119,68],[21],[]),([319,1119,116],[8],[]),([319,1119,316],[17],[362,364,365]),([319,1383,56],[21],[]),([319,1383,60],[8,24],[366]),([319,1383,92],[8,24],[]),([319,1391,48],[],[360]),([319,1391,52],[8],[]),([319,1391,56],[8,21,17],[367]),([319,1391,60],[8,24],[368]),([319,1391,68],[21],[]),([331,58,78],[8],[]),([331,58,94],[8],[]),([331,62,70],[0],[]),([331,62,86],[0],[]),([331,62,96],[32],[]),([331,62,100],[],[]),([331,62,112],[34],[]),([331,62,116],[],[]),([331,78,66],[8,27],[117]),([331,78,70],[8,14],[233]),([331,78,78],[8,17],[369,370,371]),([331,78,86],[8],[]),([331,78,94],[8,17,24],[372,373]),([331,78,100],[],[]),([331,78,350],[21,17],[]),([331,94,66],[8,27],[156]),([331,94,70],[8,21],[234]),([331,94,78],[8,24],[374,375,376]),([331,94,86],[8],[]),([331,94,116],[],[]),([331,94,350],[14,24],[]),([331,1119,52],[],[325]),([335,50,78],[8],[]),([335,50,94],[8],[]),([335,50,110],[8],[]),([335,50,126],[8],[]),([335,54,78],[0],[]),([335,54,94],[0],[]),([335,54,110],[0],[]),([335,54,126],[0],[]),([335,54,622],[32,8],[238]),([335,54,638],[34,8],[239]),([335,62,54],[0,27],[]),([335,62,70],[0],[]),([335,62,86],[0],[])]
set_option maxRecDepth 100000 in
theorem v88_7_19 : ∀ e ∈ k88_7_19, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_19 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_20 : List Entry := [([335,62,96],[8,32],[]),([335,62,100],[],[]),([335,62,102],[0],[]),([335,62,112],[8,34],[]),([335,62,116],[],[]),([335,62,118],[0],[]),([335,62,622],[32],[]),([335,62,638],[34],[]),([335,63,68],[0,8,27],[]),([335,63,112],[0,8],[]),([335,63,116],[0,8],[]),([335,63,128],[0,8],[]),([335,63,132],[0,8],[]),([335,70,74],[8],[]),([335,70,78],[8,14,17],[377,378,379]),([335,70,94],[8],[]),([335,70,126],[8],[]),([335,70,638],[11],[]),([335,79,52],[8,11],[]),([335,79,116],[8],[]),([335,86,74],[8],[]),([335,86,78],[8,21,24],[380,381,382]),([335,86,94],[8],[]),([335,86,110],[8],[]),([335,86,622],[11],[]),([335,95,52],[8,11],[]),([335,95,132],[8],[]),([335,102,74],[8],[49]),([335,102,78],[8,29],[383,384]),([335,102,110],[8,24],[385]),([335,102,126],[8],[]),([335,110,66],[8],[]),([335,110,70],[8],[]),([335,110,102],[8],[]),([335,110,118],[8],[]),([335,118,74],[8],[50]),([335,118,78],[8,31],[386,387]),([335,118,94],[8,17],[388]),([335,118,126],[8],[]),([335,126,66],[8],[]),([335,126,70],[8],[]),([335,126,86],[8],[]),([335,126,118],[8],[]),([335,366,48],[27,11,32,29],[353]),([335,366,118],[],[]),([335,382,48],[27,11,34,31],[327]),([335,382,118],[],[]),([335,591,116],[8],[]),([335,607,132],[8],[]),([335,1119,48],[],[])]
set_option maxRecDepth 100000 in
theorem v88_7_20 : ∀ e ∈ k88_7_20, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_20 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_21 : List Entry := [([335,1119,52],[8],[325]),([335,1119,56],[8],[]),([335,1151,48],[],[]),([335,1151,52],[8],[]),([335,1391,48],[],[]),([335,1391,52],[8],[]),([335,1663,48],[29],[]),([335,1663,52],[8],[]),([351,50,94],[8],[]),([351,50,110],[8,32],[]),([351,50,126],[8],[]),([351,54,94],[0],[]),([351,54,110],[0,8],[]),([351,54,120],[8,34],[]),([351,54,124],[0],[]),([351,54,126],[0],[]),([351,62,86],[0],[]),([351,62,118],[0],[]),([351,86,74],[8],[]),([351,86,78],[8,21],[]),([351,86,110],[8],[]),([351,86,124],[32],[284]),([351,98,72],[8,27,17],[389,390,356]),([351,98,74],[8],[68]),([351,98,76],[32,29],[]),([351,98,78],[8,32,29],[]),([351,98,92],[32,29],[]),([351,98,104],[21],[]),([351,98,108],[32,29],[]),([351,98,110],[8],[]),([351,98,120],[],[]),([351,98,124],[27,34,8,17,29],[391,69,357]),([351,98,126],[8,27,34],[]),([351,98,316],[8,18,27],[70,358]),([351,98,366],[24],[353,359,390,391]),([351,102,366],[21,24],[]),([351,106,74],[8],[49,71]),([351,106,78],[8,18],[392,393]),([351,106,110],[8,24],[394]),([351,106,126],[8],[]),([351,118,74],[8],[]),([351,118,78],[8,32],[]),([351,118,126],[8],[]),([351,118,894],[],[]),([351,126,66],[8],[51,72]),([351,126,70],[8,18],[309,310]),([351,126,112],[34,29,21,8,17,24],[311,73]),([351,126,116],[],[]),([351,622,66],[8],[]),([351,1391,48],[29,32],[361])]
set_option maxRecDepth 100000 in
theorem v88_7_21 : ∀ e ∈ k88_7_21, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_21 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_22 : List Entry := [([351,1391,56],[8,24],[395]),([351,1391,132],[8],[]),([351,1663,48],[29],[]),([351,1663,56],[8],[]),([367,50,78],[8],[]),([367,50,110],[8,34],[]),([367,50,126],[8],[]),([367,54,78],[0],[]),([367,54,110],[0,8],[]),([367,54,120],[8,32],[]),([367,54,124],[0],[]),([367,54,126],[0],[]),([367,62,70],[0],[]),([367,62,118],[0],[]),([367,70,74],[8],[]),([367,70,78],[8,14],[]),([367,70,110],[8],[]),([367,70,124],[34],[301]),([367,98,72],[8,27,24],[396,397,330]),([367,98,74],[8],[75]),([367,98,76],[34,31],[]),([367,98,78],[8,34,31],[]),([367,98,88],[14],[]),([367,98,92],[34,31],[]),([367,98,94],[8],[]),([367,98,108],[34,31],[]),([367,98,120],[],[]),([367,98,124],[27,32,8,24,31],[398,76,331]),([367,98,126],[8,27,32],[]),([367,98,316],[8,25,27],[77,332]),([367,98,350],[17],[327,333,397,398]),([367,102,350],[14,17],[]),([367,106,74],[8],[50,78]),([367,106,78],[8,25],[399,400]),([367,106,94],[8,17],[401]),([367,106,126],[8],[]),([367,118,74],[8],[]),([367,118,78],[8,32],[]),([367,118,126],[8],[]),([367,118,894],[],[]),([367,622,66],[8],[]),([367,1135,48],[31,34],[335]),([367,1135,56],[8,17],[402]),([367,1135,132],[8],[]),([367,1663,48],[31],[]),([367,1663,56],[8],[]),([575,54,72],[],[]),([575,54,76],[8,0,14,3,21,5],[261]),([575,54,78],[0,8],[]),([575,54,88],[0,14,3,21,5],[260])]
set_option maxRecDepth 100000 in
theorem v88_7_22 : ∀ e ∈ k88_7_22, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_22 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_23 : List Entry := [([575,54,90],[0,14,21,3,5],[260]),([575,54,92],[],[]),([575,54,94],[0],[]),([575,54,108],[14,3,21,5],[262]),([575,54,124],[21,5,14,3],[263]),([575,62,70],[0],[]),([575,62,82],[0,3,5],[]),([575,62,86],[0],[403,404]),([575,70,74],[8],[]),([575,70,90],[8],[405,406]),([575,70,94],[8],[]),([575,70,606],[17],[]),([575,70,862],[24],[]),([575,82,74],[14],[]),([575,82,94],[8],[]),([575,82,300],[14,3,27,17],[]),([575,82,316],[14,5,27,24],[]),([575,86,74],[14,21],[]),([575,86,88],[8],[]),([575,86,92],[],[]),([575,86,94],[8,14],[]),([575,90,72],[],[]),([575,90,76],[27,3],[]),([575,90,94],[8],[]),([575,94,86],[8],[]),([575,94,100],[],[]),([575,94,116],[],[]),([575,350,317],[14,24,27,17],[]),([587,62,70],[0],[]),([587,62,86],[0],[]),([587,62,100],[14,3],[]),([587,62,116],[14,27],[]),([587,94,66],[14,27,3],[]),([587,94,86],[8],[]),([591,50,118],[14,3,24],[407]),([591,54,78],[0],[247]),([591,54,94],[0],[]),([591,54,126],[0],[]),([591,62,54],[0],[408,2]),([591,62,70],[0],[]),([591,62,86],[0],[]),([591,62,100],[],[]),([591,62,112],[34],[]),([591,62,116],[],[]),([591,62,118],[0],[]),([591,70,74],[8,3],[]),([591,70,94],[8,24],[409]),([591,70,118],[8,14],[]),([591,70,126],[8],[]),([591,86,74],[14],[])]
set_option maxRecDepth 100000 in
theorem v88_7_23 : ∀ e ∈ k88_7_23, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_23 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_24 : List Entry := [([591,86,94],[8],[]),([591,86,318],[21],[410]),([591,100,607],[14,24],[411]),([591,100,623],[14,27],[]),([591,118,74],[14],[412,413]),([591,118,94],[8],[]),([591,126,86],[8],[]),([591,126,116],[],[]),([591,382,48],[14,27,3,17],[]),([591,382,86],[],[]),([591,607,68],[14],[410]),([591,607,132],[14,17],[411]),([623,54,78],[0],[]),([623,54,110],[0],[]),([623,54,124],[14,3],[]),([623,62,70],[0],[]),([623,70,74],[8],[]),([623,70,110],[8],[]),([623,98,74],[14],[]),([623,98,94],[8],[]),([623,98,108],[34,31],[]),([623,106,94],[8],[]),([843,62,70],[0],[]),([843,62,86],[0],[]),([843,62,100],[21,27],[]),([843,62,116],[21,5],[]),([843,94,66],[14,27,5],[]),([843,94,86],[8],[]),([847,50,102],[21,5,17],[414]),([847,54,78],[0],[249]),([847,54,94],[0],[]),([847,54,110],[0],[]),([847,62,54],[0],[415,6]),([847,62,70],[0],[]),([847,62,86],[0],[]),([847,62,96],[32],[]),([847,62,100],[],[]),([847,62,102],[0],[]),([847,62,116],[],[]),([847,70,74],[8,5],[]),([847,70,94],[8,17],[416]),([847,70,102],[8,21],[]),([847,70,110],[8],[]),([847,86,74],[14],[]),([847,86,94],[8],[]),([847,102,74],[21],[417,418]),([847,102,94],[8],[]),([847,110,86],[8],[]),([847,110,116],[],[]),([847,116,623],[21,27],[])]
set_option maxRecDepth 100000 in
theorem v88_7_24 : ∀ e ∈ k88_7_24, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_24 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_25 : List Entry := [([847,366,48],[21,27,5,24],[]),([847,366,86],[],[]),([863,54,78],[0],[]),([863,54,110],[0],[]),([863,54,124],[21,5],[]),([863,62,70],[0],[]),([863,70,74],[8],[]),([863,70,110],[8],[]),([863,98,74],[21],[]),([863,98,94],[8],[]),([863,98,108],[32,29],[]),([863,106,94],[8],[]),([1111,58,72],[8],[]),([1111,58,73],[8],[49]),([1111,58,76],[],[]),([1111,58,77],[8,27],[]),([1111,58,78],[8,27],[]),([1111,58,110],[21],[]),([1111,62,70],[0],[]),([1111,62,102],[0],[]),([1111,62,112],[34],[]),([1111,62,116],[0],[]),([1111,78,78],[8],[419,420,421]),([1111,110,66],[21,27],[159]),([1111,110,70],[21],[]),([1111,110,78],[21,24],[422,423]),([1111,110,86],[8],[]),([1111,110,116],[32],[287]),([1119,50,78],[8],[]),([1119,50,110],[21],[]),([1119,50,126],[32],[]),([1119,50,894],[28],[]),([1119,54,78],[0],[]),([1119,54,110],[0],[]),([1119,54,126],[0],[]),([1119,62,70],[0],[]),([1119,62,102],[0],[]),([1119,62,112],[],[]),([1119,62,116],[],[]),([1119,62,118],[0],[]),([1119,70,74],[8],[13,80]),([1119,70,78],[8],[424,425,426]),([1119,70,110],[8,24],[427]),([1119,70,126],[8],[]),([1119,102,74],[21],[]),([1119,102,78],[21,24],[428,429]),([1119,102,94],[8],[]),([1119,118,74],[32],[430,431]),([1119,118,78],[32,31],[432]),([1119,118,94],[8],[])]
set_option maxRecDepth 100000 in
theorem v88_7_25 : ∀ e ∈ k88_7_25, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_25 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_26 : List Entry := [([1119,126,66],[32],[]),([1119,126,70],[32],[]),([1119,126,86],[8],[]),([1119,638,48],[27,18,34,31,28],[]),([1119,638,86],[],[]),([1127,58,72],[8],[]),([1127,58,73],[8],[50]),([1127,58,76],[],[]),([1127,58,77],[8,27],[]),([1127,58,78],[8,27],[]),([1127,58,94],[14],[]),([1127,62,70],[0],[]),([1127,62,86],[0],[]),([1127,62,112],[32],[]),([1127,62,116],[0],[]),([1127,78,78],[8],[433,434,435]),([1127,94,66],[14,27],[120]),([1127,94,70],[14],[]),([1127,94,78],[14,17],[436,437]),([1127,94,86],[8],[]),([1127,94,116],[34],[304]),([1135,50,78],[8],[]),([1135,50,94],[14],[]),([1135,50,126],[32],[]),([1135,50,894],[30],[]),([1135,54,78],[0],[]),([1135,54,94],[0],[]),([1135,54,126],[0],[]),([1135,62,70],[0],[]),([1135,62,86],[0],[]),([1135,62,112],[],[]),([1135,62,116],[],[]),([1135,62,118],[0],[]),([1135,70,74],[8],[15,81]),([1135,70,78],[8],[438,439,440]),([1135,70,94],[8,17],[441]),([1135,70,126],[8],[]),([1135,86,74],[14],[]),([1135,86,78],[14,17],[442,443]),([1135,86,94],[8],[]),([1135,118,74],[32],[444,445]),([1135,118,78],[32,29],[446]),([1135,118,94],[8],[]),([1135,638,48],[27,25,32,29,30],[]),([1135,638,86],[],[]),([1391,50,72],[8],[]),([1391,50,76],[],[]),([1391,50,78],[8,32],[]),([1391,50,126],[32,34],[]),([1391,54,78],[0],[])]
set_option maxRecDepth 100000 in
theorem v88_7_26 : ∀ e ∈ k88_7_26, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_26 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def k88_7_27 : List Entry := [([1391,54,126],[0],[]),([1391,62,70],[0],[]),([1391,62,112],[29,0],[]),([1391,62,116],[],[]),([1391,70,74],[8],[]),([1391,70,78],[8],[447,448]),([1391,70,126],[8],[]),([1391,114,72],[],[]),([1391,114,74],[27],[]),([1391,114,76],[27,32,29,34,31],[270]),([1391,114,78],[27,32,34,29,31],[270]),([1391,114,88],[],[]),([1391,114,92],[27,8,32,29,34,31],[271]),([1391,114,94],[8,27],[]),([1391,114,108],[32,29,34,31],[272]),([1391,114,124],[34,31,32,29],[273]),([1391,122,74],[27],[449,450]),([1391,122,78],[27,18,25],[]),([1391,122,94],[8],[])]
set_option maxRecDepth 100000 in
theorem v88_7_27 : ∀ e ∈ k88_7_27, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := level_sound hR88 7 k88_7_27 (D88_6.map (wsOf c88.2)) (map_dead w88_6) (by decide +kernel)
def D88_7 : List Entry := k88_7_0 ++ (k88_7_1 ++ (k88_7_2 ++ (k88_7_3 ++ (k88_7_4 ++ (k88_7_5 ++ (k88_7_6 ++ (k88_7_7 ++ (k88_7_8 ++ (k88_7_9 ++ (k88_7_10 ++ (k88_7_11 ++ (k88_7_12 ++ (k88_7_13 ++ (k88_7_14 ++ (k88_7_15 ++ (k88_7_16 ++ (k88_7_17 ++ (k88_7_18 ++ (k88_7_19 ++ (k88_7_20 ++ (k88_7_21 ++ (k88_7_22 ++ (k88_7_23 ++ (k88_7_24 ++ (k88_7_25 ++ (k88_7_26 ++ (k88_7_27)))))))))))))))))))))))))))
theorem w88_7 : ∀ e ∈ D88_7, ¬ Live516.live basicOps goal 7 (wsOf c88.2 e).toFinset := (app_dead v88_7_0 (app_dead v88_7_1 (app_dead v88_7_2 (app_dead v88_7_3 (app_dead v88_7_4 (app_dead v88_7_5 (app_dead v88_7_6 (app_dead v88_7_7 (app_dead v88_7_8 (app_dead v88_7_9 (app_dead v88_7_10 (app_dead v88_7_11 (app_dead v88_7_12 (app_dead v88_7_13 (app_dead v88_7_14 (app_dead v88_7_15 (app_dead v88_7_16 (app_dead v88_7_17 (app_dead v88_7_18 (app_dead v88_7_19 (app_dead v88_7_20 (app_dead v88_7_21 (app_dead v88_7_22 (app_dead v88_7_23 (app_dead v88_7_24 (app_dead v88_7_25 (app_dead v88_7_26 v88_7_27)))))))))))))))))))))))))))
def k88_8_0 : List Entry := [([23,54],[0,8,1,3,21,32,17,34],[0,1,2,3]),([23,55],[8,14,9,2,1],[]),([23,62],[8,1,14,21,32,17,34,3],[4,5,6,7]),([23,70],[0,8,1,5,14,32,34,24],[8,9,10,11]),([23,71],[8,21,10,4,1],[]),([23,78],[8,1,21,14,32,34,24,5],[12,13,14,15]),([23,82],[8,1,27,14,21,32,34,0],[16,17,18,19,20,21,22,23,24,25,26]),([23,83],[8,27,1,0],[27,28,29,30,31,32,33]),([23,86],[0,8,1,11,14,21,32,34],[34,35,36,37,38,39,40,41,42,43]),([23,87],[8,27,11,1],[44]),([23,90],[8,27,0,14,21,32,34,1],[45,46,47,48,49,50,51]),([23,94],[8,1,14,21,32,34],[27,52,53,54,55]),([23,102],[0,8,1,12,14,17,21,34],[56,57,58,59,60,61,40,62,63,64,65,66,67,68]),([23,103],[8,32,12,17,1,0],[69,70]),([23,110],[8,1,32,14,17,21,34],[71,72,73,74,75,76]),([23,118],[0,8,1,13,14,21,24,32],[77,78,79,80,81,82,42,83,84,64,85,86,87,88]),([23,119],[8,34,13,24,1,0],[89,90]),([23,126],[8,1,34,14,21,24,32],[91,92,93,94,95,96]),([23,311],[0,8,14,2,1,3],[]),([23,327],[0,8,21,4,1,5],[]),([23,339],[0,8,27,1],[97,27,29,98,99,100,101]),([23,342],[8,0,27,1],[102,49,103,104,105,106,66,75,86,95,107,108]),([23,343],[8,27,0,1],[44]),([23,350],[0,1,27,3,5],[97,67,87]),([23,359],[0,8,32,17,1],[69,109]),([23,375],[0,8,34,24,1],[89,110]),([23,574],[8,14,0,3,17],[111,112,25,50,88,96,107]),([23,590],[8,21,0,5,24],[113,114,26,51,68,76,108]),([23,847],[8,3,14],[115,116]),([23,859],[8,27,14],[117,118,119,120,103]),([23,863],[8,3,17],[121,122,123,104]),([23,895],[8,3,14],[124,125]),([23,1115],[8,27,21],[126,127,128,129,105]),([23,1119],[8,5,24],[130,131,132,106]),([23,1135],[8,5,21],[133,134]),([23,1383],[8,27,32],[135,136,137,138]),([23,1391],[8,32],[139,140,40,141]),([23,1399],[8,27,34],[142,143,144,145]),([23,1407],[8,34],[146,147,42,148]),([23,1663],[8,32],[149,150,64,151]),([31,54],[0,8,21,3,2,17],[152,153]),([31,70],[0,8,14,3,5,4,24],[154,155]),([31,82],[0,27,8,14,3,21,5,32,34],[156,157,158,159,160,161]),([31,86],[0,8,14,3,21,5,32,34,27],[34,162,163,164,165,166,167,168,169]),([31,102],[0,8,14,3,17,6,21,5,34],[170,171,163,172,173,174,175,176,177,178]),([31,118],[0,8,14,3,21,5,24,7,32],[179,180,165,181,182,174,183,184,185,186]),([31,342],[0,11,8,27,3,5],[187,188,178,186,189,190]),([31,602],[0,8,27],[34,191,192,193,167,188,152,154]),([31,622],[0,8,32,12,14,17],[194,195,196,197,198,199,155,168,189]),([31,638],[0,8,34,13,21,24],[200,201,202,203,198,204,153,169,190])]
set_option maxRecDepth 100000 in
theorem v88_8_0 : ∀ e ∈ k88_8_0, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_0 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_1 : List Entry := [([31,1383],[0,27,32,8],[205,206,176]),([31,1391],[0,8,32],[207,163,208,199]),([31,1399],[0,27,34,8],[209,210,184]),([31,1407],[0,8,34],[211,165,212,204]),([31,1663],[0,8,32,34],[213,174,198,177,185]),([39,62],[8,2,21,32,17,34],[214,215,216,217,218,219]),([39,70],[0,14,2,3,8,32,17,34,24],[220,221,222]),([39,78],[14,2,21,8,32,17,34,24,5],[223,224,225]),([39,82],[14,27,3,8,21,32,17,34],[226,227,228,229,230,231]),([39,86],[0,14,2,3,8,21,17,34],[232,233,234,235,236,237]),([39,90],[14,27,0,8,21,32,17,34,2],[238,239,240]),([39,94],[14,2,3,8,21,32,17,34],[241,242,243,244,245]),([39,118],[0,14,2,3,8,24,32,17],[246,247,248,249]),([39,126],[14,2,34,8,21,24,32,17],[250,251,252]),([39,327],[0,14,21,3,2],[]),([39,339],[0,14,3,27,2],[253,254]),([39,343],[0,14,27,3,2],[255,256]),([39,375],[0,14,34,3,24,2],[257]),([39,574],[8,14,0,3,17],[258,259,260,261,244]),([39,590],[14,21,0,3,5,32,24,17],[262,263,245]),([39,847],[8,5],[264,265]),([39,859],[8,27,14],[266,267,218,260]),([39,863],[8,14],[268,269,36,270]),([39,895],[8,14],[271,272,78,273,219,261]),([39,1115],[14,27,21],[274,275]),([39,1119],[14,5,24],[276,277,278]),([39,1399],[14,27,34],[279,280]),([39,1407],[14,34],[281,282,283,284]),([47,54],[0,8,14,21,5,1,32,17,34],[285,286,287,288]),([47,70],[0,14,8,5,4,32],[289]),([47,82],[0,14,27,8,21,5,32,17,34],[226,290,291,292,293,294,295]),([47,86],[0,14,8,21,5,32,17,34],[286,296,297,298,299,300,301,302,303,304]),([47,118],[0,14,8,21,5,24,7,32,17],[287,305,306,307,301,308,309,310,311,312]),([47,606],[0,14,3,17,27],[226,313,294,288,289,312]),([47,859],[0,27,14,8],[314,315,303]),([47,863],[0,8,14],[316,286,295,304]),([47,895],[0,8,34,14],[317,287,310]),([47,1399],[0,27,14,34],[318,319,311]),([47,1407],[0,34,14],[320,301]),([55,62],[8,4,14,32,34,24],[321,322,323,324,325,326]),([55,78],[14,3,8,32,17,34,24],[327,328,329]),([55,82],[21,27,5,8,14,32,34,24],[330,331,332,333,334,335]),([55,86],[0,21,4,5,8,14,32,24],[336,337,338,339,340,341]),([55,90],[21,27,0,8,14,32,34,24,4],[342,343,344]),([55,94],[21,4,5,8,14,32,34,24],[345,346,347,348,349]),([55,102],[0,21,4,5,8,17,34,24],[350,351,352,353]),([55,110],[21,4,32,8,14,17,34,24],[354,355,356]),([55,339],[0,21,5,27,4],[357,358]),([55,343],[0,21,27,5,4],[359,360]),([55,359],[0,21,32,5,17,4],[361])]
set_option maxRecDepth 100000 in
theorem v88_8_1 : ∀ e ∈ k88_8_1, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_1 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_2 : List Entry := [([55,574],[8,21,0,5,24],[362,363,364,365,348]),([55,590],[14,21,0,3,5,17,34,24],[366,367,349]),([55,847],[8,3],[368,369]),([55,859],[8,27,21],[370,371,325,364]),([55,863],[8,21],[372,373,38,374]),([55,879],[8,21],[375,376,59,377,326,365]),([55,1115],[14,27,21],[378,379]),([55,1119],[14,3,17],[380,381,382]),([55,1383],[21,27,32],[383,384]),([55,1391],[21,32],[385,386,387,388]),([63,54],[0,8,21,14,3,1,32,34,24],[389,390,391,392]),([63,70],[0,14,21,8,3,2,34],[393]),([63,82],[0,21,27,8,14,3,32,34,24],[330,394,395,396,397,398,399]),([63,86],[0,21,8,14,3,32,34,24],[390,400,401,402,403,404,405,406,407,408]),([63,102],[0,21,8,14,3,17,6,34,24],[391,409,410,411,405,412,413,414,415,416]),([63,606],[0,21,5,24,27],[330,417,398,392,393,416]),([63,859],[0,27,21,8],[418,419,407]),([63,863],[0,8,21],[420,390,399,408]),([63,879],[0,8,32,21],[421,391,414]),([63,1383],[0,27,21,32],[422,423,415]),([63,1391],[0,32,21],[424,405]),([67,26],[0,27,8,14,3,21,5,32,29,34,31],[27,425,426,34,427,428,97,429]),([67,28],[0,8,14,21,27,32],[]),([67,62],[8,27,14,11,21,32,29,34,31],[27,430,431,29]),([67,72],[14,27,8,0,21,32,17,34,31],[98,357,432]),([67,76],[3,27,8,21,32,29,34,31],[433,434,99,358,435]),([67,78],[14,27,3,8,21,32,17,34,31],[436,437]),([67,88],[21,27,8,0,14,32,29,34,24],[100,253,438]),([67,92],[5,27,8,14,32,29,34,31],[439,440,101,254,441]),([67,94],[21,27,5,8,14,32,29,34,24],[442,443]),([67,110],[27,32,29,8,28,17],[]),([67,126],[27,34,31,8,30,24],[]),([67,300],[0,27,8,14,3,21,5,32,29,34,31],[444]),([67,574],[8,27,1,11,29,31],[445,446,429]),([67,590],[14,27,2,3,17],[447,448]),([67,606],[21,27,4,5,24],[449,450]),([67,847],[8,27,3,14],[451,438,441]),([67,863],[8,27,5,21],[452,432,435]),([67,1119],[14,27,3,21,5],[453]),([71,55],[8,11,1],[427,35,454]),([71,56],[8,27,0,14,21,32,34,17,24],[426,255,359,455,456,457,458,459,460,461,462,463,464]),([71,57],[0,8,27,14,21,32,34],[34,427,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481]),([71,60],[0,27,14,21,32,34,17,24],[482,162,483,484,485,486,487,488,489,490,427,256,360,491,492,493,494,495,496,497,498,499,500]),([71,61],[8,27,0,14,21,32,34],[427,34,187,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518]),([71,62],[8,27,0,14,21,32,34],[35,34,519,520,521,522,523,524,525,526,44,527,528,529,530,531]),([71,63],[8,27,0],[427,35,102,187,501,532,533]),([71,71],[14,2,17,3],[534,535,536,537,465,502]),([71,78],[14,3,8,21,32,17,34],[538,539,540]),([71,79],[14,0,3],[466,503]),([71,87],[21,4,24,5],[541,542,543,544,467,504])]
set_option maxRecDepth 100000 in
theorem v88_8_2 : ∀ e ∈ k88_8_2, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_2 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_3 : List Entry := [([71,94],[21,5,8,14,32,34,24],[545,546,547]),([71,95],[21,0,5],[468,505]),([71,102],[0,32,29,28,8,17,21,34],[548,549,550,551,552,553]),([71,103],[32,28,17,29],[554,555,556,557,469,506]),([71,110],[32,29,8,14,17,21,34],[558,559,560]),([71,111],[32,27,29],[470,507]),([71,118],[0,34,31,30,8,14,24,32],[561,562,563,564,565,566]),([71,119],[34,30,24,31],[567,568,569,570,471,508]),([71,126],[34,31,8,14,21,24,32],[571,572,573]),([71,127],[34,27,31],[472,509]),([71,296],[0,8,14,3,21,5,32,29,34,31],[444,574,575,454,473,510,533]),([71,358],[32,0,27,29,17],[576,577,578,474,511,579,580]),([71,359],[32,27,17,0,29],[581,554,582,455,491]),([71,366],[0,32,28,3,29,5],[583,584,475,512,585]),([71,374],[34,0,27,31,24],[586,587,588,476,513,589,590]),([71,375],[34,27,24,0,31],[591,567,592,456,492]),([71,382],[0,34,30,5,31,3],[593,594,477,514,595]),([71,566],[8,27,1,0,29,31],[596,597,501,188,598,599]),([71,574],[8,27,0,11],[600,601,602,603,604,532,605,606,579,585,589,595]),([71,575],[8,0,11,27],[527]),([71,582],[14,27,2,17,3,31],[607,608,478,515,103]),([71,590],[14,27,0,3,17],[609,610,611,479,516,104,590]),([71,591],[14,0,17,27,3],[534,612,613,457,493]),([71,598],[21,27,4,24,5,29],[614,615,480,517,105]),([71,606],[21,27,0,5,24],[616,617,618,481,518,106,580]),([71,607],[21,0,24,27,5],[541,619,620,458,494]),([71,623],[27,32,0,28,29],[459,495]),([71,639],[27,34,0,30,31],[460,496]),([71,847],[8,3,14],[621,622,528,107,598]),([71,863],[8,5,21],[623,624,529,108,599]),([71,879],[8,29,32],[625,626,530,189,605]),([71,895],[8,31,34],[627,628,531,190,606]),([71,1119],[14,3,21,5],[629,630,631,632,461,497]),([71,1151],[14,3,31],[633,634,462,498]),([71,1391],[21,5,29],[635,636,463,499]),([71,1663],[32,29,34,31],[637,638,639,640,464,500]),([75,62],[0,8,27,14,1,3,21,5,32,29,34,31],[575]),([75,78],[0,14,27,8,2,3],[]),([75,94],[0,21,27,8,4,5],[]),([75,110],[0,27,8,28,29],[]),([75,126],[0,27,8,30,31],[]),([79,54],[0,8,14,3,21,5,32,1,34],[27,641,642,643]),([79,70],[0,14,3,8,2,17],[]),([79,86],[0,21,5,8,4,24],[]),([79,96],[0,32,8,27,14,3,21,5,34],[644,645,646]),([79,100],[0,27,29,8,14,3,21,5,34],[647,648,649,650,651]),([79,102],[0,27,29,8,14,3,21,5,34,32],[652,653]),([79,112],[0,34,8,27,14,3,21,5,32],[654,655,656]),([79,116],[0,27,31,8,14,3,21,5,32],[657,658,659,660,661]),([79,118],[0,27,31,8,14,3,21,5,32,34],[662,663])]
set_option maxRecDepth 100000 in
theorem v88_8_3 : ∀ e ∈ k88_8_3, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_3 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_4 : List Entry := [([79,358],[0,28,29,32,17],[664,665]),([79,374],[0,30,31,34,24],[666,667]),([79,575],[0,8,11],[27,429,643,644,649,654,659]),([79,623],[0,32,29,28],[655,660]),([79,639],[0,34,31,30],[645,650]),([79,879],[0,29,8,32],[668,656,661]),([79,895],[0,31,8,34],[669,646,651]),([79,1663],[0,29,32,34,31],[670]),([87,62],[8,29,32,14,17,21,34],[671,672,673,674,675,676,69,677,577,664]),([87,63],[8,0,29,6,32],[]),([87,76],[32,0,8,18,3,21,29,34,24],[109,361,582,678,679,680,681,682,683]),([87,77],[32,14,0,8,18,6,29],[]),([87,94],[21,5,8,14,17,29,34,24],[684,685]),([87,95],[21,0,5,6],[]),([87,98],[27,32,8,17,21,34],[686,687,688,689,690,691,692]),([87,106],[27,32,0,8,14,17,21,34],[693,694,695,576,581]),([87,110],[32,18,0,29,8,17,21,34],[696,674,697,698,554,699]),([87,118],[0,32,18,34,33,8,17,24,29],[700,701,702]),([87,126],[32,18,0,8,17,21,24,29],[703,676,704,698,705,578,665]),([87,127],[32,34,0,18,6],[]),([87,375],[0,32,34,24,17],[706,707,705,708,678]),([87,574],[8,32,0,12,17,18,29],[709,710,711,712]),([87,606],[21,32,0,5,17,29,24],[713,714]),([87,618],[27,18,0,32,17],[696,715,716,717,718,699]),([87,638],[32,34,0,18,24,29,17],[719,720,708]),([87,863],[8,5,17],[721,722,723,724,68,712,679]),([87,879],[8,29,32,17],[725,674,579,680]),([87,895],[8,32,17],[726,727,64,676,728,677,681]),([87,1391],[21,29,5,32,24,17],[729,730,580,682]),([87,1663],[32,29,17],[731,698,683]),([95,54],[0,8,32,14,3,21,5,29,1,34],[732,733,583]),([95,86],[0,21,32,8,5,4],[]),([95,98],[0,27,32,8,17,21,5,34],[734,735,158,736,737,738]),([95,102],[0,32,8,29,14,3,21,5,34],[732,739,740]),([95,118],[0,32,8,14,3,21,5,29,34],[733,741,739,742,743,584]),([95,879],[0,8,32],[744,732,738,740,585]),([95,895],[0,8,34,32],[745,733,743]),([95,1663],[0,34,32],[746,739]),([103,62],[8,31,34,14,21,24,32],[747,748,749,750,751,752,89,753,587,666]),([103,63],[8,0,31,7,34],[]),([103,78],[14,3,8,21,24,31,32,17],[754,755]),([103,79],[14,0,3,7],[]),([103,92],[34,0,8,25,5,14,31,32,17],[110,257,592,707,756,757,758,759,760]),([103,93],[34,21,0,8,25,7,31],[]),([103,98],[27,34,8,14,24,32],[761,762,763,764,765,766,767]),([103,106],[27,34,0,8,14,21,24,32],[768,769,770,586,591]),([103,110],[34,25,0,31,8,14,24,32],[771,750,772,773,567,774]),([103,126],[32,25,34,8,14,17,24,31],[775,752,776,773,706,588,667]),([103,127],[32,0,25,7,34],[]),([103,574],[8,34,0,13,25,31,24],[777,778,779,780])]
set_option maxRecDepth 100000 in
theorem v88_8_4 : ∀ e ∈ k88_8_4, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_4 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_5 : List Entry := [([103,590],[14,34,0,3,24,31,17],[781,782]),([103,618],[27,25,0,34,24],[771,783,784,785,786,774]),([103,638],[32,34,0,25,17,31,24],[787,788,708]),([103,847],[8,3,24],[789,790,791,792,88,780,756]),([103,879],[8,31,34,24],[793,750,589,757]),([103,895],[8,34,24],[794,795,64,752,796,753,758]),([103,1135],[14,31,3,34,17,24],[797,798,590,759]),([103,1663],[32,31,34,24],[799,773,760]),([111,54],[0,8,34,14,3,21,5,31,1,32],[800,801,593]),([111,70],[0,14,34,8,3,2],[]),([111,98],[0,27,34,8,14,3,24,32],[802,156,803,804,805,806]),([111,102],[0,34,8,31,14,3,21,5,32],[800,807,808]),([111,118],[0,32,34,8,14,3,21,5,31],[801,809,807,810,811,594]),([111,879],[0,8,34],[812,800,806,808,595]),([111,895],[0,8,32,34],[813,801,811]),([111,1663],[0,32,34],[814,807]),([303,50],[8,3,21,9],[791]),([303,54],[0,8,14,21,17,34,3],[815,816,817,818,819,820,821,822,823,824,825,111,258,792,826,827]),([303,62],[8,0,14,21,32,17,34,3],[828,829,830,831,832,833]),([303,70],[8,3,14,9,32,17,34,24],[834,835,836,112,837,259,838]),([303,78],[8,3,21,32,17,34,24],[839,840,841,842,843,844]),([303,82],[8,27,14,3,21,32,17,34],[845,846,847,848,849,850]),([303,86],[8,3,14,9,21,32,17,34,27],[851,852,853,854,855]),([303,90],[8,27,14,3,21,32,17,34],[856,857]),([303,94],[8,3,9,21,17,34,27],[858,859,860,861]),([303,118],[8,3,14,9,24,32,17],[862,863,864,865,866]),([303,126],[8,3,34,21,24,32,17],[867,868]),([303,346],[8,14,27,17,9],[869,870,854,598,826,832,837,844,260]),([303,382],[8,14,34,13,17,9,21,24],[871,88,872,873,780,874,827,833,855,861,261,875]),([303,606],[8,14,27,3,17],[850,838,866,875]),([303,1115],[8,27,14,21],[876,877,878]),([303,1119],[8,24],[879,880,881,882,883,884,843]),([303,1399],[8,27,14,34],[885,886,887]),([303,1407],[8,34],[888,889,890,891,892,874]),([319,50],[8,5,14,10],[723]),([319,54],[0,8,21,14,32,24,5],[893,894,895,896,897,898,899,900,901,902,903,113,362,724,904,905]),([319,62],[8,0,21,14,32,34,24,5],[906,907,908,909,910,911]),([319,70],[8,5,14,10,32,17,34,24],[912,913,914,114,915,363,916]),([319,82],[8,27,21,5,14,32,34,24],[917,918,919,920,921,922]),([319,86],[8,5,21,10,14,32,34,24,27],[923,924,925,926,927]),([319,90],[8,27,21,5,14,32,34,24],[928,929]),([319,94],[8,5,10,14,32,24,27],[930,931,932,933]),([319,102],[8,5,21,10,17,34,24],[934,935,936,937,938]),([319,110],[8,5,32,14,17,34,24],[939,940]),([319,346],[8,21,27,24,10],[941,942,926,599,904,910,915,844,364]),([319,366],[8,21,32,12,24,10,14,17],[943,68,944,945,712,946,905,911,927,933,365,947]),([319,606],[8,21,27,5,24],[922,916,938,947]),([319,1115],[8,27,21,14],[948,949,950]),([319,1119],[8,17],[951,952,953,882,954,955,956]),([319,1383],[8,27,21,32],[957,958,959])]
set_option maxRecDepth 100000 in
theorem v88_8_5 : ∀ e ∈ k88_8_5, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_5 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_6 : List Entry := [([319,1391],[8,32],[960,961,962,963,964,946]),([331,58],[8,27,14,21,32,29,34,31,0],[34,482,266,965,370,966,191,869,941]),([331,62],[8,0,27,14,21,32,29,34,31],[967,968,969,970,971,972]),([331,78],[8,27,21,17,16,34,31],[973,974,266,975,976,977,978,315,979,596]),([331,94],[8,27,14,32,29,24,22],[980,981,370,982,983,977,984,419,985,597]),([331,110],[8,27,28,29,17],[192,942]),([331,126],[8,27,30,31,24],[193,870]),([331,1119],[8,27,14,21],[986,977,844,979,985]),([335,50],[8,11,14,21,32,34],[27,987,988,989,990]),([335,54],[0,8,27,14,21,32,34,11],[991,992,993,994,600,995,996]),([335,59],[0,8,1,11],[527]),([335,62],[8,0,14,21,32,34,27],[997,998,999,1000,1001,1002,1003,1004,1005,1006,1007]),([335,63],[8,11,27],[27,643,1008,1009,1010,1011,1012]),([335,70],[8,11,14,21,32,17,34],[1013,1014,1015,1016,1017,601]),([335,79],[8,14,9,17,11,27],[1018,1019]),([335,86],[8,11,21,14,32,34,24],[1020,1021,1022,1023,1024,603]),([335,95],[8,21,10,24,11,27],[1025,1026]),([335,102],[8,11,32,14,17,21,34,29],[1027,1028,1029,1030]),([335,110],[8,11,28,12,29,14,17,21,34],[1031,1032,1033,1034]),([335,111],[8,32,28,12,11],[]),([335,118],[8,11,34,14,21,24,32,31],[1035,1036,1037,1038]),([335,126],[8,11,30,13,31,14,21,24,32],[1039,1040,1041,1042]),([335,127],[8,34,30,13,11],[]),([335,366],[8,32,27,12,29,17],[1043,1044,995,1006,1024,933,605]),([335,382],[8,34,27,13,31,24],[1045,1046,996,1007,1017,861,606]),([335,591],[8,14,17,11],[1018,1047]),([335,607],[8,21,24,11],[1025,1048]),([335,623],[8,32,28,11,29],[]),([335,639],[8,34,30,11,31],[]),([335,1119],[8,14],[1049,1050,1051,882]),([335,1151],[8,31,14],[1052,1053]),([335,1391],[8,29,21],[1054,1055]),([335,1663],[8,29,32],[1056,1057]),([351,50],[8,12,18,32,17,21,29,34,0],[1058,1059,1060,194,943]),([351,54],[0,8,32,14,17,21,29,34],[1061,1062,1063,1064,1065,709]),([351,62],[8,0,32,14,17,21,29,34],[1066,1067]),([351,86],[8,12,21,14,17,29,24],[1068,1069,1070,1071,710]),([351,98],[8,27,32,17,21,34,29],[1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1043,1083,1084,195,944]),([351,102],[8,12,18,29,34],[1085]),([351,106],[8,27,32,14,17,21,34,18],[1086,1087,1088,1089,196,945]),([351,118],[8,12,34,14,17,21,24,29],[1090,1091,1092,197,1044,711,1093]),([351,126],[8,12,18,21,24,29,32],[1094,1095,1096,1097,796,198]),([351,622],[8,32,27,18,29],[1098,1083,1093,199,946]),([351,1391],[8,29,24],[1099,1100,933,1101,947,1084,1085]),([351,1663],[8,29],[1102,1103]),([367,50],[8,13,25,34,14,24,31,32,0],[1104,1105,1106,200,871]),([367,54],[0,8,34,14,21,24,31,32],[1107,1108,1109,1110,1111,777]),([367,62],[8,0,34,14,21,24,31,32],[1112,1113]),([367,70],[8,13,14,21,24,31,17],[1114,1115,1116,1117,778]),([367,98],[8,27,34,14,24,32,31],[1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1045,1129,1130,201,872])]
set_option maxRecDepth 100000 in
theorem v88_8_6 : ∀ e ∈ k88_8_6, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_6 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_7 : List Entry := [([367,102],[8,13,25,31,32],[1131]),([367,106],[8,27,34,14,21,24,32,25],[1132,1133,1134,1135,202,873]),([367,118],[8,13,32,14,17,21,24,31],[1136,1137,1138,203,1046,779,1139]),([367,622],[8,34,27,25,31],[1140,1129,1139,204,874]),([367,1135],[8,31,17],[1141,1142,861,1143,875,1130,1131]),([367,1663],[8,31],[1144,1145]),([575,50],[14,3,8,15],[631]),([575,54],[0,14,21,8,17,24,3,5],[1146,1147,1148,1149,1150,1151,1152,1153,1154,262,366,632]),([575,62],[14,0,21,8,32,17,34,24,3,5],[1155,1156,1157]),([575,70],[8,3,14,15,32,17,34,24],[1158,1159,1160,263,1161,367,1162]),([575,82],[14,27,21,3,8,32,17,34,24],[1163,1164,1165,1166]),([575,86],[8,14,3,21,15,32,17,34,24],[1167,1168,1169,1170]),([575,90],[14,27,21,3,8,32,17,34,24],[1171,1172,1173]),([575,94],[14,3,15,21,8,17,24],[1174,1175,1176]),([575,350],[14,21,27,3,17,24],[1165,1177,1161]),([575,606],[14,21,27,5,17,24],[1166,1177,1162]),([587,58],[14,27,8,3,21,32,17,34,31],[117,378,119]),([587,62],[14,0,27,8,21,17,34,31],[1178,1179,1180,971,1181,120]),([587,78],[8,27,14,11,3,21,32,17,34,31],[117,949,607]),([587,94],[14,27,3,8,32,17,34,24],[1182,378,1183,949,950,608]),([587,126],[14,27,30,31],[]),([591,50],[14,3,8,21,32,17,34],[226,121,380,1184,313,534]),([591,54],[0,14,27,8,21,32,17,34],[1185,1186,1187,609,612]),([591,62],[14,0,8,21,17,34],[1188,1189,1190,1191,1192,1193,1194]),([591,70],[8,3,14,21,32,17,34],[121,1195,952,1196,1197,1198,1018,954,447,610]),([591,71],[8,27,3,16,14],[]),([591,86],[8,14,3,21,32,17,34,24],[380,1199,952,1200,1201,448,611]),([591,87],[14,21,27,3,16],[]),([591,100],[14,27,16,20,3,8,21,34,24],[613,1047,1202,1203,123,382,798,955,1143]),([591,101],[14,32,27,3,8,16],[]),([591,118],[8,14,3,27,31,21,24,32,17],[1204,1205]),([591,119],[14,34,27,3,16],[]),([591,126],[14,3,34,31,8,21,24,17],[1206,1207]),([591,382],[14,34,27,3,24,17],[1208,1209]),([591,607],[14,21,24,17],[1210,1211,1201,1177,1202]),([591,639],[14,34,30,31,17],[1203]),([623,50],[14,3,8,19,17],[]),([623,54],[0,14,34,8,21,24,31,17,3],[1212,1213,1214,781]),([623,62],[14,0,34,8,21,24,31,32,17],[1215]),([623,70],[8,3,14,19,21,24,31,32,17],[1216,1217,1209,782]),([623,98],[14,27,34,3,8,24,32,17,31],[1218,1219,1220,1208]),([623,102],[8,14,3,27,19,31,24],[]),([623,106],[14,27,34,3,8,21,24,32,17],[1221]),([843,58],[21,27,8,5,14,32,29,34,24],[126,274,128]),([843,62],[21,0,27,8,14,32,29,24],[1222,1223,969,1224,1225,129]),([843,78],[8,27,21,11,5,14,32,29,34,24],[126,877,614]),([843,94],[14,27,21,5,8,32,17,34,24],[1226,274,1227,877,878,615]),([843,110],[21,27,28,29],[]),([847,50],[21,5,8,14,32,34,24],[330,130,276,1228,417,541]),([847,54],[0,21,27,8,14,32,34,24],[1229,1230,1231,616,619])]
set_option maxRecDepth 100000 in
theorem v88_8_7 : ∀ e ∈ k88_8_7, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_7 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_8 : List Entry := [([847,62],[21,0,8,14,32,24],[1232,1233,1234,1235,1236,1237,1238]),([847,70],[8,5,21,14,32,34,24],[130,1239,880,1240,1241,1242,1025,883,449,617]),([847,71],[8,27,5,22,21],[]),([847,86],[8,14,5,21,32,17,34,24],[276,1243,880,1244,1210,450,618]),([847,87],[14,27,5,22,21],[]),([847,102],[8,21,5,27,29,14,17,34,24],[1245,1246]),([847,103],[21,32,27,5,22],[]),([847,110],[21,5,32,29,8,14,17,24],[1247,1248]),([847,116],[21,27,22,26,5,8,14,32,17],[620,1048,1211,1249,132,278,730,884,1101]),([847,117],[21,34,27,5,8,22],[]),([847,366],[21,32,27,5,17,24],[1250,1251]),([847,623],[21,32,28,29,24],[1249]),([863,50],[21,5,8,23,24],[]),([863,54],[0,21,32,8,14,17,29,24,5],[1252,1253,1254,713]),([863,62],[21,0,32,8,14,17,29,34,24],[1255]),([863,70],[8,5,21,23,14,17,29,34,24],[1256,1257,1251,714]),([863,98],[21,27,32,5,8,17,34,24,29],[1258,1259,1260,1250]),([863,102],[8,21,5,27,23,29,17],[]),([863,106],[21,27,32,5,8,14,17,34,24],[1261]),([1111,58],[27,32,8,14,17,21,34,31],[135,1262,1263,1264,1265,1266,383,1267,137,206]),([1111,62],[27,0,32,8,14,17,21,34,31],[696,1268,1269,1270,1271,715,138]),([1111,78],[8,27,32,11,14,17,21,34,31],[135,1272,958,716]),([1111,110],[21,27,32,8,14,17,24,22],[1273,1274,383,1275,1276,958,1277,423,959,717]),([1111,126],[27,32,30,31,14],[718]),([1119,50],[32,18,0,8,28,17,21,34],[1278,1279,1280,1098,1281]),([1119,54],[0,32,27,8,14,17,21,34,28],[1282,1283,1284]),([1119,62],[32,0,29,8,14,17,21,34],[696,1285,1286,1287,1288,1289]),([1119,70],[8,18,32,28,17,21,34],[1290,1291,1292,1293,208,964]),([1119,102],[8,21,18,32,28,17,34,24],[1294,1295,1296]),([1119,118],[8,32,18,27,28,17,21,24,31],[1297,1298,1299]),([1119,126],[32,18,34,29,8,21,24],[1300,1301,1302]),([1119,383],[27,32,34,29,28],[]),([1119,638],[32,34,27,18,29,31,24],[1303,1304,1281]),([1127,58],[27,34,8,14,21,24,32,29],[142,1305,1306,1307,1308,1309,279,1310,144,210]),([1127,62],[27,0,34,8,14,21,24,32,29],[771,1311,1312,1313,1314,783,145]),([1127,78],[8,27,34,11,14,21,24,32,29],[142,1315,886,784]),([1127,94],[14,27,34,8,21,24,17,16],[1316,1317,279,1318,1319,886,1320,319,887,785]),([1127,126],[27,32,34,28,29,21],[786]),([1135,50],[34,25,0,8,30,14,24,32],[1321,1322,1323,1140,1324]),([1135,54],[0,34,27,8,14,21,24,32,30],[1325,1326,1327]),([1135,62],[34,0,31,8,14,21,24,32],[771,1328,1329,1330,1331,1332]),([1135,70],[8,25,34,30,14,24,32],[1333,1334,1335,1336,212,892]),([1135,86],[8,14,25,34,30,24,32,17],[1337,1338,1339]),([1135,118],[8,32,25,34,29,14,17,24],[1340,1341,1342]),([1135,638],[32,34,27,25,29,17],[1343,1344,1324]),([1391,50],[32,18,0,8,33,17,21,24,29],[1345,1346,1347,1348]),([1391,54],[0,32,34,8,14,17,21,24,29],[1349,1350,719,787]),([1391,62],[32,0,34,8,14,17,21,24,29],[1351,1352,1353]),([1391,70],[8,18,32,33,17,21,24,29],[1354,1355,1356,720,1304,788,1344]),([1391,114],[27,32,34,8,17,24,29,31],[1357,1358,1359,1360,1361,1362,1363,1364,1365,1303,1343,639])]
set_option maxRecDepth 100000 in
theorem v88_8_8 : ∀ e ∈ k88_8_8, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_8 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def k88_8_9 : List Entry := [([1391,118],[8,32,18,27,33,29],[640]),([1391,122],[27,32,34,8,14,17,21,24,18,25],[1366,1367,1368])]
set_option maxRecDepth 100000 in
theorem v88_8_9 : ∀ e ∈ k88_8_9, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := level_sound hR88 8 k88_8_9 (D88_7.map (wsOf c88.2)) (map_dead w88_7) (by decide +kernel)
def D88_8 : List Entry := k88_8_0 ++ (k88_8_1 ++ (k88_8_2 ++ (k88_8_3 ++ (k88_8_4 ++ (k88_8_5 ++ (k88_8_6 ++ (k88_8_7 ++ (k88_8_8 ++ (k88_8_9)))))))))
theorem w88_8 : ∀ e ∈ D88_8, ¬ Live516.live basicOps goal 8 (wsOf c88.2 e).toFinset := (app_dead v88_8_0 (app_dead v88_8_1 (app_dead v88_8_2 (app_dead v88_8_3 (app_dead v88_8_4 (app_dead v88_8_5 (app_dead v88_8_6 (app_dead v88_8_7 (app_dead v88_8_8 v88_8_9)))))))))
def k88_9_0 : List Entry := [([23],[8,0,14,1,21,32,34,17,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]),([31],[8,0,14,21,32,34,3,5],[40,41,42,43,44,45,46,47,48,49,50,51,52,53,54]),([39],[14,0,8,3,2,21,32,17,34,24],[0,55,56,57,58,59,60,61,62,63,18,64,65,66,67,68,69,70,71,72,73,74,75,76,77]),([47],[14,0,8,21,32,17,34,5],[78,79,80,81,82,83,84,85,86,87,88]),([55],[21,0,8,5,4,14,32,34,24,17],[3,89,56,90,91,92,93,94,95,96,19,64,97,98,99,100,101,102,103,104,105,106,107,108,109]),([63],[21,0,8,14,32,34,24,3],[110,111,112,113,114,115,116,117,118,119,120]),([67],[27,8,14,21,32,34,0,29,31],[121,122,123,124,125,126,127,128,129,130,131,132,20,65,97,133,134,135,136,137,138]),([71],[0,27,8,14,21,32,34,17,24],[121,122,8,139,140,141,142,143,144,145,59,146,147,148,92,149,150,151,152,153,154,155,156,157,158,159,160,21,22,46,66,98,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185]),([75],[0,27,8,14,21,32,34,3,5,29,31],[122,186,187,188,189,190,160]),([79],[0,8,14,21,32,34,27,3,5],[122,121,191,192,193,194,195,196,197,198,199,132,23,200,201,202,203,204,205,206,207]),([87],[32,0,8,29,14,17,21,34,24],[12,208,209,210,211,95,212,213,214,152,215,216,217,218,219,24,99,161,162,200,220,221,222,223,224,225,226,227,228,229]),([95],[32,0,8,14,17,21,34,5,29],[230,231,232,233,234,163,235,236,237]),([103],[34,0,8,31,14,21,24,32,17],[15,238,239,62,240,241,242,243,244,156,245,246,217,247,248,25,67,164,165,201,220,249,250,251,252,253,254,255,256,257]),([111],[34,0,8,14,21,24,32,3,31],[258,259,260,261,262,166,263,264,265]),([303],[8,14,3,21,9,32,17,34,24],[266,267,0,268,269,270,271,272,273,274,275,276,26,277,278,68,279,102,136,178,253,280,281,282,283]),([319],[8,21,5,14,10,32,34,24,17],[284,285,3,286,287,270,288,289,290,291,292,293,27,294,295,100,296,70,137,179,225,297,298,299,300]),([331],[8,27,14,21,32,34,29,31],[301,302,303,304,305,306,47,277,294,167,71,84,103,116,307]),([335],[8,27,11,14,21,32,34,17,24],[308,309,8,310,311,312,313,274,314,315,291,316,317,318,319,320,321,322,323,324,133,168,169,202,325,326,327,328,72,85,104,117,226,235,254,263,329,330,331,332]),([351],[8,32,12,18,14,17,21,34,29,24],[333,334,12,335,336,293,337,338,339,318,340,341,48,295,323,221,342,105,118,180,205,255,264,343,344]),([367],[8,34,13,25,14,21,24,32,31,17],[345,346,15,347,348,276,349,350,351,321,352,341,49,278,324,249,353,73,86,181,206,227,236,354,355]),([575],[14,21,3,8,15,32,17,34,24],[356,357,56,358,359,270,360,361,362,363,69,364,101,365,28,138,182,307,329]),([587],[8,14,27,21,32,17,34,3,31],[366,367,368,369,370,170,29,106,297]),([591],[14,27,3,8,21,17,34,24],[371,372,59,373,374,375,274,376,377,363,378,379,380,381,382,83,279,364,383,134,171,172,325,384,385,30,107,256,298,354]),([623],[14,34,3,8,19,21,24,32,17,31],[386,387,62,388,389,276,390,391,392,382,383,250,31,183,330]),([843],[8,21,27,14,32,34,24,5,29],[393,394,395,396,397,173,32,74,280]),([847],[21,27,5,8,14,32,24,17],[398,399,92,400,401,402,291,403,404,363,405,406,407,408,409,115,296,365,410,135,174,175,326,384,411,33,75,228,281,343]),([863],[21,32,5,8,23,14,17,34,24,29],[412,413,95,414,415,293,416,417,418,407,410,222,34,184,331]),([1111],[27,32,8,14,17,21,34,31],[419,420,421,422,423,223,35,50,108,119,299]),([1119],[32,27,28,18,8,14,17,21,34,24],[424,425,152,426,427,318,428,407,429,430,176,203,327,411,431,342,432,36,51,109,120,257,265,300,355]),([1127],[27,34,8,14,21,24,32,29],[433,434,435,436,437,251,37,52,76,87,282]),([1135],[34,27,30,25,8,14,21,24,32,17],[438,439,156,440,441,321,442,382,443,430,177,204,328,385,431,353,444,38,53,77,88,229,237,283,344]),([1391],[32,34,33,18,8,14,17,21,24,29],[445,446,217,447,448,341,449,450,451,430,224,432,252,444,39,54,185,207,332])]
set_option maxRecDepth 100000 in
theorem v88_9_0 : ∀ e ∈ k88_9_0, ¬ Live516.live basicOps goal 9 (wsOf c88.2 e).toFinset := level_sound hR88 9 k88_9_0 (D88_8.map (wsOf c88.2)) (map_dead w88_8) (by decide +kernel)
def D88_9 : List Entry := k88_9_0
theorem w88_9 : ∀ e ∈ D88_9, ¬ Live516.live basicOps goal 9 (wsOf c88.2 e).toFinset := v88_9_0
def k88_10_0 : List Entry := [([],[8,14,21,32,34,17,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])]
set_option maxRecDepth 100000 in
theorem v88_10_0 : ∀ e ∈ k88_10_0, ¬ Live516.live basicOps goal 10 (wsOf c88.2 e).toFinset := level_sound hR88 10 k88_10_0 (D88_9.map (wsOf c88.2)) (map_dead w88_9) (by decide +kernel)
def D88_10 : List Entry := k88_10_0
theorem w88_10 : ∀ e ∈ D88_10, ¬ Live516.live basicOps goal 10 (wsOf c88.2 e).toFinset := v88_10_0
theorem g88 : GoodC c88 := claim_sound2 D88_10 c88 w88_10 (by decide +kernel)
def c89 : Claim := (3, available 0xb3000000000000000000000000000000000001b3 0 inputs)
def r89 : List RE := []
def d89 : List Entry := [([],[],[])]
def e89 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g89 : GoodC c89 := claim_sound [] gnil r89 d89 e89 c89 (by decide +kernel)
def c90 : Claim := (4, available 0xf3000000000000000000000000030c80000001f3 0 inputs)
def r90 : List RE := [(0xb3000000000000000000000000000000000001b3,0,0)]
def d90 : List Entry := [([],[0],[])]
def e90 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g90 : GoodC c90 := claim_sound [c89] (gcons g89 gnil) r90 d90 e90 c90 (by decide +kernel)
def c91 : Claim := (3, available 0x331800000000000000000000000000 107 inputs)
def r91 : List RE := []
def d91 : List Entry := [([],[],[])]
def e91 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g91 : GoodC c91 := claim_sound [] gnil r91 d91 e91 c91 (by decide +kernel)
def c92 : Claim := (4, available 0xbb9c00000000000000000000000000 106 inputs)
def r92 : List RE := [(0x331800000000000000000000000000,107,0)]
def d92 : List Entry := [([],[0],[])]
def e92 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g92 : GoodC c92 := claim_sound [c91] (gcons g91 gnil) r92 d92 e92 c92 (by decide +kernel)
def c93 : Claim := (6, available 0xf300000000bb9c0000000000000b8e80000001f3 0 inputs)
def r93 : List RE := [(0x6000000000aa040000000000000a028000000160,5,0),(0x5100000000098c00000000000000868000000051,0,1),(0xb3000000000000000000000000000000000001b3,0,2),(0xf3000000000000000000000000030c80000001f3,0,3),(0xbb9c00000000000000000000000000,106,4)]
def d93 : List Entry := [([],[0,1,2,4],[0,1,2,3,4])]
def e93 : List (List Entry) := [[([19],[0,3,4],[]),([23],[0,2],[0]),([39],[0],[]),([295],[1,3,4],[]),([303],[1,2],[1])],[([23,56],[],[]),([303,52],[],[])]]
set_option maxRecDepth 100000 in
theorem g93 : GoodC c93 := claim_sound [c11,c61,c89,c90,c92] (gcons g11 (gcons g61 (gcons g89 (gcons g90 (gcons g92 gnil))))) r93 d93 e93 c93 (by decide +kernel)
def c94 : Claim := (7, available 0xf39ce70000bb9c0005dce000000fcf80000001f3 0 inputs)
def r94 : List RE := [(0xf300000000bb9c0000000000000b8e80000001f3,0,0)]
def d94 : List Entry := [([],[0],[])]
def e94 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g94 : GoodC c94 := claim_sound [c93] (gcons g93 gnil) r94 d94 e94 c94 (by decide +kernel)
def c95 : Claim := (3, available 0xb318c600003318000198c00000000000000001b3 0 inputs)
def r95 : List RE := []
def d95 : List Entry := [([4100,4099],[],[]),([4100],[],[]),([4099],[],[]),([],[],[])]
def e95 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g95 : GoodC c95 := claim_sound [] gnil r95 d95 e95 c95 (by decide +kernel)
def c96 : Claim := (3, available 0x198c0000000000000000000 78 inputs)
def r96 : List RE := []
def d96 : List Entry := [([],[],[])]
def e96 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g96 : GoodC c96 := claim_sound [] gnil r96 d96 e96 c96 (by decide +kernel)
def c97 : Claim := (4, available 0x5dce0000000000000000000 77 inputs)
def r97 : List RE := [(0x198c0000000000000000000,78,0)]
def d97 : List Entry := [([],[0],[])]
def e97 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g97 : GoodC c97 := claim_sound [c96] (gcons g96 gnil) r97 d97 e97 c97 (by decide +kernel)
def c98 : Claim := (6, available 0xf30000000000000005dce00000074d80000001f3 0 inputs)
def r98 : List RE := [(0x6000000000000000055020000006018000000160,5,0),(0x5100000000000000004c60000000458000000051,0,1),(0xb3000000000000000000000000000000000001b3,0,2),(0xf3000000000000000000000000030c80000001f3,0,3),(0x5dce0000000000000000000,77,4)]
def d98 : List Entry := [([],[0,1,2,4],[0,1,2,3,4])]
def e98 : List (List Entry) := [[([19],[0,3,4],[]),([23],[0,2],[0]),([39],[0],[]),([295],[1,3,4],[]),([303],[1,2],[1])],[([23,56],[],[]),([303,52],[],[])]]
set_option maxRecDepth 100000 in
theorem g98 : GoodC c98 := claim_sound [c13,c71,c89,c90,c97] (gcons g13 (gcons g71 (gcons g89 (gcons g90 (gcons g97 gnil))))) r98 d98 e98 c98 (by decide +kernel)
def c99 : Claim := (3, available 0x18c60000331800000000000000000000000000 107 inputs)
def r99 : List RE := []
def d99 : List Entry := [([4099],[],[]),([],[],[])]
def e99 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g99 : GoodC c99 := claim_sound [] gnil r99 d99 e99 c99 (by decide +kernel)
def c100 : Claim := (4, available 0x9ce70000bb9c00000000000000000000000000 106 inputs)
def r100 : List RE := [(0x18c60000331800000000000000000000000000,107,0)]
def d100 : List Entry := [([4100],[0],[]),([],[],[])]
def e100 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g100 : GoodC c100 := claim_sound [c99] (gcons g99 gnil) r100 d100 e100 c100 (by decide +kernel)
def c101 : Claim := (4, available 0xb5a80000077000000003740000 18 inputs)
def r101 : List RE := []
def d101 : List Entry := [([],[],[])]
def e101 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g101 : GoodC c101 := claim_sound [] gnil r101 d101 e101 c101 (by decide +kernel)
def c102 : Claim := (4, available 0x775a00000000000000000000000000 105 inputs)
def r102 : List RE := [(0x331800000000000000000000000000,107,0)]
def d102 : List Entry := [([],[0],[])]
def e102 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g102 : GoodC c102 := claim_sound [c91] (gcons g91 gnil) r102 d102 e102 c102 (by decide +kernel)
def c103 : Claim := (6, available 0xbb00000000775a00000000000000000007bc01bb 0 inputs)
def r103 : List RE := [(0x8a000000005052000000000000000000050c008a,1,0),(0x1900000000054a000000000000000000009c0019,0,1),(0xb3000000000000000000000000000000000001b3,0,2),(0x775a00000000000000000000000000,105,3)]
def d103 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e103 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g103 : GoodC c103 := claim_sound [c46,c62,c89,c102] (gcons g46 (gcons g62 (gcons g89 (gcons g102 gnil)))) r103 d103 e103 c103 (by decide +kernel)
def c104 : Claim := (3, available 0x48148000000110488280000000000000000000 79 inputs)
def r104 : List RE := []
def d104 : List Entry := [([],[],[])]
def e104 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g104 : GoodC c104 := claim_sound [] gnil r104 d104 e104 c104 (by decide +kernel)
def c105 : Claim := (3, available 0x2528000000008c80a40000000000000000000 78 inputs)
def r105 : List RE := []
def d105 : List Entry := [([],[],[])]
def e105 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g105 : GoodC c105 := claim_sound [] gnil r105 d105 e105 c105 (by decide +kernel)
def c106 : Claim := (3, available 0x18c60000000000000000000000000000000000 137 inputs)
def r106 : List RE := []
def d106 : List Entry := [([],[],[])]
def e106 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g106 : GoodC c106 := claim_sound [] gnil r106 d106 e106 c106 (by decide +kernel)
def c107 : Claim := (4, available 0x5ad68000000000000000000000000000000000 135 inputs)
def r107 : List RE := [(0x18c60000000000000000000000000000000000,137,0)]
def d107 : List Entry := [([],[0],[])]
def e107 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g107 : GoodC c107 := claim_sound [c106] (gcons g106 gnil) r107 d107 e107 c107 (by decide +kernel)
def c108 : Claim := (6, available 0x5ad68000000139c99ac0000000000000000000 78 inputs)
def r108 : List RE := [(0x48148000000110488280000000000000000000,79,0),(0x2528000000008c80a40000000000000000000,78,1),(0x198c0000000000000000000,78,2),(0x5ad68000000000000000000000000000000000,135,3)]
def d108 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e108 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g108 : GoodC c108 := claim_sound [c104,c105,c96,c107] (gcons g104 (gcons g105 (gcons g96 (gcons g107 gnil)))) r108 d108 e108 c108 (by decide +kernel)
def c109 : Claim := (3, available 0xb3000000000000000198c00000000000000001b3 0 inputs)
def r109 : List RE := []
def d109 : List Entry := [([4099],[],[]),([],[],[])]
def e109 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g109 : GoodC c109 := claim_sound [] gnil r109 d109 e109 c109 (by decide +kernel)
def c110 : Claim := (4, available 0xbb00000000000031899ac00000000000033401bb 0 inputs)
def r110 : List RE := [(0xb3000000000000000198c00000000000000001b3,0,0)]
def d110 : List Entry := [([4100],[0],[]),([],[],[])]
def e110 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g110 : GoodC c110 := claim_sound [c109] (gcons g109 gnil) r110 d110 e110 c110 (by decide +kernel)
def c111 : Claim := (4, available 0x5ad68000775a00000000000000000000000000 105 inputs)
def r111 : List RE := [(0x18c60000331800000000000000000000000000,107,0)]
def d111 : List Entry := [([4100],[0],[]),([],[],[])]
def e111 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g111 : GoodC c111 := claim_sound [c99] (gcons g99 gnil) r111 d111 e111 c111 (by decide +kernel)
def c112 : Claim := (5, available 0xfb000000000000000000000330032c80037401fb 0 inputs)
def r112 : List RE := [(0xf3000000000000000000000000030c80000001f3,0,0)]
def d112 : List Entry := [([],[0],[])]
def e112 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g112 : GoodC c112 := claim_sound [c90] (gcons g90 gnil) r112 d112 e112 c112 (by decide +kernel)
def c113 : Claim := (5, available 0xffde00000000000000000000000000 105 inputs)
def r113 : List RE := [(0xbb9c00000000000000000000000000,106,0)]
def d113 : List Entry := [([],[0],[])]
def e113 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g113 : GoodC c113 := claim_sound [c92] (gcons g92 gnil) r113 d113 e113 c113 (by decide +kernel)
def c114 : Claim := (8, available 0xfb00000000ffde000000000bb00bae8007fc01fb 0 inputs)
def r114 : List RE := [(0x6000000000ee06000000000aa00a028006e80160,5,0),(0x8a00000000d0d600000000099009aa00050c008a,1,1),(0x59000000000dce0000000000b000a68000dc0059,0,2),(0xf300000000bb9c0000000000000b8e80000001f3,0,3),(0xbb00000000775a00000000000000000007bc01bb,0,4),(0xfb000000000000000000000330032c80037401fb,0,5),(0xffde00000000000000000000000000,105,6)]
def d114 : List Entry := [([],[2,3,4,5,6],[0,1,2,3])]
def e114 : List (List Entry) := [[([19],[1,2,3,4,5,6,0],[0,1]),([23],[2,1,0,3,4,5,6],[2,3,4]),([27],[0,2,1,3,4,5,6],[5,6,7,8,9,4]),([31],[2,0,3,4,5,6,1],[0,1])],[([19,26],[1,2],[0]),([19,300],[1,0],[1]),([23,60],[],[]),([23,61],[2],[2]),([23,296],[0,2],[1,3,4,2]),([27,60],[0,1],[4]),([27,76],[0],[]),([27,92],[1],[]),([27,104],[],[]),([27,108],[],[])],[([19,26,60],[],[]),([19,300,20],[2],[0]),([23,61,568],[],[1,2]),([23,296,30],[0,2],[1,2]),([23,296,44],[2],[1])],[([19,300,20,29],[],[]),([23,61,568,28],[],[]),([23,61,568,44],[],[])]]
set_option maxRecDepth 100000 in
theorem g114 : GoodC c114 := claim_sound [c15,c38,c64,c93,c103,c112,c113] (gcons g15 (gcons g38 (gcons g64 (gcons g93 (gcons g103 (gcons g112 (gcons g113 gnil))))))) r114 d114 e114 c114 (by decide +kernel)
def c115 : Claim := (4, available 0x9ce70000000000000000000000000000000000 136 inputs)
def r115 : List RE := [(0x18c60000000000000000000000000000000000,137,0)]
def d115 : List Entry := [([],[0],[])]
def e115 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g115 : GoodC c115 := claim_sound [c106] (gcons g106 gnil) r115 d115 e115 c115 (by decide +kernel)
def c116 : Claim := (5, available 0xdef78000000000000000000000000000000000 135 inputs)
def r116 : List RE := [(0x9ce70000000000000000000000000000000000,136,0)]
def d116 : List Entry := [([],[0],[])]
def e116 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g116 : GoodC c116 := claim_sound [c115] (gcons g115 gnil) r116 d116 e116 c116 (by decide +kernel)
def c117 : Claim := (7, available 0xfb000000000000b5addee00770076d80037401fb 0 inputs)
def r117 : List RE := [(0xf30000000000000005dce00000074d80000001f3,0,0)]
def d117 : List Entry := [([],[0],[])]
def e117 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g117 : GoodC c117 := claim_sound [c98] (gcons g98 gnil) r117 d117 e117 c117 (by decide +kernel)
def c118 : Claim := (10, available 0xfbdef78000ffdfbdeddee00ff00fef8007fc01fb 0 inputs)
def r118 : List RE := [(0x60d6818000ee07ad6550200ee00e038006e80160,5,0),(0xc0018000c007806400200cc00c030004080000,19,1),(0x40060180000c060c60402000e000038000c80040,6,2),(0xd0000000e001a00500000e000e000006000100,8,3),(0x6094810000aa040005502000000e038000000160,5,4),(0x1ad6000000ee000000006e80000,19,5),(0x8ac8358000d0d7906c86a00dd00deb00050c008a,1,6),(0x80031800000c60068062000d000e300000c0008,3,7),(0x80c8000000d001900480000d000d000005000080,7,8),(0x8a481480005053104882800000000000050c008a,1,9),(0x59067380000dce0ce84e6000f000e78000dc0059,0,10),(0x5104630000098c00004c60000000c78000000051,0,11),(0x1902528000054a08c80a400000000000009c0019,0,12),(0x5900000000000004a84e60007000658000540059,0,13),(0xf39ce70000bb9c0005dce000000fcf80000001f3,0,14),(0xb318c600003318000198c00000000000000001b3,0,15),(0xf300000000bb9c0000000000000b8e80000001f3,0,16),(0xf30000000000000005dce00000074d80000001f3,0,17),(0x9ce70000bb9c00000000000000000000000000,106,18),(0xb5a80000077000000003740000,18,19),(0xbb00000000775a00000000000000000007bc01bb,0,20),(0x5ad68000000139c99ac0000000000000000000,78,21),(0xbb00000000000031899ac00000000000033401bb,0,22),(0x5ad68000775a00000000000000000000000000,105,23),(0xfb00000000ffde000000000bb00bae8007fc01fb,0,24),(0xfb000000000000000000000330032c80037401fb,0,25),(0xdef78000000000000000000000000000000000,135,26),(0xfb000000000000b5addee00770076d80037401fb,0,27)]
def R118 : List RR := r118.map (resolve [c16,c8,c57,c10,c12,c14,c40,c25,c36,c37,c65,c66,c67,c69,c94,c95,c93,c98,c100,c101,c103,c108,c110,c111,c114,c112,c116,c117] c118.2)
theorem hR118 : ∀ y ∈ R118, RInv c118.2.toFinset y := res_inv [c16,c8,c57,c10,c12,c14,c40,c25,c36,c37,c65,c66,c67,c69,c94,c95,c93,c98,c100,c101,c103,c108,c110,c111,c114,c112,c116,c117] (gcons g16 (gcons g8 (gcons g57 (gcons g10 (gcons g12 (gcons g14 (gcons g40 (gcons g25 (gcons g36 (gcons g37 (gcons g65 (gcons g66 (gcons g67 (gcons g69 (gcons g94 (gcons g95 (gcons g93 (gcons g98 (gcons g100 (gcons g101 (gcons g103 (gcons g108 (gcons g110 (gcons g111 (gcons g114 (gcons g112 (gcons g116 (gcons g117 gnil)))))))))))))))))))))))))))) r118 c118.2
def k118_4_0 : List Entry := [([23,56,623,124,96,60],[],[]),([23,342,862,36,76,52],[],[]),([39,58,92,348,18,92],[],[]),([39,58,92,366,108,32],[],[])]
set_option maxRecDepth 100000 in
theorem v118_4_0 : ∀ e ∈ k118_4_0, ¬ Live516.live basicOps goal 4 (wsOf c118.2 e).toFinset := level_sound hR118 4 k118_4_0 [] nil_dead (by decide +kernel)
def D118_4 : List Entry := k118_4_0
theorem w118_4 : ∀ e ∈ D118_4, ¬ Live516.live basicOps goal 4 (wsOf c118.2 e).toFinset := v118_4_0
def k118_5_0 : List Entry := [([19,300,20,25,837],[],[]),([19,300,20,25,1118],[],[]),([19,300,20,29,837],[],[]),([19,300,20,29,1118],[],[]),([19,300,20,55,56],[],[]),([19,300,20,55,60],[],[]),([19,300,20,87,56],[],[]),([19,300,20,87,60],[],[]),([19,300,20,87,76],[],[]),([19,300,20,837,94],[],[]),([23,56,623,124,96],[],[0]),([23,57,374,840,28],[],[]),([23,57,374,840,60],[],[]),([23,57,568,28,837],[],[]),([23,57,568,28,1118],[],[]),([23,60,623,124,96],[],[]),([23,61,568,28,837],[],[]),([23,61,568,28,1118],[],[]),([23,61,568,44,837],[],[]),([23,61,568,44,1118],[],[]),([23,87,88,840,28],[],[]),([23,87,92,840,28],[],[]),([23,87,92,840,44],[],[]),([23,119,88,840,28],[],[]),([23,119,92,840,28],[],[]),([23,119,92,840,44],[],[]),([23,119,108,840,44],[],[]),([23,119,108,840,76],[],[]),([23,296,44,837,94],[],[]),([23,310,56,28,837],[],[]),([23,310,56,28,1118],[],[]),([23,342,862,36,76],[],[1]),([23,590,52,60,837],[],[]),([23,591,68,76,348],[1],[]),([23,591,68,92,348],[],[]),([27,92,111,636,32],[],[]),([39,50,126,124,96],[],[]),([39,58,92,348,18],[],[2]),([39,58,92,348,86],[],[]),([39,58,92,366,108],[],[3]),([39,58,382,124,96],[],[3]),([39,62,382,124,96],[],[]),([39,590,52,60,77],[2],[]),([39,590,52,60,837],[],[]),([47,50,126,124,96],[],[]),([103,636,847,84,56],[],[]),([103,636,847,84,92],[17],[]),([103,636,847,84,108],[],[])]
set_option maxRecDepth 100000 in
theorem v118_5_0 : ∀ e ∈ k118_5_0, ¬ Live516.live basicOps goal 5 (wsOf c118.2 e).toFinset := level_sound hR118 5 k118_5_0 (D118_4.map (wsOf c118.2)) (map_dead w118_4) (by decide +kernel)
def D118_5 : List Entry := k118_5_0
theorem w118_5 : ∀ e ∈ D118_5, ¬ Live516.live basicOps goal 5 (wsOf c118.2 e).toFinset := v118_5_0
def k118_6_0 : List Entry := [([19,26,56,1109],[],[]),([19,26,56,1390],[],[]),([19,26,60,1109],[],[]),([19,26,60,1390],[],[]),([19,26,86,72],[],[]),([19,26,86,76],[],[]),([19,26,118,72],[],[]),([19,26,118,76],[],[]),([19,26,118,92],[],[]),([19,94,94,116],[],[]),([19,126,124,96],[27,20,26],[]),([19,300,20,25],[0,10,1,24],[0,1]),([19,300,20,29],[0,10,24],[2,3]),([19,300,20,55],[0,24,21],[4,5]),([19,300,20,63],[0,24,21],[]),([19,300,20,87],[0,17],[6,7,8]),([19,300,20,95],[0,27],[]),([19,300,20,837],[0,24,20],[9,0,2]),([19,300,20,863],[0,24,21],[]),([19,300,20,1118],[0,24,20,14,27,21],[1,3]),([19,300,1109,110],[],[9]),([19,375,652,52],[17],[]),([23,56,327,76],[],[]),([23,56,359,92],[],[]),([23,56,359,636],[17],[]),([23,56,575,64],[],[]),([23,56,575,364],[1],[]),([23,56,605,102],[],[]),([23,56,623,124],[],[10]),([23,56,847,116],[],[]),([23,56,1109,78],[],[]),([23,56,1109,110],[],[]),([23,56,1390,70],[],[]),([23,57,326,44],[],[]),([23,57,342,44],[],[]),([23,57,374,44],[],[]),([23,57,374,92],[],[]),([23,57,374,840],[],[11,12]),([23,57,568,28],[0,1,24],[12,13,14]),([23,57,568,1109],[],[13,0]),([23,57,568,1390],[],[14,1]),([23,60,103,92],[],[]),([23,60,359,92],[],[]),([23,60,359,636],[17],[]),([23,60,605,102],[],[]),([23,60,623,124],[],[15]),([23,60,847,116],[],[]),([23,60,1109,78],[],[]),([23,60,1109,110],[],[]),([23,60,1390,70],[],[])]
set_option maxRecDepth 100000 in
theorem v118_6_0 : ∀ e ∈ k118_6_0, ¬ Live516.live basicOps goal 6 (wsOf c118.2 e).toFinset := level_sound hR118 6 k118_6_0 (D118_5.map (wsOf c118.2)) (map_dead w118_5) (by decide +kernel)
def k118_6_1 : List Entry := [([23,61,326,40],[],[]),([23,61,342,40],[],[]),([23,61,374,40],[],[]),([23,61,374,92],[],[]),([23,61,568,28],[0,1,24],[16,17]),([23,61,568,44],[10,0,24],[18,19]),([23,61,568,1109],[],[16,18]),([23,61,568,1390],[],[17,19]),([23,62,118,92],[],[]),([23,70,72,861],[],[]),([23,70,72,1109],[],[]),([23,70,76,861],[],[]),([23,70,76,1109],[],[]),([23,71,88,28],[],[]),([23,86,29,296],[],[]),([23,86,29,316],[],[]),([23,86,41,316],[],[]),([23,86,61,328],[],[]),([23,86,70,76],[],[]),([23,86,86,88],[],[]),([23,86,86,92],[],[]),([23,86,86,124],[],[]),([23,86,118,88],[],[]),([23,86,118,92],[],[]),([23,86,118,108],[],[]),([23,87,88,840],[],[20,4]),([23,87,92,840],[],[21,22]),([23,87,840,28],[0,20],[21]),([23,87,840,44],[0,24,21],[4,22]),([23,87,840,76],[0,24,21],[20,21]),([23,94,94,116],[],[]),([23,95,840,44],[0,24,21],[]),([23,95,840,76],[0,24,21],[]),([23,119,88,840],[],[23,6]),([23,119,92,840],[],[24,25]),([23,119,108,840],[],[26,27]),([23,119,840,28],[0,27],[24,11]),([23,119,840,44],[0,17],[6,25,26]),([23,119,840,76],[0,17],[23,24,12,27]),([23,127,840,44],[0],[]),([23,127,840,76],[1,0,27],[]),([23,296,30,1109],[0],[16,0,18]),([23,296,30,1390],[0],[17,1,19]),([23,296,44,837],[0,24,20],[28,13,16]),([23,296,44,863],[0,24,21],[]),([23,296,44,1118],[0,24,20,14,27,21],[14,17]),([23,296,46,1109],[0],[]),([23,296,46,1390],[0],[]),([23,296,1109,110],[],[9,28]),([23,310,56,28],[10,1,24],[29,30])]
set_option maxRecDepth 100000 in
theorem v118_6_1 : ∀ e ∈ k118_6_1, ¬ Live516.live basicOps goal 6 (wsOf c118.2 e).toFinset := level_sound hR118 6 k118_6_1 (D118_5.map (wsOf c118.2)) (map_dead w118_5) (by decide +kernel)
def k118_6_2 : List Entry := [([23,310,56,1109],[],[29]),([23,310,56,1390],[],[30]),([23,310,94,588],[],[]),([23,310,316,54],[],[]),([23,310,316,1109],[10],[29]),([23,310,316,1390],[10],[30]),([23,310,846,36],[5],[]),([23,318,312,1109],[],[]),([23,318,312,1390],[],[]),([23,342,56,46],[1],[]),([23,342,56,60],[1,24,20,21],[]),([23,342,56,62],[6],[]),([23,342,57,76],[6,24,21],[]),([23,342,57,92],[],[]),([23,342,70,60],[3],[]),([23,342,70,72],[3],[]),([23,342,334,52],[3],[]),([23,342,350,52],[5],[]),([23,342,846,36],[3],[]),([23,342,862,36],[5],[31]),([23,343,72,76],[1,6],[]),([23,343,72,92],[],[]),([23,574,52,1109],[],[29]),([23,574,52,1390],[],[30]),([23,590,52,46],[1],[]),([23,590,52,60],[1,14,5,24,17],[32]),([23,590,52,62],[0],[]),([23,590,52,1109],[],[32]),([23,591,68,76],[1,0,24],[33]),([23,591,68,92],[],[34]),([23,591,68,364],[1],[33,34]),([23,639,140,112],[6],[10,15]),([23,847,52,108],[],[]),([23,1119,48,88],[],[]),([23,1119,48,92],[],[]),([23,1407,48,88],[],[]),([23,1407,48,92],[],[]),([27,60,1109,110],[],[28]),([27,76,1109,110],[],[]),([27,92,85,110],[],[]),([27,92,111,116],[],[]),([27,92,111,636],[24],[35]),([27,92,1390,34],[24,21],[35]),([27,94,356,110],[],[]),([31,86,118,108],[],[]),([31,118,380,54],[17],[]),([31,639,140,112],[6,27,26],[]),([39,50,108,102],[],[]),([39,50,126,124],[],[36]),([39,50,1381,44],[],[])]
set_option maxRecDepth 100000 in
theorem v118_6_2 : ∀ e ∈ k118_6_2, ¬ Live516.live basicOps goal 6 (wsOf c118.2 e).toFinset := level_sound hR118 6 k118_6_2 (D118_5.map (wsOf c118.2)) (map_dead w118_5) (by decide +kernel)
def k118_6_3 : List Entry := [([39,50,1662,36],[],[]),([39,58,60,1109],[],[29]),([39,58,60,1390],[],[30]),([39,58,72,1109],[],[]),([39,58,76,366],[],[]),([39,58,76,1109],[],[]),([39,58,76,1390],[],[]),([39,58,92,85],[20],[]),([39,58,92,348],[20,21,0,10,8],[37,38]),([39,58,92,366],[],[39]),([39,58,92,1390],[21],[]),([39,58,94,356],[20],[]),([39,58,108,102],[],[]),([39,58,120,1381],[],[]),([39,58,124,109],[],[]),([39,58,124,1381],[],[]),([39,58,126,124],[],[]),([39,58,126,380],[],[]),([39,58,316,1109],[10],[]),([39,58,316,1390],[10],[]),([39,58,364,102],[],[38]),([39,58,382,124],[],[40,39]),([39,58,1381,44],[],[]),([39,58,1662,36],[],[]),([39,62,364,102],[],[]),([39,62,382,124],[],[41]),([39,574,52,1109],[10],[]),([39,574,52,1390],[10],[]),([39,590,52,60],[3,2,24,14,5,17],[42,43]),([39,590,52,1109],[],[43]),([39,895,140,112],[10],[40,41]),([47,50,108,102],[],[]),([47,50,126,124],[],[44]),([47,50,1381,44],[],[]),([47,50,1662,36],[],[]),([47,54,118,92],[],[]),([47,54,308,1109],[],[]),([47,54,308,1390],[],[]),([47,86,118,108],[],[]),([47,118,92,862],[],[]),([47,118,380,70],[17],[]),([47,570,56,1109],[],[]),([47,570,56,1390],[],[]),([47,570,1381,44],[],[]),([47,895,140,112],[27,26,10],[]),([55,50,124,1381],[],[]),([55,50,1381,44],[],[]),([55,58,60,1109],[],[]),([55,58,316,1109],[],[]),([55,58,1381,44],[],[])]
set_option maxRecDepth 100000 in
theorem v118_6_3 : ∀ e ∈ k118_6_3, ¬ Live516.live basicOps goal 6 (wsOf c118.2 e).toFinset := level_sound hR118 6 k118_6_3 (D118_5.map (wsOf c118.2)) (map_dead w118_5) (by decide +kernel)
def k118_6_4 : List Entry := [([55,78,66,108],[],[]),([55,78,66,124],[],[]),([55,94,66,124],[],[]),([55,574,52,349],[],[]),([55,574,52,1109],[],[]),([55,590,52,861],[],[]),([55,590,52,1109],[],[]),([55,855,56,88],[],[]),([55,855,56,92],[],[]),([55,855,92,68],[],[]),([55,877,598,56],[],[]),([55,877,598,60],[],[]),([63,50,1381,44],[],[]),([63,54,72,1109],[],[]),([63,54,76,846],[17],[]),([63,54,76,1109],[],[]),([63,54,86,88],[],[]),([63,54,86,92],[],[]),([63,86,74,76],[],[]),([63,86,74,92],[],[]),([63,86,74,124],[],[]),([63,86,74,300],[],[]),([71,51,300,20],[20],[]),([71,55,88,296],[],[]),([71,58,316,21],[],[]),([71,59,140,588],[],[]),([71,62,86,124],[],[]),([71,62,118,108],[],[]),([71,78,118,108],[],[]),([71,94,70,88],[],[]),([71,94,70,92],[],[]),([71,374,846,36],[26],[]),([71,374,862,36],[3],[]),([71,574,52,46],[],[]),([71,574,78,52],[],[]),([71,574,78,68],[],[]),([71,574,94,52],[],[]),([71,574,94,68],[],[]),([71,574,382,52],[26],[]),([71,574,582,40],[21],[]),([71,574,582,56],[],[]),([71,590,52,46],[],[]),([71,590,52,62],[21],[]),([71,606,52,46],[],[]),([71,606,52,62],[21],[]),([71,847,52,88],[],[]),([71,847,52,92],[],[]),([71,863,52,88],[],[]),([71,863,52,92],[],[31]),([71,1119,68,92],[3,5],[])]
set_option maxRecDepth 100000 in
theorem v118_6_4 : ∀ e ∈ k118_6_4, ¬ Live516.live basicOps goal 6 (wsOf c118.2 e).toFinset := level_sound hR118 6 k118_6_4 (D118_5.map (wsOf c118.2)) (map_dead w118_5) (by decide +kernel)
def k118_6_5 : List Entry := [([71,1119,68,124],[3,5],[]),([103,78,66,92],[],[]),([103,636,839,56],[17],[]),([103,636,847,80],[17],[]),([103,636,847,84],[17],[45,46,47]),([103,847,68,92],[17],[46]),([103,847,68,108],[],[47]),([295,58,118,92],[],[]),([295,62,118,92],[],[]),([295,62,118,380],[17],[]),([295,78,94,116],[],[]),([295,126,124,96],[27,18,6,20],[]),([295,590,52,334],[17],[]),([295,590,52,1109],[],[]),([295,590,350,52],[],[]),([295,590,1381,76],[],[]),([303,54,72,1109],[],[]),([303,54,76,1109],[],[]),([303,54,76,1390],[],[46]),([303,54,92,85],[],[]),([303,54,92,1390],[],[47]),([303,54,94,356],[],[]),([303,54,108,102],[],[]),([303,54,120,1381],[],[]),([303,54,124,109],[],[]),([303,54,124,1381],[],[]),([303,54,126,124],[],[]),([303,54,126,380],[],[]),([303,54,1381,44],[],[]),([303,54,1662,36],[],[45]),([303,62,118,92],[],[]),([303,62,118,380],[17],[]),([303,78,64,1109],[],[]),([303,78,68,334],[17],[]),([303,78,68,1109],[],[]),([303,118,92,862],[],[]),([303,383,140,112],[6],[]),([303,606,48,56],[7,3,24,9,21],[]),([303,1119,56,124],[],[]),([303,1119,60,80],[],[]),([303,1119,60,84],[],[]),([303,1119,60,116],[],[]),([319,54,76,605],[],[33]),([319,54,76,1109],[],[32]),([319,54,92,85],[],[]),([319,54,92,605],[],[34]),([319,54,94,356],[],[]),([319,54,124,621],[],[]),([319,54,124,1381],[],[]),([319,54,621,36],[],[])]
set_option maxRecDepth 100000 in
theorem v118_6_5 : ∀ e ∈ k118_6_5, ¬ Live516.live basicOps goal 6 (wsOf c118.2 e).toFinset := level_sound hR118 6 k118_6_5 (D118_5.map (wsOf c118.2)) (map_dead w118_5) (by decide +kernel)
def k118_6_6 : List Entry := [([319,54,1381,44],[],[]),([319,86,74,88],[],[]),([319,86,74,92],[],[]),([319,86,302,52],[],[]),([319,590,48,1109],[],[]),([319,1119,64,88],[8],[]),([319,1119,64,124],[8],[]),([327,58,118,88],[],[]),([327,58,118,92],[],[]),([327,58,118,108],[],[]),([327,62,118,108],[],[]),([327,94,70,92],[],[]),([327,94,70,124],[],[]),([335,50,118,108],[],[]),([335,51,300,20],[20,21],[]),([335,70,78,112],[],[]),([335,70,78,116],[],[]),([335,86,29,36],[],[]),([335,86,70,76],[],[]),([335,86,78,116],[],[]),([335,382,862,32],[8],[]),([335,590,48,42],[],[]),([349,847,86,92],[8],[]),([349,847,86,108],[],[]),([349,847,86,124],[],[]),([575,54,76,93],[],[42]),([575,54,76,1109],[],[43]),([575,54,78,108],[],[]),([575,54,92,85],[],[]),([575,54,94,356],[],[]),([575,54,124,1381],[],[]),([575,54,1381,44],[],[]),([575,66,1381,44],[],[]),([575,74,124,1381],[],[]),([575,74,1381,44],[],[]),([591,50,118,108],[],[]),([847,86,90,124],[],[]),([1109,62,59,60],[],[]),([1109,62,59,88],[],[]),([1109,62,59,92],[],[]),([1109,62,63,52],[],[]),([1109,62,63,112],[],[]),([1109,62,63,116],[],[]),([1109,62,95,116],[],[]),([1135,50,74,108],[],[]),([1135,86,90,108],[],[])]
set_option maxRecDepth 100000 in
theorem v118_6_6 : ∀ e ∈ k118_6_6, ¬ Live516.live basicOps goal 6 (wsOf c118.2 e).toFinset := level_sound hR118 6 k118_6_6 (D118_5.map (wsOf c118.2)) (map_dead w118_5) (by decide +kernel)
def D118_6 : List Entry := k118_6_0 ++ (k118_6_1 ++ (k118_6_2 ++ (k118_6_3 ++ (k118_6_4 ++ (k118_6_5 ++ (k118_6_6))))))
theorem w118_6 : ∀ e ∈ D118_6, ¬ Live516.live basicOps goal 6 (wsOf c118.2 e).toFinset := (app_dead v118_6_0 (app_dead v118_6_1 (app_dead v118_6_2 (app_dead v118_6_3 (app_dead v118_6_4 (app_dead v118_6_5 v118_6_6))))))
def k118_7_0 : List Entry := [([19,26,56],[6,0,10,24],[0,1]),([19,26,60],[6,24],[2,3]),([19,26,86],[0,24,21],[4,5]),([19,26,94],[0,24,21],[]),([19,26,118],[0,17],[6,7,8]),([19,26,126],[0],[]),([19,26,342],[6,20],[]),([19,26,1381],[0],[0,2]),([19,26,1662],[0],[1,3]),([19,62,1381],[6],[]),([19,62,1662],[6],[]),([19,78,86],[6,24,21],[]),([19,78,1381],[6],[]),([19,94,86],[6],[]),([19,94,94],[6,24,21,17],[9]),([19,94,118],[6,24,21],[]),([19,94,126],[6,24,21],[]),([19,94,298],[0,6],[]),([19,108,102],[6,21],[]),([19,108,327],[0],[]),([19,126,102],[6,24,21],[]),([19,126,124],[6,21,27,26],[10]),([19,300,20],[10,3,14,5,20,24,27],[11,12,13,14,15,16,17,18,19]),([19,300,1109],[0,24,6,20],[20,17]),([19,300,1135],[0,24,21],[18]),([19,300,1390],[0,24,6,20,14,27,21],[19]),([19,343,76],[0],[]),([19,375,76],[0],[]),([19,375,108],[0,24,26],[]),([19,375,652],[21,17,0],[21]),([19,574,1381],[6],[]),([19,574,1662],[6],[]),([19,590,1381],[6],[]),([19,1119,52],[24,21],[]),([19,1119,132],[14,24,21,5],[]),([19,1381,44],[6,24,26],[]),([19,1381,126],[22,26],[20]),([19,1407,52],[24,21],[]),([19,1662,36],[24,6,20,27,14,21],[21]),([23,54,78],[10],[]),([23,54,94],[10,24,21],[]),([23,54,126],[10],[]),([23,54,1381],[10],[2]),([23,54,1662],[10],[3]),([23,56,311],[0],[]),([23,56,327],[0,1,24,21],[22]),([23,56,359],[0,17],[23,24]),([23,56,575],[6,1],[25,26]),([23,56,591],[6,24,21],[]),([23,56,605],[6,24,10,20,21,0],[27,26])]
set_option maxRecDepth 100000 in
theorem v118_7_0 : ∀ e ∈ k118_7_0, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_0 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_1 : List Entry := [([23,56,623],[6,24],[28]),([23,56,847],[10,24,21,17],[29]),([23,56,1109],[10,24,20],[30,31]),([23,56,1135],[10,24,21],[]),([23,56,1390],[10,24,21,27,14],[32,24]),([23,57,326],[10],[33,25]),([23,57,342],[10,24,21],[34,22]),([23,57,374],[10,17],[35,36,37]),([23,57,568],[0,10,1,24],[38,11,37,39,40]),([23,57,598],[1],[]),([23,57,846],[14,1],[]),([23,57,1381],[10],[2,39]),([23,57,1662],[10],[3,40]),([23,60,55],[14],[]),([23,60,71],[24,21],[]),([23,60,103],[24,17],[41]),([23,60,311],[0],[]),([23,60,327],[0,24,21],[]),([23,60,359],[0,17],[42,43]),([23,60,575],[6],[]),([23,60,591],[6,24,21],[]),([23,60,605],[6,24,20,21],[44]),([23,60,623],[6,24],[45]),([23,60,847],[14,24,21,17],[46]),([23,60,1109],[24,20],[47,48]),([23,60,1135],[24,21],[]),([23,60,1390],[24,21,27,14],[49,43]),([23,61,326],[14],[50]),([23,61,342],[24,21],[51]),([23,61,374],[24,17],[52,53]),([23,61,568],[0,1,24],[54,55,56,57]),([23,61,598],[1],[]),([23,61,846],[14,1],[]),([23,61,1381],[10,24],[56]),([23,61,1662],[10,24],[57]),([23,62,70],[10,14],[]),([23,62,86],[10,3,24,21],[]),([23,62,118],[10,27,17],[58]),([23,62,1381],[10,24],[]),([23,62,1662],[10,24],[]),([23,70,72],[10,24,17],[59,60]),([23,70,76],[24,17],[61,62]),([23,70,78],[10,14],[]),([23,70,94],[14,24,21],[]),([23,70,877],[6],[59,61]),([23,70,1381],[14],[60,62]),([23,71,56],[0,5],[25]),([23,71,88],[10,5],[63]),([23,71,92],[10,14,5],[]),([23,78,70],[10],[])]
set_option maxRecDepth 100000 in
theorem v118_7_1 : ∀ e ∈ k118_7_1, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_1 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_2 : List Entry := [([23,78,86],[14,24,21],[]),([23,78,877],[6],[]),([23,78,1381],[14],[]),([23,86,29],[20],[64,65]),([23,86,41],[0],[64,66]),([23,86,42],[0],[]),([23,86,61],[6],[65,66,67]),([23,86,62],[6,24,21],[]),([23,86,70],[10,24,21],[5,68]),([23,86,72],[10,24,20,21],[]),([23,86,73],[10,24,21],[5,67]),([23,86,76],[24,20,21],[]),([23,86,77],[10,24,21],[]),([23,86,78],[10,24],[]),([23,86,86],[14,24,21,17],[69,70,71]),([23,86,94],[14],[]),([23,86,118],[24,17,21],[72,73,74]),([23,86,126],[24,21],[]),([23,86,334],[10],[]),([23,87,56],[0],[64]),([23,87,76],[6],[65,22]),([23,87,88],[10],[63,75]),([23,87,92],[10,20],[76]),([23,87,840],[0,24,21],[77,78,79,75,76]),([23,94,70],[10],[]),([23,94,78],[10,24,21],[]),([23,94,86],[14],[]),([23,94,94],[14,24,21,17],[80]),([23,94,118],[24,21],[]),([23,94,126],[24,21],[]),([23,94,298],[0],[65]),([23,94,318],[6,21],[64]),([23,95,568],[20],[]),([23,95,840],[0,24,21],[81,82]),([23,118,42],[0,24,26],[]),([23,118,62],[6],[]),([23,118,72],[10,24,27,26],[]),([23,118,76],[24,27,26],[]),([23,118,78],[10,24],[]),([23,118,92],[24,27,26],[]),([23,118,110],[24,21],[]),([23,118,614],[20],[]),([23,118,622],[],[]),([23,119,56],[0,26],[]),([23,119,76],[6,26],[]),([23,119,88],[10],[63,83]),([23,119,92],[10,27],[84]),([23,119,108],[24],[36,53,85]),([23,119,840],[0,17],[86,87,88,83,84,85,37]),([23,126,70],[10],[])]
set_option maxRecDepth 100000 in
theorem v118_7_2 : ∀ e ∈ k118_7_2, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_2 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_3 : List Entry := [([23,126,102],[24,21],[]),([23,126,614],[],[]),([23,126,622],[],[]),([23,127,840],[0,27,1],[89,90]),([23,296,30],[0,3,1,10,14,5,20,24,27],[54,11,55,78,81,87,89,91,92]),([23,296,44],[10,2,3,14,5,20,24,27],[38,54,79,82,88,90,93,94,95]),([23,296,46],[0,10,3,24],[96,97]),([23,296,1109],[0,24,20],[98,17,91,93,96,39,56]),([23,296,1135],[0,24,21],[18,94]),([23,296,1390],[0,24,20,14,27,21],[19,92,95,97,40,57]),([23,310,56],[0,6,10,3,1,8,24],[99,100,101]),([23,310,94],[],[102]),([23,310,316],[6,3,10,24],[99,103,102,104,105]),([23,310,846],[5],[106]),([23,310,1381],[10],[100,104]),([23,310,1662],[10],[101,105]),([23,318,86],[8],[]),([23,318,312],[0,6,1,24],[107,108]),([23,318,1381],[0,10],[107]),([23,318,1662],[0,10],[108]),([23,342,56],[6,24,20,1,21],[109,110,111]),([23,342,57],[6,24,21],[112,113]),([23,342,61],[6],[]),([23,342,70],[3],[114,115]),([23,342,78],[3],[]),([23,342,318],[6,20,21],[]),([23,342,334],[3],[116]),([23,342,350],[5],[117]),([23,342,838],[6,3],[]),([23,342,846],[3],[118]),([23,342,854],[],[]),([23,342,862],[5],[119]),([23,343,72],[0,6,1],[120,121]),([23,350,38],[0],[]),([23,350,70],[3],[]),([23,375,72],[0],[]),([23,375,108],[0],[23,42]),([23,375,652],[17,0],[24,43]),([23,566,78],[3],[]),([23,566,1381],[6,10],[107]),([23,566,1662],[6,10],[108]),([23,574,52],[0,10,8,1,3,24],[99,122,123]),([23,574,70],[],[103]),([23,574,1381],[10],[122,104]),([23,574,1662],[10],[123,105]),([23,575,380],[10,7,8],[]),([23,582,78],[8],[]),([23,582,1381],[],[]),([23,590,52],[0,14,5,1,24,17],[124,125,126,127]),([23,590,70],[5],[])]
set_option maxRecDepth 100000 in
theorem v118_7_3 : ∀ e ∈ k118_7_3, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_3 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_4 : List Entry := [([23,590,1381],[14],[127]),([23,591,68],[0,24,1],[128,129,130]),([23,591,380],[14],[130,26]),([23,607,68],[0,6,21],[]),([23,621,118],[6],[27,44]),([23,639,68],[0],[]),([23,639,140],[6],[131,28,45]),([23,847,48],[10,14],[]),([23,847,52],[10,3,24,8,5],[132]),([23,863,48],[10,3],[]),([23,863,52],[10,8,3],[116]),([23,895,48],[10,27],[]),([23,895,52],[10,24,26],[]),([23,1119,48],[5],[133,134]),([23,1119,52],[5],[117]),([23,1119,132],[14,5],[29,46]),([23,1381,78],[6],[30,47]),([23,1381,126],[24],[31,48,98]),([23,1407,48],[24],[135,136]),([23,1407,52],[],[]),([23,1662,70],[6],[32,49]),([27,60,1109],[0,24,6,20],[137,93]),([27,60,1135],[0,24,21],[94]),([27,60,1390],[0,24,6,20,14,27,21],[95]),([27,62,1381],[0],[96]),([27,62,1662],[0],[97]),([27,72,1109],[0,24,6,17],[]),([27,76,1109],[0,24,6,20],[138]),([27,76,1135],[0,24,21],[]),([27,76,1390],[0,24,6,20,27,4,21],[]),([27,78,1381],[0],[]),([27,92,85],[0,24,6,21],[139]),([27,92,103],[0,24,9,27],[]),([27,92,111],[0,24,27],[140,141]),([27,92,1390],[0,24,21,6,27,14],[142,141]),([27,94,118],[0,24,9,27],[]),([27,94,126],[0,24,21],[]),([27,94,356],[0,9],[143]),([27,94,382],[0,24,21,27],[]),([27,108,102],[0,21,6],[]),([27,120,1381],[0,24,27,6],[]),([27,124,87],[0,24,21],[]),([27,124,109],[0,24,6,20,14,21],[]),([27,124,1381],[0,24,9,26],[]),([27,126,102],[0,24,21],[]),([27,126,124],[0,21,27,6,14],[]),([27,126,380],[0,24,6,20,14,21],[]),([27,1381,44],[0,24,6,9,26],[]),([27,1381,126],[22,26],[143,137,138,98]),([27,1407,52],[0,24,21],[])]
set_option maxRecDepth 100000 in
theorem v118_7_4 : ∀ e ∈ k118_7_4, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_4 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_5 : List Entry := [([27,1662,36],[0,24,6,20,14,27,21],[]),([31,54,1381],[0],[]),([31,54,1662],[0],[]),([31,70,877],[0],[]),([31,70,1381],[0],[]),([31,86,118],[0,17,24,21],[144]),([31,86,126],[0,24,21],[]),([31,86,318],[0,6,21],[]),([31,118,92],[24,27,26],[]),([31,118,110],[0,24,21],[]),([31,118,380],[24,21,0,14,17,26],[145]),([31,118,614],[20,21],[]),([31,310,1381],[0],[]),([31,310,1662],[0],[]),([31,342,41],[0],[]),([31,342,318],[0,6,21],[]),([31,607,64],[0,21],[]),([31,621,118],[6],[]),([31,639,64],[0],[]),([31,639,140],[6,27,26],[146]),([31,1381,78],[6],[]),([31,1381,126],[24],[20]),([31,1407,48],[21],[]),([31,1662,70],[6,27],[145]),([39,50,78],[6],[]),([39,50,94],[6,24,21],[]),([39,50,108],[6,20,21],[147]),([39,50,126],[6,24],[148]),([39,50,1381],[20],[149]),([39,50,1662],[21],[150]),([39,58,60],[0,6,24],[99,151,152]),([39,58,72],[10,14,6,24,17],[153]),([39,58,76],[6,2,24],[154,155,156]),([39,58,78],[6],[]),([39,58,88],[24,20,6,21],[]),([39,58,92],[6,20,24,0,10,8],[157,158,159,160]),([39,58,94],[6,24,21],[161]),([39,58,108],[6,20,21],[162]),([39,58,120],[6,27,24],[163]),([39,58,124],[24,6,10,8],[164,165]),([39,58,126],[6,24],[166,167]),([39,58,316],[6,3,10,24],[168,169]),([39,58,364],[6,21,0,10,8],[170,158]),([39,58,382],[27],[171,154,159]),([39,58,1381],[20,10],[172,161,151,153,155,163,165,100,168]),([39,58,1662],[21,27,10,17],[173,167,152,156,160,101,169]),([39,62,364],[24,20,21],[174]),([39,62,382],[27],[175]),([39,62,1381],[20],[]),([39,62,1662],[21],[])]
set_option maxRecDepth 100000 in
theorem v118_7_5 : ∀ e ∈ k118_7_5, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_5 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_6 : List Entry := [([39,70,94],[10,24,21],[]),([39,70,1381],[10],[]),([39,78,70],[10,8],[]),([39,78,86],[10,24,21],[]),([39,78,1133],[10],[]),([39,78,1381],[10],[]),([39,86,72],[8,24,20,0,10,21],[]),([39,86,76],[24,8,20,21],[]),([39,86,94],[10],[]),([39,86,126],[10,24,21],[]),([39,94,70],[10,24,21],[]),([39,94,86],[10],[]),([39,94,118],[10,24,21],[]),([39,94,846],[],[102]),([39,94,862],[2],[]),([39,118,92],[24,27,8,26],[]),([39,118,110],[10,24,21],[]),([39,126,70],[10],[]),([39,126,102],[10,24,21],[]),([39,375,108],[0],[]),([39,375,652],[17,0],[]),([39,574,52],[0,10,2,24,7],[176,177]),([39,574,70],[],[103]),([39,574,1381],[],[151,176,168,104]),([39,574,1662],[],[152,177,169,105]),([39,590,52],[0,2,8,14,5,24,17],[178,179]),([39,590,1381],[14],[179]),([39,847,52],[5],[106]),([39,863,52],[8,21],[]),([39,863,60],[10,24,21],[]),([39,877,118],[10],[170,174]),([39,895,52],[8,24,26],[]),([39,895,140],[10],[180,171,175]),([39,1119,48],[5],[]),([39,1119,52],[5],[]),([39,1119,132],[10],[]),([39,1381,94],[10],[]),([39,1381,126],[10],[]),([39,1407,48],[10],[]),([39,1407,52],[],[]),([39,1662,86],[10],[]),([47,50,94],[0,24,21],[]),([47,50,108],[6,20,21],[181]),([47,50,126],[0,24],[182]),([47,50,1381],[20,0],[183]),([47,50,1662],[21,0],[184]),([47,54,86],[0,8,24,21],[]),([47,54,118],[0,8,17],[185]),([47,54,308],[0,6,1,24],[186,187]),([47,54,1381],[0],[2,186])]
set_option maxRecDepth 100000 in
theorem v118_7_6 : ∀ e ∈ k118_7_6, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_6 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_7 : List Entry := [([47,54,1662],[0],[3,187]),([47,70,842],[],[]),([47,70,862],[],[]),([47,70,1133],[0],[]),([47,70,1381],[0],[]),([47,86,78],[0,24,21],[]),([47,86,118],[0,17,24,21],[188]),([47,86,126],[0,24,21],[]),([47,86,334],[0,8,21],[]),([47,118,78],[0],[]),([47,118,92],[24,27,10,26],[189]),([47,118,110],[0,24,21],[]),([47,118,380],[24,21,0,14,17,26],[190]),([47,118,878],[21],[189]),([47,570,56],[0,1,24],[191,192]),([47,570,94],[],[]),([47,570,1381],[],[193,2,191,186,107]),([47,570,1662],[],[3,192,187,108]),([47,606,48],[0,3,8,24,20,21],[]),([47,863,48],[8],[]),([47,877,118],[10],[]),([47,895,48],[24,26],[]),([47,895,140],[27,26,10],[194]),([47,1381,94],[10],[]),([47,1381,126],[10],[]),([47,1407,48],[21],[]),([47,1662,86],[27,10],[190]),([55,50,78],[6],[]),([55,50,94],[6,24,21],[]),([55,50,108],[6,20,17],[]),([55,50,124],[24,18,6],[195]),([55,50,1381],[20,17],[196,195]),([55,58,60],[0,6,24,17],[197]),([55,58,78],[6],[]),([55,58,94],[6,24,21],[]),([55,58,108],[6,20,17],[]),([55,58,316],[6,5,24,17],[198]),([55,58,1381],[20],[199,197,198]),([55,62,70],[10],[]),([55,62,86],[14,24,21],[]),([55,62,365],[6],[]),([55,62,846],[10],[]),([55,62,1381],[14],[]),([55,78,66],[10,24,17],[200,201]),([55,78,70],[10,3],[]),([55,78,86],[10,24,21],[]),([55,78,846],[],[]),([55,78,1133],[10],[]),([55,78,1381],[10],[]),([55,86,74],[14,5,24,21],[])]
set_option maxRecDepth 100000 in
theorem v118_7_7 : ∀ e ∈ k118_7_7, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_7 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_8 : List Entry := [([55,86,78],[14,24,21],[]),([55,86,94],[10],[]),([55,86,124],[24,18,20,21],[]),([55,94,66],[14,4,24,21,17],[202]),([55,94,70],[14,24,21],[]),([55,94,86],[10],[]),([55,94,846],[],[]),([55,94,862],[4],[]),([55,574,52],[0,4,24,17],[203,204]),([55,574,70],[],[]),([55,574,365],[6],[203]),([55,574,1381],[],[197,204,198]),([55,590,52],[0,4,10,3,5,24,17],[205,206]),([55,590,70],[14,3],[]),([55,590,1133],[10],[205]),([55,590,1381],[10],[206]),([55,839,56],[3],[]),([55,839,60],[3],[]),([55,839,92],[6,3],[]),([55,839,124],[6,14],[]),([55,847,48],[10],[]),([55,847,52],[3],[]),([55,855,56],[6],[207,208]),([55,855,60],[],[]),([55,855,92],[6],[209]),([55,863,48],[14],[]),([55,863,52],[],[]),([55,863,60],[14,24,21],[]),([55,877,598],[10],[210,211]),([55,1119,48],[3],[]),([55,1119,52],[3],[]),([55,1381,94],[14],[]),([63,50,94],[0,24,21],[]),([63,50,108],[6,20,17],[]),([63,50,1381],[20],[212]),([63,54,72],[10,24,1,17],[213]),([63,54,76],[24,1,14,27,17],[214,215]),([63,54,86],[0,24,21],[216,217]),([63,54,94],[0,24,21],[]),([63,54,365],[0,1],[]),([63,54,862],[17],[214]),([63,54,1381],[0],[213,215]),([63,70,862],[17],[]),([63,70,1133],[2,0],[]),([63,70,1381],[0],[]),([63,86,66],[0,24,21],[]),([63,86,74],[0,20,21,17],[218,219,220,221]),([63,86,78],[0,24,21],[]),([63,86,334],[0,21],[221]),([63,606,48],[0,5,24,20,21],[])]
set_option maxRecDepth 100000 in
theorem v118_7_8 : ∀ e ∈ k118_7_8, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_8 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_9 : List Entry := [([63,855,56],[1],[]),([63,863,48],[],[]),([63,1381,94],[14],[]),([71,50,42],[0,1],[]),([71,50,78],[6],[]),([71,50,94],[6],[]),([71,50,126],[6,24,21],[]),([71,51,56],[0,6],[]),([71,51,300],[20],[222]),([71,55,56],[0],[66]),([71,55,88],[10,24,21],[223,67]),([71,55,92],[24,21],[]),([71,55,296],[20],[222,223]),([71,58,60],[24,9,6,21],[]),([71,58,76],[6,10,24,9,21],[110,120]),([71,58,78],[6,10],[111]),([71,58,88],[6,24,9,17],[]),([71,58,92],[6,24,9,21],[121]),([71,58,94],[6],[]),([71,58,120],[24,27,6,9],[]),([71,58,124],[24,21],[]),([71,58,126],[6,24,21],[]),([71,58,316],[6,24,9,21],[224]),([71,59,60],[0],[]),([71,59,76],[0,24,21],[]),([71,59,92],[6,24,21],[112]),([71,59,104],[6,24,21],[]),([71,59,108],[6,24,21],[113]),([71,59,136],[6,24,21],[]),([71,59,140],[6,24,21],[225]),([71,59,588],[6,21,24],[225]),([71,62,70],[10,24,21],[]),([71,62,78],[10],[]),([71,62,86],[14,24,21,17],[226]),([71,62,94],[14],[]),([71,62,118],[24,17,21],[227]),([71,62,126],[24,21],[]),([71,62,846],[10],[]),([71,63,588],[6,21],[]),([71,71,56],[0,3],[]),([71,71,88],[10,3,24,21],[]),([71,71,92],[10,24,21],[]),([71,78,66],[10,24,21],[]),([71,78,70],[10,3],[]),([71,78,86],[10],[]),([71,78,118],[10,17,21],[228]),([71,78,846],[21],[]),([71,87,56],[0,5],[]),([71,87,140],[14,24,21],[]),([71,94,66],[14,24,21],[])]
set_option maxRecDepth 100000 in
theorem v118_7_9 : ∀ e ∈ k118_7_9, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_9 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_10 : List Entry := [([71,94,70],[14],[229,230]),([71,94,86],[10],[]),([71,118,74],[24,26],[]),([71,118,78],[24,21],[]),([71,118,94],[10],[]),([71,118,108],[24,27,20,21],[]),([71,119,76],[20,26,21],[]),([71,119,124],[24,21],[]),([71,126,66],[24,21],[]),([71,126,70],[24,21],[]),([71,126,86],[10,24,21],[]),([71,374,78],[20],[]),([71,374,846],[26,21],[231]),([71,374,862],[3,21],[232]),([71,375,124],[0,24,21],[]),([71,382,70],[],[]),([71,382,846],[21],[]),([71,574,37],[0,6,24,9,21],[]),([71,574,49],[0,21],[]),([71,574,52],[0,20,21],[233]),([71,574,53],[0,24,9,21],[]),([71,574,70],[],[]),([71,574,78],[],[234,235]),([71,574,86],[],[]),([71,574,94],[],[236,237]),([71,574,374],[21],[]),([71,574,382],[21,26],[238]),([71,574,582],[21],[239,240]),([71,590,52],[0,24,21],[241,242]),([71,590,70],[3],[]),([71,590,86],[],[]),([71,606,52],[0,24,21],[243,244]),([71,606,70],[5],[]),([71,606,86],[],[]),([71,839,56],[3,24,21],[]),([71,839,60],[24,21],[]),([71,839,72],[6,3],[]),([71,839,92],[6,3],[]),([71,847,48],[10,24,21],[]),([71,847,52],[3,10],[245,246,118]),([71,855,56],[6,24,21],[]),([71,855,60],[24,21],[]),([71,855,72],[6,5],[]),([71,855,76],[0],[]),([71,855,92],[6,5],[]),([71,855,140],[6,24,21],[]),([71,863,48],[14,24,21],[]),([71,863,52],[5],[247,248,119]),([71,887,56],[6,24,21],[]),([71,887,60],[24,21],[])]
set_option maxRecDepth 100000 in
theorem v118_7_10 : ∀ e ∈ k118_7_10, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_10 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_11 : List Entry := [([71,887,72],[6,20],[]),([71,887,76],[0],[]),([71,887,92],[6,23],[]),([71,887,124],[6,24,21],[]),([71,895,48],[24,21],[]),([71,895,52],[23,24,21],[238]),([71,1119,48],[10,24,21],[]),([71,1119,52],[14,10,3,5],[]),([71,1119,64],[3],[]),([71,1119,68],[20,21,3,5],[249,250]),([71,1151,48],[10,24,21],[]),([71,1151,52],[3,23],[]),([79,50,126],[0,24,21],[]),([79,54,118],[0,24,21],[]),([79,54,126],[0,24,21],[]),([79,116,59],[0,24,21,23],[]),([79,116,63],[0,24,21,23],[]),([79,118,74],[0,24,21,23],[]),([79,118,78],[0,24,21,23],[]),([79,374,78],[],[]),([79,887,56],[0,24,21],[]),([79,887,72],[23],[]),([79,887,124],[27,23,24,21],[]),([79,895,48],[0,24,21,23],[]),([103,58,78],[6],[]),([103,58,110],[6,24,21,23],[]),([103,62,70],[10],[]),([103,62,78],[10,27],[]),([103,62,102],[24,21],[]),([103,62,110],[24,23,21],[]),([103,78,66],[10,17,24,26],[251]),([103,78,70],[10,3],[]),([103,78,102],[10,24,21],[]),([103,92,839],[10,24,26],[]),([103,92,847],[10],[]),([103,92,855],[24,21],[]),([103,92,863],[24,21],[]),([103,92,1119],[10,24,21],[]),([103,110,74],[24,23,21],[]),([103,110,94],[10,23,24,21],[]),([103,636,54],[24,18,20,27,17,21],[]),([103,636,839],[10,18,17],[252]),([103,636,847],[10,17],[253,254]),([103,839,60],[],[]),([103,847,52],[3,24,26],[]),([103,847,64],[27,17],[253]),([103,847,68],[27,17],[255,256,254]),([103,871,60],[],[]),([103,879,52],[23],[231]),([103,1135,52],[3],[232])]
set_option maxRecDepth 100000 in
theorem v118_7_11 : ∀ e ∈ k118_7_11, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_11 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_12 : List Entry := [([111,50,110],[0,24,21],[]),([111,54,102],[0,24,21],[]),([111,54,110],[0,24,21],[]),([111,102,66],[0,24,21],[]),([111,102,334],[0,24,23,21],[]),([111,871,56],[],[]),([111,879,48],[],[]),([295,58,118],[6,3,17],[257]),([295,58,1381],[6],[2,191]),([295,58,1662],[6],[3,192]),([295,62,70],[0],[]),([295,62,86],[0,24,21],[]),([295,62,118],[0,17],[258,259]),([295,62,1381],[6],[]),([295,62,1662],[27,6],[259]),([295,78,66],[6],[]),([295,78,86],[6,24,21],[]),([295,78,94],[6,24,21,17],[260]),([295,78,350],[6,17,20],[]),([295,78,1381],[6],[]),([295,94,66],[6,10],[]),([295,94,86],[6],[]),([295,94,118],[6,24,9],[]),([295,94,126],[6,24,21],[]),([295,94,862],[14],[]),([295,108,102],[6,21],[]),([295,126,66],[6,24,26],[]),([295,126,102],[6,24,21],[]),([295,126,124],[6,18,20,27],[261]),([295,590,52],[6,8,14,3,27,24,17],[262,263]),([295,590,350],[17],[264,262]),([295,590,1381],[14],[265,263]),([295,1119,52],[24,21],[264]),([295,1119,132],[10,24,21],[]),([295,1381,44],[6,24,9,23,10],[193,265]),([295,1381,126],[22,23,10],[]),([295,1407,52],[24,21],[]),([295,1662,36],[24,6,20,27,14,21],[252]),([303,50,1381],[10],[]),([303,50,1662],[10],[253]),([303,54,72],[24,7,17],[266]),([303,54,76],[14,0,6,24,7,3],[255,267,268]),([303,54,78],[0,14],[]),([303,54,88],[10,3,24,20,7,21],[]),([303,54,92],[24,7,0],[269,256,270]),([303,54,94],[0,24,21],[271]),([303,54,108],[7,20,21],[272]),([303,54,120],[27,24,7],[273]),([303,54,124],[24,7,3],[274,275]),([303,54,126],[0,24],[276,277])]
set_option maxRecDepth 100000 in
theorem v118_7_12 : ∀ e ∈ k118_7_12, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_12 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_13 : List Entry := [([303,54,1381],[20,10],[278,271,151,266,267,273,275,122,176]),([303,54,1662],[21,27,10,17],[279,277,254,152,268,270,123,177]),([303,62,70],[0],[]),([303,62,86],[0,24,21],[]),([303,62,118],[0,17],[280,281]),([303,62,1381],[10],[]),([303,62,1662],[27],[281]),([303,70,74],[10],[]),([303,70,94],[10,24,21],[]),([303,70,862],[7],[]),([303,70,1381],[10],[]),([303,78,64],[24,8,17],[282]),([303,78,68],[14,3,27,6,24,8,10,17],[283,284]),([303,78,86],[10,24,21],[]),([303,78,350],[20,17],[283]),([303,78,1381],[10],[282,284]),([303,86,74],[10,3],[]),([303,86,94],[10],[]),([303,86,126],[10,24,21],[]),([303,94,86],[10],[]),([303,94,118],[10,24,21],[]),([303,118,74],[10],[]),([303,118,92],[24,27,7,23],[285]),([303,118,110],[10,24,21],[]),([303,118,878],[],[285]),([303,126,102],[10,24,21],[]),([303,365,118],[6],[]),([303,383,140],[6],[286]),([303,606,48],[6,3,24,9,7,21],[287]),([303,1119,48],[20],[]),([303,1119,52],[10],[]),([303,1119,56],[10,24,21,17],[288]),([303,1119,60],[10,24,21,17],[289,290,291]),([303,1119,132],[10],[]),([303,1381,62],[6],[]),([303,1381,126],[10],[]),([303,1407,48],[],[]),([303,1407,52],[10],[]),([303,1662,54],[6],[]),([311,58,1381],[6],[]),([311,62,86],[0,24,21],[]),([311,62,1381],[6],[]),([311,78,1381],[6],[]),([311,94,66],[6,14],[]),([311,124,1381],[6,24,9,18],[]),([311,1381,44],[6,24,9,17],[]),([319,50,70],[10],[]),([319,50,621],[6],[]),([319,50,1381],[14],[]),([319,54,76],[10,0,24,14,5,17],[125,128,292,293])]
set_option maxRecDepth 100000 in
theorem v118_7_13 : ∀ e ∈ k118_7_13, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_13 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_14 : List Entry := [([319,54,78],[0,10],[126]),([319,54,88],[14,5,24,20,21],[]),([319,54,92],[24,0,17],[294,129,295]),([319,54,94],[0,24,21],[296]),([319,54,108],[16,20,17,5],[]),([319,54,124],[14,5,24,18],[297,298]),([319,54,621],[14,6,21,17],[299,130,292,295,297,203]),([319,54,1381],[20,14,17],[300,296,197,293,298,127,204]),([319,62,38],[0,1],[]),([319,62,70],[0],[]),([319,62,86],[0,24,21],[]),([319,62,621],[6],[]),([319,62,1381],[14],[]),([319,70,74],[10,5],[]),([319,70,94],[10,24,21],[]),([319,70,862],[17],[]),([319,70,1381],[10],[]),([319,86,74],[14],[301,302]),([319,86,86],[10,14,24,21],[]),([319,86,94],[10],[]),([319,86,302],[6,21],[303]),([319,86,862],[10],[]),([319,94,38],[6,24,21],[]),([319,94,86],[10],[]),([319,94,116],[24,18,20,21],[]),([319,351,68],[6],[303]),([319,590,48],[6,5,24,17],[304]),([319,590,86],[],[]),([319,590,1381],[10],[304]),([319,606,48],[6,5,24,9,17],[]),([319,606,86],[],[]),([319,1119,48],[8],[]),([319,1119,52],[10],[]),([319,1119,64],[14,8],[305,306]),([319,1119,68],[14],[]),([319,1381,62],[6],[]),([327,58,72],[6,10,24,20,21],[]),([327,58,76],[6,24,20,21],[]),([327,58,94],[6],[]),([327,58,118],[6,17],[307,308,309]),([327,58,126],[6],[]),([327,62,86],[0],[]),([327,62,118],[0,17,21],[310]),([327,94,66],[6],[]),([327,94,70],[6,14,24,21,17],[236,311,312,209]),([327,94,78],[6],[]),([327,126,66],[6,24,21],[]),([327,126,70],[6,24,21,23],[]),([335,50,70],[10],[]),([335,50,78],[10],[])]
set_option maxRecDepth 100000 in
theorem v118_7_14 : ∀ e ∈ k118_7_14, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_14 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_15 : List Entry := [([335,50,94],[14],[]),([335,50,118],[24,17],[313]),([335,50,126],[24],[]),([335,50,846],[10],[]),([335,51,300],[20,21],[314]),([335,54,78],[0],[]),([335,54,94],[0],[]),([335,54,126],[0,21],[]),([335,55,296],[20,21],[314]),([335,59,60],[6,21],[66]),([335,59,88],[10,24,21],[]),([335,59,92],[24,21],[]),([335,62,38],[0,24,21],[]),([335,62,70],[0],[]),([335,62,86],[0],[]),([335,62,112],[24,27,21],[]),([335,62,116],[24,21],[]),([335,62,118],[0,24,21],[]),([335,63,52],[0,6,21],[]),([335,63,128],[0,24,21],[]),([335,63,132],[0,24,21],[]),([335,70,74],[10,8],[]),([335,70,78],[10,24,21],[315,316]),([335,70,94],[10],[]),([335,70,126],[10],[]),([335,79,52],[6,21,8],[]),([335,86,29],[14],[317,303]),([335,86,70],[14],[318]),([335,86,74],[14],[]),([335,86,78],[14,24,21,17],[319]),([335,86,86],[10],[]),([335,86,94],[10],[]),([335,95,52],[6,21],[317]),([335,95,132],[14,24,21],[]),([335,118,74],[24,21],[]),([335,118,78],[24,23,21],[]),([335,118,94],[10,24,21],[]),([335,126,66],[24],[]),([335,126,70],[24],[]),([335,126,86],[10],[]),([335,127,68],[20,23,21],[]),([335,382,862],[8,21],[320]),([335,590,48],[6,10,8,24,9,21],[321]),([335,590,66],[8,21],[]),([335,1119,48],[10,8],[]),([335,1119,52],[14,24,21],[]),([335,1119,572],[10,17],[]),([335,1151,48],[8,23],[]),([335,1151,52],[10,24,21],[]),([349,847,82],[10],[])]
set_option maxRecDepth 100000 in
theorem v118_7_15 : ∀ e ∈ k118_7_15, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_15 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_16 : List Entry := [([349,847,86],[10,14,16,21,17,8],[322,323,324,205]),([359,58,110],[6,27,24,21],[]),([359,62,102],[0,24,21],[]),([359,110,78],[6,27,23,24,21],[]),([367,50,70],[10,27,24,26],[]),([367,50,78],[10],[]),([367,50,110],[24,27,21],[]),([367,54,78],[0],[]),([367,54,110],[0,24,21],[]),([367,70,74],[10,8],[]),([367,70,78],[10],[]),([367,70,110],[10,24,21],[]),([367,102,70],[24,27,23,21],[]),([367,102,86],[10,24,21],[]),([367,124,96],[6,20,27,10,14,17,18],[131,146,286,180,194]),([367,1135,48],[8,24,21],[320]),([575,50,1381],[10],[]),([575,54,76],[8,0,10,3,24,14,5,17],[325,178,249,326]),([575,54,78],[0,10,24,8,3],[327,322]),([575,54,88],[20,21],[]),([575,54,92],[24,17],[328,323]),([575,54,94],[0,24,21],[329]),([575,54,108],[16,21,17],[]),([575,54,124],[14,5,24,18,10,3],[250,324,330]),([575,54,1381],[20,14,10,17],[331,329,326,330,179,206]),([575,62,86],[0,24,21],[]),([575,62,1381],[10],[]),([575,66,74],[6,10,5],[]),([575,66,94],[6,24,21],[]),([575,66,108],[6,20,17],[]),([575,66,1381],[20,10],[332,304]),([575,70,862],[17],[262]),([575,70,1381],[10,14],[263]),([575,74,94],[6,24,21],[]),([575,74,108],[6,20,17],[]),([575,74,124],[24,18,6],[333]),([575,74,1381],[20,17],[334,333]),([575,86,74],[10,14],[]),([575,86,94],[10,24,21],[]),([575,94,116],[24,18,20,8],[]),([575,606,86],[10],[]),([575,1381,110],[10],[]),([591,50,118],[10,3,17],[335]),([591,54,78],[0,10,21],[242]),([591,54,94],[0],[]),([591,54,126],[0,21],[]),([591,62,86],[0],[]),([591,62,112],[24,27,20,8],[]),([591,62,116],[24,21],[]),([591,62,118],[0,24,21],[])]
set_option maxRecDepth 100000 in
theorem v118_7_16 : ∀ e ∈ k118_7_16, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_16 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_17 : List Entry := [([591,66,72],[6,3,10,8,24,9,21],[287,305]),([591,66,74],[6,10,3,8],[]),([591,66,88],[6,14,24,9,17],[]),([591,66,92],[6,24,9,21],[]),([591,66,94],[6],[]),([591,66,120],[24,27,6,9],[]),([591,66,124],[24,21,6,10,8],[306]),([591,66,126],[6,24,21],[]),([591,70,118],[10,24,21],[]),([591,74,94],[6],[]),([591,74,126],[6,24,21],[]),([591,86,74],[10],[]),([591,86,94],[10],[]),([591,118,74],[10,24,21],[]),([591,118,94],[10,24,21],[]),([623,54,78],[0,10,24,26],[]),([623,54,110],[0,24,21],[]),([623,66,74],[6,10],[]),([623,66,110],[6,24,21,23],[]),([847,50,66],[14,5,24,21],[]),([847,54,74],[0,24,21],[]),([847,54,78],[0,21],[244]),([847,54,94],[0],[]),([847,62,66],[0,24,21],[]),([847,62,70],[0,24,21],[]),([847,62,86],[0],[]),([847,62,116],[24,18,20,21],[]),([847,66,74],[6,5],[]),([847,66,94],[6],[]),([847,70,74],[14,24,21],[]),([847,70,94],[10,24,21],[]),([847,74,94],[6],[]),([847,74,124],[24,18,6,9],[]),([847,86,74],[10],[]),([847,86,82],[10,20,21],[]),([847,86,90],[10,24,21,17],[336]),([847,86,94],[10,21],[]),([1109,62,59],[24,9],[337,338,339]),([1109,62,63],[24,9],[340,341,342]),([1109,62,79],[10,12],[]),([1109,62,95],[14,15,17],[343]),([1135,50,74],[24,20,27,17,21],[344]),([1135,50,78],[24],[]),([1135,50,94],[10],[]),([1135,54,74],[0,24,21],[]),([1135,54,78],[0],[]),([1135,54,94],[0],[]),([1135,66,74],[6],[]),([1135,66,78],[6],[]),([1135,66,94],[6],[])]
set_option maxRecDepth 100000 in
theorem v118_7_17 : ∀ e ∈ k118_7_17, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_17 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def k118_7_18 : List Entry := [([1135,70,74],[24,21],[]),([1135,70,78],[24,20,27,26],[]),([1135,70,94],[10,24,21],[]),([1135,86,74],[10],[]),([1135,86,78],[10,26,24],[]),([1135,86,90],[10,17,24,21],[345]),([1135,86,94],[10],[])]
set_option maxRecDepth 100000 in
theorem v118_7_18 : ∀ e ∈ k118_7_18, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := level_sound hR118 7 k118_7_18 (D118_6.map (wsOf c118.2)) (map_dead w118_6) (by decide +kernel)
def D118_7 : List Entry := k118_7_0 ++ (k118_7_1 ++ (k118_7_2 ++ (k118_7_3 ++ (k118_7_4 ++ (k118_7_5 ++ (k118_7_6 ++ (k118_7_7 ++ (k118_7_8 ++ (k118_7_9 ++ (k118_7_10 ++ (k118_7_11 ++ (k118_7_12 ++ (k118_7_13 ++ (k118_7_14 ++ (k118_7_15 ++ (k118_7_16 ++ (k118_7_17 ++ (k118_7_18))))))))))))))))))
theorem w118_7 : ∀ e ∈ D118_7, ¬ Live516.live basicOps goal 7 (wsOf c118.2 e).toFinset := (app_dead v118_7_0 (app_dead v118_7_1 (app_dead v118_7_2 (app_dead v118_7_3 (app_dead v118_7_4 (app_dead v118_7_5 (app_dead v118_7_6 (app_dead v118_7_7 (app_dead v118_7_8 (app_dead v118_7_9 (app_dead v118_7_10 (app_dead v118_7_11 (app_dead v118_7_12 (app_dead v118_7_13 (app_dead v118_7_14 (app_dead v118_7_15 (app_dead v118_7_16 (app_dead v118_7_17 v118_7_18))))))))))))))))))
def k118_8_0 : List Entry := [([19,26],[6,0,10,3,1,14,5,20,24,27,8],[0,1,2,3,4,5,6,7,8]),([19,62],[6,10,3,14,7,24],[9,10]),([19,78],[6,14,5,10,8,20,24,27,17],[11,12]),([19,94],[6,20,10,8,14,21,27],[2,13,14,15,16,17]),([19,108],[24,21,6,10,8,14,0,27,26],[18,19]),([19,126],[6,27,26,10,8,14,17,20,24],[20,21]),([19,300],[0,6,10,14,3,5,24,27,20],[22,23,24,25]),([19,327],[0,6,5,14,4,24],[19]),([19,343],[0,6,20,21],[2,26,6,17]),([19,375],[0,6,26,27,17,24],[27,28,29]),([19,574],[6,3,7,24],[30,31]),([19,590],[6,4,8,14,5,17,24],[32]),([19,1119],[6,5,24,21,17],[33,34]),([19,1381],[6,24,20,10,14,27,26,0],[35,36,7,9,12,23,30,32]),([19,1407],[6,26,24,21,27],[37,24]),([19,1662],[6,24,21,27,14,10,17,0],[38,29,8,10,25,31]),([23,54],[0,10,3,8,14,20,24,27],[1,39,40,41,42,43]),([23,55],[10,1,7,2,3],[]),([23,56],[6,0,10,1,14,20,24,27,17],[44,45,46,47,48,49,50,51,52,53,54]),([23,57],[0,10,1,14,20,24,27],[1,55,56,57,58,59,60,61,62]),([23,60],[1,14,20,24,27,17],[63,64,65,66,67,68,69,70,71,72,73,74,75,76]),([23,61],[24,10,6,1,14,20,27],[77,78,79,80,81,82,83,84]),([23,62],[10,3,24,14,20,27,8],[85,86,87,88,89]),([23,63],[10,24,6,0,3,8],[]),([23,70],[0,14,5,4,10,20,24,27,17],[90,91,92,93,94,95]),([23,71],[14,4,5],[96,97,98,55,77]),([23,78],[14,5,10,20,24,27,17],[99,100,101,102]),([23,79],[14,0,5,1],[]),([23,86],[0,24,20,10,14,21,27],[103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118]),([23,87],[24,20,21],[119,120,121,122,103,56,78,123]),([23,94],[24,20,6,0,10,14,21,27],[103,124,125,126,127,128,129,130,131]),([23,95],[24,20,6,21,1],[103,132,133]),([23,118],[0,24,26,10,17,20],[134,135,136,137,138,139,140,141,142]),([23,119],[24,27,17,26],[143,144,145,146,147,57,79,148]),([23,126],[24,26,27,10,14,17,20],[149,150,151,152]),([23,127],[24,27,26,1],[153]),([23,296],[0,10,3,14,5,20,24,27],[22,154,155,156,58,80,123,133,148,153,157,158,159]),([23,310],[10,0,6,2,8,24],[160,161,162,163,164,165]),([23,311],[10,6,2,0,3],[]),([23,318],[0,10,7,1,8,5,24],[166,167,168,169]),([23,327],[0,14,6,4,5],[44,66]),([23,342],[24,0,6,20,21],[170,171,172,173,174,132,175,176,177,59,81,141,151,178,179,180,181]),([23,343],[24,20,6,21,0],[182,120,130,45,67]),([23,350],[0,20,6,1,3,5,21],[183,184,142,152]),([23,375],[0,27,6,17,26],[185,144,186,187,46,68]),([23,566],[6,10,2,1,3,24],[188,167,178,189,190]),([23,574],[10,6,0,3,24],[191,192,162,179,193,194]),([23,575],[6,10,0,7,24,3,8],[195]),([23,582],[6,14,4,1,17,8,5,24],[196,180,197]),([23,590],[14,6,0,5,17,24],[198,199,60,82,163,181,200])]
set_option maxRecDepth 100000 in
theorem v118_8_0 : ∀ e ∈ k118_8_0, ¬ Live516.live basicOps goal 8 (wsOf c118.2 e).toFinset := level_sound hR118 8 k118_8_0 (D118_7.map (wsOf c118.2)) (map_dead w118_7) (by decide +kernel)
def k118_8_1 : List Entry := [([23,591],[6,14,0,24,5],[96,201,202,47,69]),([23,607],[6,20,0,21],[119,203,131,175,48,70]),([23,621],[6,24,0,21,10,8,1,14,27,26],[204,195,202,49,71,94,101]),([23,639],[6,27,0,24,26],[143,205,206,50,72]),([23,847],[10,3,8,14,5],[207,208]),([23,863],[10,3,8,24,21],[209,210,118,176]),([23,895],[10,3,27,26],[211,212]),([23,1119],[14,5,24,21,17],[213,214,215,177,51,73]),([23,1381],[24,20,6,0,10,14,27,26],[216,217,42,52,61,74,83,88,95,102,157,164,168,189,193,197,200]),([23,1407],[24,26,21],[218,219,53,75,158]),([23,1662],[24,21,27,14,6,0,10,17],[220,187,43,54,62,76,84,89,159,165,169,190,194]),([27,60],[0,6,14,2,3,5,24,27,20],[155,221,222,223]),([27,62],[0,6,14,2,3,24],[156,224,225]),([27,72],[0,6,10,14,3,24,27,17],[226]),([27,76],[0,6,10,3,4,5,24,27,20],[227,228,229]),([27,78],[0,6,10,14,3,4,5,24,17],[230]),([27,88],[0,6,10,3,14,5,24,20,21],[]),([27,92],[0,6,10,3,14,5,24,27],[231,232,233,234]),([27,94],[0,6,10,3,14,5,24,21,27],[235,236,237,238]),([27,108],[0,6,10,24,3,14,5,20,21],[239]),([27,120],[0,6,10,27,14,3,5,24],[240]),([27,124],[0,6,10,3,14,5,20,26,24],[241,242,243]),([27,126],[0,6,10,27,3,14,5,20,26,24],[244,245,246]),([27,1381],[0,24,20,6,14,27,26],[247,248,237,221,224,226,227,230,240,243,157]),([27,1407],[0,26,24,21,27],[249,238,222,228,158]),([27,1662],[0,24,21,6,27,14,17],[250,246,223,225,229,234,159]),([31,54],[0,6,3,10,14,2,24,8],[251,252]),([31,70],[0,6,5,14,10,3,4,24,17],[253,254]),([31,86],[0,6,20,10,3,14,5,21,27],[2,255,256,257]),([31,118],[0,6,26,27,10,3,17,20,24],[258,259,260,261]),([31,310],[0,2,6,3,8,24],[262,263]),([31,342],[0,6,3,24,21,5],[264,265,6,261]),([31,607],[0,20,21,6],[2,266,257,265]),([31,621],[0,24,21,6,10,8,14,27,26],[267,253]),([31,639],[0,27,26,24,6],[268,269]),([31,1381],[0,24,9,20,10,14,27,26],[270,271,7,251,254,23,262]),([31,1407],[0,26,24,21],[272,24]),([31,1662],[0,24,21,27,14,10,17,6],[273,260,8,252,25,263]),([39,50],[6,10,3,14,20,24,27],[274,275,276,277,278,279]),([39,58],[6,10,0,14,20,24,27,2,8],[280,281,282,283,284,285,286,287,288,289,290,160,291,292,293,294,295]),([39,62],[10,2,3,14,8,20,24],[296,297,298,299]),([39,70],[0,10,2,3,8,20,24,27,17],[300,301]),([39,78],[10,2,14,8,20,24,27,17,5],[302,303,304,305]),([39,86],[0,10,2,3,8,14,24,21,27],[306,307,308,309]),([39,94],[10,2,3,8,14,24,21,27],[310,311,312,161,313,314]),([39,118],[0,10,2,3,8,17,20,24,26],[315,316]),([39,126],[10,2,27,8,14,17,20,24,26],[317,318]),([39,327],[0,10,14,3,2],[]),([39,343],[0,10,3,24,21,2],[]),([39,375],[0,10,27,3,17,2],[319,320])]
set_option maxRecDepth 100000 in
theorem v118_8_1 : ∀ e ∈ k118_8_1, ¬ Live516.live basicOps goal 8 (wsOf c118.2 e).toFinset := level_sound hR118 8 k118_8_1 (D118_7.map (wsOf c118.2)) (map_dead w118_7) (by decide +kernel)
def k118_8_2 : List Entry := [([39,574],[10,6,3,8,24],[280,321,322,291,162,313,323,324]),([39,590],[10,14,0,3,8,5,17,24],[325,314,326]),([39,847],[10,8,5],[327,163]),([39,863],[10,8,24,21],[328,329]),([39,877],[10,24,8,21,14,27,26],[330,292,296,304]),([39,895],[10,8,26,24],[331,332,293,297]),([39,1119],[10,5,24,21,17],[333,334,335]),([39,1381],[10,24,20,0,14,27,26],[336,337,278,42,294,298,301,305,164,262,323,326]),([39,1407],[10,26,24,21],[338,339]),([39,1662],[10,24,21,27,14,0,17],[340,320,279,43,295,299,165,263,324]),([47,50],[0,6,10,14,5,20,24,27],[341,342,343,344,345]),([47,54],[0,10,1,14,5,20,8,24,27],[1,346,347,348,349,350]),([47,70],[0,10,5,4,24,17],[351,352,353,354]),([47,86],[0,10,8,14,5,24,21,27],[346,355,356,357,358,166]),([47,118],[0,10,8,26,17,20,24],[359,360,361,362,363]),([47,570],[0,6,24],[1,364,365,348,167,351,366,367]),([47,606],[0,10,20,3,8,21],[368,352,363]),([47,863],[0,10,8,24,21],[369,346,358]),([47,877],[0,24,21,6,8,14,27,26,10],[370,353]),([47,895],[0,26,10,8,24,27],[371,372]),([47,1381],[0,24,20,10,14,27,26],[373,374,344,349,354,168,366]),([47,1407],[0,26,24,21,10],[375]),([47,1662],[0,24,21,27,14,10,17],[376,362,345,350,169,367]),([55,50],[6,14,5,10,20,24,17],[377,378,379,380,381]),([55,58],[6,14,0,20,24,27,17,4],[382,383,384,385,386,387]),([55,62],[14,4,5,10,20,24,27,17],[388,389,390,391,392]),([55,78],[10,3,20,24,27,17],[393,394,395,396,397,398]),([55,86],[0,14,4,5,10,24,21,17],[399,400,401,402]),([55,94],[14,4,5,10,24,21,27,17],[403,404,405,406,407]),([55,343],[0,14,5,24,21,4],[]),([55,574],[14,6,5,24,17],[382,408,409,386,410,396,406,411]),([55,590],[10,14,0,3,5,27,17,24],[412,413,391,407,414,415]),([55,839],[10,6,14,24,3],[416,417,418,419]),([55,847],[10,3],[420,421]),([55,855],[14,6,24,21],[422,423,424]),([55,863],[14,24,21],[425,426,114,427]),([55,877],[14,24,21,17,6,0,10],[94,390,410,428,397,414]),([55,1119],[10,3,24,21],[429,430]),([55,1381],[14,24,20,17,0,10],[431,381,95,387,392,301,398,411,415]),([63,50],[0,6,14,10,3,20,24,27,17],[432,433,434]),([63,54],[0,14,10,3,1,20,24,27,17],[435,436,437,438,439,440,441]),([63,70],[0,10,14,3,2,27,24,17],[442,443,444]),([63,86],[0,14,10,3,24,21,27,17],[445,437,446,447,448]),([63,606],[0,14,20,5,17,21],[449,440,442]),([63,855],[0,6,24,21,14],[450]),([63,863],[0,24,21,14],[451,437,448]),([63,877],[0,24,21,17,6,10],[439,443]),([63,1381],[0,24,20,17,10],[452,434,441,444]),([71,50],[6,24,20,10,14,21,27],[453,454,455,456]),([71,51],[6,24,21],[2,457,17,458])]
set_option maxRecDepth 100000 in
theorem v118_8_2 : ∀ e ∈ k118_8_2, ¬ Live516.live basicOps goal 8 (wsOf c118.2 e).toFinset := level_sound hR118 8 k118_8_2 (D118_7.map (wsOf c118.2)) (map_dead w118_7) (by decide +kernel)
def k118_8_3 : List Entry := [([71,55],[24,6,21],[459,130,460,461,462,106]),([71,58],[6,24,20,0,14,21,27,10],[463,464,465,466,467,468,469,470,471,170,182,472]),([71,59],[0,6,24,20,21],[107,473,474,475,476,477,478,479,462,171,480]),([71,62],[24,20,0,10,14,21,27],[106,2,481,482,483,484,485,486,26,120,487]),([71,63],[24,6,20,0,21],[458,106,172,488]),([71,71],[10,2,24,21,3],[489,490,491]),([71,78],[10,3,14,24,27,20,21],[492,493,494,495,174,496]),([71,79],[10,0,3,24,21],[]),([71,87],[14,4,24,21,17,5],[497,498]),([71,94],[14,5,10,24,27,17,20,21],[499,500,501]),([71,95],[14,0,5,24,21],[]),([71,118],[0,24,26,22,20,10,17,21],[502,503,504,505]),([71,119],[24,27,22,17,21,26],[506,507]),([71,126],[24,26,27,10,14,17,21],[508,509,510]),([71,127],[24,27,20,21,26],[]),([71,374],[24,0,20,27,26,21,17],[511,512,513]),([71,375],[24,27,20,17,0,26,21],[506,514]),([71,382],[0,27,22,24,5,21,3],[515,516]),([71,574],[24,20,6,0,21],[463,517,474,518,519,520,521,522,523,524,472,480,488,175,265,525,526,527,496,512,516]),([71,590],[10,3,20,21],[528,529,530,118,487,176,513]),([71,606],[14,5,20,21,17],[531,532,533,177]),([71,839],[10,6,20,21,3],[534,535,536,473,537,178]),([71,847],[10,3,24,21],[538,539,179]),([71,855],[14,6,20,21,17],[540,541,542,543,544,545,180]),([71,863],[14,5,24,21],[546,547,181]),([71,887],[24,6,20,17,21],[548,549,550,551,552,553,525]),([71,895],[24,23,27,21],[554,555,526]),([71,1119],[10,3,14,5,24,21],[556,557,558,559]),([71,1151],[10,3,23,24,21],[560,561]),([79,50],[0,6,20,10,3,14,5,21,27],[562]),([79,54],[0,20,10,3,14,5,21,27],[563,564]),([79,70],[0,10,3,2,24,20,21],[184]),([79,86],[0,14,5,4,17,24,20,21],[]),([79,112],[0,27,20,10,3,14,5,21],[]),([79,116],[0,20,23,10,3,14,5,21],[565,566]),([79,118],[0,27,20,23,10,3,14,5,21],[567,568]),([79,374],[0,22,23,24,27,17,21],[569]),([79,887],[0,6,17,24,21,23],[570,571,572]),([79,895],[0,23,27,24,21],[573]),([103,58],[6,24,27,0,26,14,17,20],[574,575,185]),([103,62],[24,18,27,0,10,17,20,26],[576,577,578,579,27,144,511,569]),([103,78],[10,3,14,17,20,24,26],[580,581,582]),([103,92],[27,0,18,5,10,20,24,26],[28,186,319,514,583,584,585,586,587]),([103,110],[24,18,27,0,20,23,10,17,21],[588,579,589,506]),([103,636],[24,0,18,20,27,17,21,10],[590,29,187,320,591,592]),([103,839],[10,6,26,27,24,3,17],[593,583,591]),([103,847],[10,26,3,17],[594,595,596,584,592]),([103,871],[24,6,23,27,21,17],[597,585]),([103,879],[24,23,27,21,17],[598,579,512,586]),([103,1135],[10,23,3,27,24,21,17],[599,513,587])]
set_option maxRecDepth 100000 in
theorem v118_8_3 : ∀ e ∈ k118_8_3, ¬ Live516.live basicOps goal 8 (wsOf c118.2 e).toFinset := level_sound hR118 8 k118_8_3 (D118_7.map (wsOf c118.2)) (map_dead w118_7) (by decide +kernel)
def k118_8_4 : List Entry := [([111,50],[0,6,27,10,3,14,5,20,24,26],[600]),([111,54],[0,27,10,3,14,5,20,24,26],[601,602,515]),([111,70],[0,10,27,3,2,24,26],[]),([111,102],[0,27,23,10,3,14,5,24,21],[603,601,604]),([111,871],[0,6,24,21,27],[605]),([111,879],[0,24,21,27],[606,601,604,516]),([295,58],[6,10,1,14,3,20,24,27],[1,416,534,607,364,536,608,609]),([295,62],[6,0,10,14,20,24,27],[610,611,612,473,613,614]),([295,78],[6,10,3,20,24,27,17],[615,416,616,617,418,618,188,619]),([295,94],[6,10,3,14,24,21,27],[620,534,621,617,622,623,537,365,624]),([295,108],[6,10,21,14,3,27,26],[625,419]),([295,126],[6,10,3,26,14,17,20,24],[626,627,628]),([295,590],[6,10,14,3,27,17,24],[629,630,624,631]),([295,1119],[6,24,21,17,10],[632,617,633,618,630]),([295,1381],[6,24,20,10,14,27,23],[634,635,608,613,619,189,366,631]),([295,1407],[6,26,24,21,27,10],[636]),([295,1662],[6,24,21,27,14,10,17],[637,591,609,614,190,367]),([303,50],[10,3,14,7,24],[595,638,639]),([303,54],[0,10,6,14,20,24,27,7,3],[280,640,641,642,643,644,645,646,647,648,649,191,321,596,650,651]),([303,62],[10,0,8,14,20,24,27],[652,653,654,655,656]),([303,70],[6,10,3,7,20,24,27,17],[657,658,192,322,659,660]),([303,78],[10,3,14,8,20,24,27,17],[661,662,663,664,665]),([303,86],[6,10,3,7,14,24,21,27],[666,667,668]),([303,94],[10,3,7,8,14,24,21,27],[669,670]),([303,118],[6,10,3,7,17,20,24,23],[671,672,673,674]),([303,126],[10,3,27,8,14,17,20,24,23],[675]),([303,335],[6,10,14,8,7],[]),([303,351],[6,10,8,24,21,7],[]),([303,365],[6,24,10,8,20,21,7],[676,195]),([303,383],[6,10,27,8,24,7],[677]),([303,606],[10,20,6,3,8,21],[678,659,674]),([303,1119],[10,24,21,17],[679,680,681,682,683,664]),([303,1381],[10,24,9,20,14,27,23],[684,685,638,650,42,655,660,665,30,193,323]),([303,1407],[10,26,24,21],[686,687]),([303,1662],[10,24,21,27,14,6,17],[688,592,639,651,43,656,31,194,324]),([311,58],[6,14,10,8,20,5,24,27,17],[540,542,689]),([311,62],[6,0,14,10,8,20,24,27,17],[690,543,691]),([311,78],[6,10,14,7,8,24,17],[196,692]),([311,94],[6,14,5,10,8,24,21,27,17],[693,540,544]),([311,108],[6,14,21,17,10,8],[]),([311,124],[6,14,19,18,10,8,20,5,24],[545,694]),([311,1381],[6,24,20,17,10],[695,689,691,692,694,197]),([319,50],[14,5,10,20,24,27,17],[696,546,96,697,698]),([319,54],[0,14,6,20,24,17,10,5],[382,699,700,701,702,703,704,705,198,201,408,706,707]),([319,62],[14,0,10,20,24,27,17,5],[708,709,710,711,712]),([319,70],[6,10,5,14,8,20,24,27,17],[713,714,199,409,715,716]),([319,71],[10,6,5,14],[]),([319,86],[6,14,5,10,24,21,27,17],[546,717,718,719,720,721]),([319,87],[14,20,6,21,5],[]),([319,94],[14,5,20,10,21,17],[722,723,724])]
set_option maxRecDepth 100000 in
theorem v118_8_4 : ∀ e ∈ k118_8_4, ¬ Live516.live basicOps goal 8 (wsOf c118.2 e).toFinset := level_sound hR118 8 k118_8_4 (D118_7.map (wsOf c118.2)) (map_dead w118_7) (by decide +kernel)
def k118_8_5 : List Entry := [([319,351],[6,14,20,21],[725,720]),([319,365],[6,24,14,21,17,10,8],[202,697,706,94,711,410]),([319,590],[10,14,6,5,27,8,17,24],[726,727,721,728]),([319,606],[14,20,6,5,17,21],[729,730,715]),([319,1119],[10,8,24,21],[731,732,733,734]),([319,1381],[14,24,9,20,17,10],[735,698,707,95,712,716,665,32,200,411,728]),([327,58],[6,20,10,8,1,14,27,21],[736,737,422,738,739,740]),([327,62],[6,20,10,8,14,0,27,21],[741,742]),([327,78],[6,10,8,7,24,20,21],[]),([327,94],[6,14,20,10,8,27,17],[743,744,422,745,424]),([327,126],[6,27,20,23,10,8,14,17],[746,747]),([327,382],[6,22,24,21,27,23,17],[]),([335,50],[24,6,20,10,14,27,21],[104,2,748,749,425,750,751,752,119,266,753]),([335,51],[24,0,20,6,9,21],[104,754,518]),([335,54],[0,24,6,20,14,27,21],[463,755,756,757,203,519]),([335,55],[0,24,20,9,21],[105,517,758,520]),([335,59],[0,24,21],[759,131,760,761,104,758]),([335,62],[24,0,20,10,14,21,27],[762,763,764,765,766,767]),([335,63],[24,21,0],[2,768,257,769,770,754]),([335,70],[6,10,8,14,24,27,20,21],[771,772,773,774,521]),([335,71],[10,6,8,24,9,21],[]),([335,79],[10,7,24,21,8],[775]),([335,86],[6,14,20,10,27,17,21],[776,425,777,778,779,780,781,725,523]),([335,87],[14,24,9,20,21],[776]),([335,95],[14,24,21,17],[782,720,783,776]),([335,118],[6,24,23,27,10,14,17,21],[784,785,786]),([335,119],[24,27,20,9,23,21],[]),([335,126],[24,23,22,10,14,17,21],[787,788,789]),([335,127],[24,27,22,21,23],[790]),([335,374],[6,27,22,21,17,24,8],[525]),([335,382],[24,6,27,20,23,17,21],[526,791]),([335,383],[6,24,27,20,21,23],[790]),([335,590],[10,8,20,21],[792,793,753,118,791]),([335,1119],[10,8,14,24,21],[794,795,796]),([335,1151],[10,8,23,24,21],[797,798]),([349,102],[6,24,21,18,26,27,10,17],[204,267,676,330,370]),([349,847],[10,14,21,6,8,27,17],[799,800,414]),([359,58],[6,27,10,8,14,17,20,24,23],[548,801,550,571]),([359,62],[6,27,10,8,14,17,20,0,24,23],[802,551]),([359,78],[6,10,27,7,8,24,23],[]),([359,92],[6,14,27,18,19,10,8,20,24,23],[553,572]),([359,110],[6,27,23,10,8,14,17,24],[548,803,552]),([359,124],[6,24,27,21,10,8,14,17],[]),([367,50],[24,18,6,27,10,17,20,26],[804,805,554,806,143,268]),([367,54],[0,24,6,27,26,14,17,20],[807,808,205]),([367,70],[6,10,8,14,17,20,24,26],[809,810,811]),([367,102],[6,24,18,27,23,10,17,21],[554,812,813,790]),([367,124],[24,18,25,20,6,10,21,27],[814,206,269,677,332,372]),([367,1135],[10,23,8,24,21],[815,791]),([575,50],[10,3,8,11,5,24,17],[558,799,816])]
set_option maxRecDepth 100000 in
theorem v118_8_5 : ∀ e ∈ k118_8_5, ¬ Live516.live basicOps goal 8 (wsOf c118.2 e).toFinset := level_sound hR118 8 k118_8_5 (D118_7.map (wsOf c118.2)) (map_dead w118_7) (by decide +kernel)
def k118_8_6 : List Entry := [([575,54],[0,10,14,20,24,17,8,3,5],[817,818,819,820,821,822,823,325,412,559,800,824]),([575,62],[10,0,14,8,20,24,27,17,5],[825,826]),([575,66],[6,10,14,20,24,27,17],[827,828,829,726,830]),([575,70],[6,10,3,14,11,8,27,24,17],[629,413,831,832]),([575,74],[6,10,14,3,20,24,17],[833,834,835,836]),([575,86],[10,3,14,11,8,24,21,27,17],[837,838,727]),([575,94],[10,3,11,14,8,24,21,17],[839]),([575,350],[10,14,3,8,17,20],[]),([575,606],[10,14,5,17,20,21],[840,831,630]),([575,1381],[10,24,20,17],[841,816,824,301,826,830,832,836,665,326,631,415,728]),([591,50],[10,3,20,8,14,27,21],[209,429,842,368,793]),([591,54],[0,10,20,14,27,21],[843,844,845,528]),([591,62],[10,0,20,8,14,21,27],[846,847,848,849]),([591,66],[6,10,20,14,21,27,3,8],[850,851,852,853,854,855,856,857,678,792,733]),([591,70],[6,10,3,8,14,24,21,27],[209,732,858,734,529]),([591,74],[6,10,20,3,14,21,27],[859,860]),([591,86],[10,3,14,8,24,27,17,20,21],[429,861,732,862,530]),([591,87],[10,14,3,24,21],[]),([591,118],[10,3,27,23,8,14,17,24,21],[863,864]),([591,119],[10,27,3,24,21],[]),([591,126],[10,3,27,20,8,14,17,21],[]),([591,382],[10,27,3,20,8,17],[]),([623,50],[10,3,8,13,26,24],[]),([623,54],[0,10,27,14,17,20,24,26,3],[865,866]),([623,66],[6,10,27,14,17,20,24,26],[867,868]),([623,70],[6,10,3,13,8,26,24],[]),([623,102],[10,3,27,13,23,17,24,21],[]),([847,50],[14,5,20,10,27,17,21],[869,213,333,449]),([847,54],[0,14,20,10,27,17,21],[870,871,872,531]),([847,62],[14,0,20,10,21,17],[873,874,875,876]),([847,66],[6,14,20,5,10,21,27,17],[877,878,729]),([847,67],[6,14,5,24,21,17,15],[722]),([847,70],[6,14,5,10,24,21,27,17],[213,879,680,880,840,532]),([847,71],[14,6,5,24,15],[]),([847,74],[6,14,20,5,10,21,17],[881,882]),([847,86],[10,5,14,24,27,17,20,21],[333,883,884,680,885,886,730,533]),([847,87],[10,5,24,15,14],[]),([847,116],[14,27,15,19,20,5,10,21],[34,215,335,633,683]),([847,117],[14,27,5,24,15,21],[]),([1109,62],[24,20,9,10,14,23,27],[887,888,889,890,216,270,684,735,336,373,431,452,841]),([1109,110],[24,20,22,23,10,14,17],[36,217,248,271,337,374,635,685]),([1135,50],[24,18,27,0,22,10,17,26,21],[891,892,893]),([1135,54],[0,24,20,27,10,14,17,21],[894,895,896]),([1135,66],[6,24,20,27,10,14,17,21,26],[897,898,899]),([1135,70],[6,24,18,27,22,10,17,21],[900,901,902]),([1135,86],[10,18,27,22,17,24,26],[903,904,905,906]),([1390,54],[6,24,18,25,20,10,17,21],[220,273,688,590,340,376])]
set_option maxRecDepth 100000 in
theorem v118_8_6 : ∀ e ∈ k118_8_6, ¬ Live516.live basicOps goal 8 (wsOf c118.2 e).toFinset := level_sound hR118 8 k118_8_6 (D118_7.map (wsOf c118.2)) (map_dead w118_7) (by decide +kernel)
def D118_8 : List Entry := k118_8_0 ++ (k118_8_1 ++ (k118_8_2 ++ (k118_8_3 ++ (k118_8_4 ++ (k118_8_5 ++ (k118_8_6))))))
theorem w118_8 : ∀ e ∈ D118_8, ¬ Live516.live basicOps goal 8 (wsOf c118.2 e).toFinset := (app_dead v118_8_0 (app_dead v118_8_1 (app_dead v118_8_2 (app_dead v118_8_3 (app_dead v118_8_4 (app_dead v118_8_5 v118_8_6))))))
def k118_9_0 : List Entry := [([19],[6,24,10,14,20,27,0,8,17],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),([23],[24,6,0,10,14,20,27,17],[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60]),([27],[0,24,6,14,20,27,10,3,5],[61,62,63,64,65,66,67,68,69,70,71,72,36,73,74,75]),([31],[24,0,10,14,20,27,6,3,5],[0,76,77,78,79,6,80,81,82,83,84,85,86,87]),([39],[10,0,3,2,14,20,24,27,8,17],[88,16,89,90,91,92,93,94,95,96,37,38,80,97,98,99,100,101,102,103,104,105,106,107,108,109]),([47],[10,0,14,20,24,27,5,8],[110,111,112,113,114,39,115,116,117,118,119,120,121,122]),([55],[14,0,5,4,10,20,24,27,17],[123,24,124,125,91,126,127,128,7,40,97,129,130,131,132,133,134,135,136,137,138]),([63],[14,0,10,20,24,27,17,3],[139,140,141,142,143,144,145,146,147]),([71],[24,20,0,10,14,21,27,17],[148,149,28,150,151,152,153,154,93,155,156,157,127,158,159,160,161,162,163,164,8,41,42,81,98,129,165,166,167,168,169,170,171,172,173,174,175,176,177,178]),([79],[24,0,20,10,14,21,27,3,5],[179,180,181,182,183,184,185,43,186,187,188]),([103],[24,27,0,26,10,17,20],[189,190,191,192,193,9,44,99,165,166,186,194,195,196,197,198,199]),([111],[24,0,27,10,14,17,20,3,26],[200,201,202,203,167,204,205]),([295],[6,10,14,20,24,27,3,17],[206,207,208,209,210,211,45,115,212,132,171,195,213,214,215,216]),([303],[10,6,3,14,7,20,24,27,17],[217,218,16,219,220,221,222,223,224,225,10,46,47,226,227,228,229,100,230,133,172,196,231,232,233,234]),([311],[6,14,10,20,24,17,8,5],[235,236,237,238,239,240,48,173,241]),([319],[14,6,5,10,20,24,27,17],[242,243,24,244,245,246,221,247,248,249,11,49,50,226,250,251,130,252,253,102,174,254,255]),([327],[6,24,20,10,14,21,27,8,17],[256,257,258,259,260,261,134,144,197,204]),([335],[24,20,6,10,14,21,27,17],[262,263,264,265,28,266,267,268,269,270,223,271,272,273,249,274,275,276,277,278,51,82,227,250,279,280,281,168,282,103,117,135,145,198,205,283,284]),([349],[24,21,6,10,14,27,26],[285,52,83,228,251,104,118,136,146,286]),([359],[6,24,27,10,17,20,8,23],[287,288,289,290,291,292,279,175,187]),([367],[24,27,6,26,10,14,17,20],[293,294,295,296,297,53,84,229,261,280,281,105,119,176,188,298]),([575],[10,14,3,8,20,11,24,27,17],[299,300,91,301,302,303,304,221,305,306,101,212,307,131,252,308,54,177,283,286,309]),([591],[10,20,3,8,14,21,27,17],[310,311,93,312,313,314,315,223,316,317,306,318,319,320,116,230,307,321,169,282,55,137,199,254,298]),([623],[10,27,3,26,14,17,20,8,24],[322,323,324,325,326,321,56,178,284]),([847],[14,20,5,10,21,17],[327,328,127,329,330,331,332,333,334,249,335,336,306,337,338,143,253,308,170,12,57,106,213,231]),([1109],[24,20,10,14,27,23],[339,340,13,58,73,85,107,120,138,147,214,232,241,255,309]),([1135],[24,27,20,22,26,10,14,17,21],[341,342,343,344,345,14,59,74,86,108,121,215,233]),([1390],[24,21,27,14,10,17],[346,194,15,60,75,87,109,122,216,234])]
set_option maxRecDepth 100000 in
theorem v118_9_0 : ∀ e ∈ k118_9_0, ¬ Live516.live basicOps goal 9 (wsOf c118.2 e).toFinset := level_sound hR118 9 k118_9_0 (D118_8.map (wsOf c118.2)) (map_dead w118_8) (by decide +kernel)
def D118_9 : List Entry := k118_9_0
theorem w118_9 : ∀ e ∈ D118_9, ¬ Live516.live basicOps goal 9 (wsOf c118.2 e).toFinset := v118_9_0
def k118_10_0 : List Entry := [([],[10,14,20,24,27,17],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])]
set_option maxRecDepth 100000 in
theorem v118_10_0 : ∀ e ∈ k118_10_0, ¬ Live516.live basicOps goal 10 (wsOf c118.2 e).toFinset := level_sound hR118 10 k118_10_0 (D118_9.map (wsOf c118.2)) (map_dead w118_9) (by decide +kernel)
def D118_10 : List Entry := k118_10_0
theorem w118_10 : ∀ e ∈ D118_10, ¬ Live516.live basicOps goal 10 (wsOf c118.2 e).toFinset := v118_10_0
theorem g118 : GoodC c118 := claim_sound2 D118_10 c118 w118_10 (by decide +kernel)
def c119 : Claim := (7, available 0xdef780000001bdeddee0000000000000000000 77 inputs)
def r119 : List RE := [(0xc83580000001906c86a0000000000000000000,77,0),(0x5ad68000000139c99ac0000000000000000000,78,1)]
def d119 : List Entry := [([],[0,1],[])]
def e119 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g119 : GoodC c119 := claim_sound [c39,c108] (gcons g39 (gcons g108 gnil)) r119 d119 e119 c119 (by decide +kernel)
def c120 : Claim := (3, available 0x18c600000000000198c0000000000000000000 78 inputs)
def r120 : List RE := []
def d120 : List Entry := [([4099],[],[]),([],[],[])]
def e120 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g120 : GoodC c120 := claim_sound [] gnil r120 d120 e120 c120 (by decide +kernel)
def c121 : Claim := (4, available 0x9ce7000000000005dce0000000000000000000 77 inputs)
def r121 : List RE := [(0x18c600000000000198c0000000000000000000,78,0)]
def d121 : List Entry := [([4100],[0],[]),([],[],[])]
def e121 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g121 : GoodC c121 := claim_sound [c120] (gcons g120 gnil) r121 d121 e121 c121 (by decide +kernel)
def c122 : Claim := (4, available 0x16b5000000000000000bb000000001ba00 9 inputs)
def r122 : List RE := []
def d122 : List Entry := [([],[],[])]
def e122 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g122 : GoodC c122 := claim_sound [] gnil r122 d122 e122 c122 (by decide +kernel)
def c123 : Claim := (3, available 0xb3000000003318000000000000000000000001b3 0 inputs)
def r123 : List RE := []
def d123 : List Entry := [([4099],[],[]),([],[],[])]
def e123 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g123 : GoodC c123 := claim_sound [] gnil r123 d123 e123 c123 (by decide +kernel)
def c124 : Claim := (4, available 0xb700000631333800000000000000000000019bb7 0 inputs)
def r124 : List RE := [(0xb3000000003318000000000000000000000001b3,0,0)]
def d124 : List Entry := [([4100],[0],[]),([],[],[])]
def e124 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g124 : GoodC c124 := claim_sound [c123] (gcons g123 gnil) r124 d124 e124 c124 (by decide +kernel)
def c125 : Claim := (4, available 0x39ce400000000003b9d0000000000000000000 76 inputs)
def r125 : List RE := [(0x18c600000000000198c0000000000000000000,78,0)]
def d125 : List Entry := [([4100],[0],[]),([],[],[])]
def e125 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g125 : GoodC c125 := claim_sound [c120] (gcons g120 gnil) r125 d125 e125 c125 (by decide +kernel)
def c126 : Claim := (4, available 0x3b9d0000000000000000000 76 inputs)
def r126 : List RE := [(0x198c0000000000000000000,78,0)]
def d126 : List Entry := [([],[0],[])]
def e126 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g126 : GoodC c126 := claim_sound [c96] (gcons g96 gnil) r126 d126 e126 c126 (by decide +kernel)
def c127 : Claim := (6, available 0xb70000000000000003b9d000000000000003dfb7 0 inputs)
def r127 : List RE := [(0x8600000000000000028190000000000000028686,1,0),(0x1500000000000000002950000000000000004e15,0,1),(0xb3000000000000000000000000000000000001b3,0,2),(0x3b9d0000000000000000000,76,3)]
def d127 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e127 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g127 : GoodC c127 := claim_sound [c47,c72,c89,c126] (gcons g47 (gcons g72 (gcons g89 (gcons g126 gnil)))) r127 d127 e127 c127 (by decide +kernel)
def c128 : Claim := (3, available 0x280c6209103000000000000000000000000000 108 inputs)
def r128 : List RE := []
def d128 : List Entry := [([],[],[])]
def e128 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g128 : GoodC c128 := claim_sound [] gnil r128 d128 e128 c128 (by decide +kernel)
def c129 : Claim := (3, available 0x14a4119012800000000000000000000000000 107 inputs)
def r129 : List RE := []
def d129 : List Entry := [([],[],[])]
def e129 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g129 : GoodC c129 := claim_sound [] gnil r129 d129 e129 c129 (by decide +kernel)
def c130 : Claim := (4, available 0x39ce4000000000000000000000000000000000 134 inputs)
def r130 : List RE := [(0x18c60000000000000000000000000000000000,137,0)]
def d130 : List Entry := [([],[0],[])]
def e130 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g130 : GoodC c130 := claim_sound [c106] (gcons g106 gnil) r130 d130 e130 c130 (by decide +kernel)
def c131 : Claim := (6, available 0x39ce6739333800000000000000000000000000 107 inputs)
def r131 : List RE := [(0x280c6209103000000000000000000000000000,108,0),(0x14a4119012800000000000000000000000000,107,1),(0x331800000000000000000000000000,107,2),(0x39ce4000000000000000000000000000000000,134,3)]
def d131 : List Entry := [([],[0,1,2,3],[0,1,2,3,4])]
def e131 : List (List Entry) := [[([23],[0,2],[0]),([31],[0,2,3],[]),([39],[1,2],[1]),([47],[1,2,3],[]),([303],[0],[])],[([23,56],[],[]),([39,56],[],[])]]
set_option maxRecDepth 100000 in
theorem g131 : GoodC c131 := claim_sound [c128,c129,c91,c130] (gcons g128 (gcons g129 (gcons g91 (gcons g130 gnil)))) r131 d131 e131 c131 (by decide +kernel)
def c132 : Claim := (7, available 0xf7000016b5bbbc00000000000bbb9e800001bbf7 0 inputs)
def r132 : List RE := [(0xf300000000bb9c0000000000000b8e80000001f3,0,0)]
def d132 : List Entry := [([],[0],[])]
def e132 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g132 : GoodC c132 := claim_sound [c93] (gcons g93 gnil) r132 d132 e132 c132 (by decide +kernel)
def c133 : Claim := (5, available 0xf7000000000000000000000003331c800001bbf7 0 inputs)
def r133 : List RE := [(0xf3000000000000000000000000030c80000001f3,0,0)]
def d133 : List Entry := [([],[0],[])]
def e133 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g133 : GoodC c133 := claim_sound [c90] (gcons g90 gnil) r133 d133 e133 c133 (by decide +kernel)
def c134 : Claim := (5, available 0x7fdf0000000000000000000 76 inputs)
def r134 : List RE := [(0x5dce0000000000000000000,77,0)]
def d134 : List Entry := [([],[0],[])]
def e134 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g134 : GoodC c134 := claim_sound [c97] (gcons g97 gnil) r134 d134 e134 c134 (by decide +kernel)
def c135 : Claim := (5, available 0xbdef4000000000000000000000000000000000 134 inputs)
def r135 : List RE := [(0x9ce70000000000000000000000000000000000,136,0)]
def d135 : List Entry := [([],[0],[])]
def e135 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g135 : GoodC c135 := claim_sound [c115] (gcons g115 gnil) r135 d135 e135 c135 (by decide +kernel)
def c136 : Claim := (8, available 0xf70000000000000007fdf00007775d800003fff7 0 inputs)
def r136 : List RE := [(0x6000000000000000077030000666018000037560,5,0),(0x86000000000000000685b0000555590000028686,1,1),(0x5500000000000000006d70000070558000006e55,0,2),(0xf30000000000000005dce00000074d80000001f3,0,3),(0xb70000000000000003b9d000000000000003dfb7,0,4),(0xf7000000000000000000000003331c800001bbf7,0,5),(0x7fdf0000000000000000000,76,6)]
def d136 : List Entry := [([],[2,3,4,5,6],[0,1,2,3])]
def e136 : List (List Entry) := [[([19],[1,2,3,4,5,6,0],[0,1]),([23],[2,1,0,3,4,5,6],[2,3,4]),([27],[0,2,1,3,4,5,6],[5,6,7,8,9,4]),([31],[2,0,3,4,5,6,1],[0,1])],[([19,26],[1,2],[0]),([19,300],[1,0],[1]),([23,60],[],[]),([23,61],[2],[2]),([23,296],[0,2],[1,3,4,2]),([27,60],[0,1],[4]),([27,76],[0],[]),([27,92],[1],[]),([27,104],[],[]),([27,108],[],[])],[([19,26,60],[],[]),([19,300,20],[2],[0]),([23,61,568],[],[1,2]),([23,296,30],[0,2],[1,2]),([23,296,44],[2],[1])],[([19,300,20,29],[],[]),([23,61,568,28],[],[]),([23,61,568,44],[],[])]]
set_option maxRecDepth 100000 in
theorem g136 : GoodC c136 := claim_sound [c22,c43,c74,c98,c127,c133,c134] (gcons g22 (gcons g43 (gcons g74 (gcons g98 (gcons g127 (gcons g133 (gcons g134 gnil))))))) r136 d136 e136 c136 (by decide +kernel)
def c137 : Claim := (10, available 0xf7bdef77bdbbbc0007fdf0000fffdf800003fff7 0 inputs)
def r137 : List RE := [(0x60b58175acaa0400077030000eee038000037560,5,0),(0xa001700c800400060030000ccc030000020400,10,1),(0x400501418c0804000060300000e0038000006440,6,2),(0xb0003400a00000070000000e0e000000030100,8,3),(0x6094810000aa040005502000000e038000000160,5,4),(0x35ac000000000000000ee0000000037400,10,5),(0x86a82d720d90b4000685b0000ddddb0000028686,1,6),(0x40029400d00a4000005300000d0d30000000604,2,7),(0x80a8003200900000068000000d0d000000028080,7,8),(0x86280c6209103000028190000000000000028686,1,9),(0x55056b419d09ac00006d700000f0d78000006e55,0,10),(0x5104630000098c00004c60000000c78000000051,0,11),(0x15014a4119012800002950000000000000004e15,0,12),(0x550000009509ac000000000000b0968000002a55,0,13),(0xf39ce70000bb9c0005dce000000fcf80000001f3,0,14),(0xb318c600003318000198c00000000000000001b3,0,15),(0xf300000000bb9c0000000000000b8e80000001f3,0,16),(0x9ce7000000000005dce0000000000000000000,77,17),(0xf30000000000000005dce00000074d80000001f3,0,18),(0x16b5000000000000000bb000000001ba00,9,19),(0xb700000631333800000000000000000000019bb7,0,20),(0x39ce400000000003b9d0000000000000000000,76,21),(0xb70000000000000003b9d000000000000003dfb7,0,22),(0x39ce6739333800000000000000000000000000,107,23),(0xf7000016b5bbbc00000000000bbb9e800001bbf7,0,24),(0xf7000000000000000000000003331c800001bbf7,0,25),(0x7fdf0000000000000000000,76,26),(0xbdef4000000000000000000000000000000000,134,27),(0xf70000000000000007fdf00007775d800003fff7,0,28)]
def R137 : List RR := r137.map (resolve [c23,c18,c58,c20,c12,c21,c45,c27,c41,c42,c75,c66,c76,c77,c94,c95,c93,c121,c98,c122,c124,c125,c127,c131,c132,c133,c134,c135,c136] c137.2)
theorem hR137 : ∀ y ∈ R137, RInv c137.2.toFinset y := res_inv [c23,c18,c58,c20,c12,c21,c45,c27,c41,c42,c75,c66,c76,c77,c94,c95,c93,c121,c98,c122,c124,c125,c127,c131,c132,c133,c134,c135,c136] (gcons g23 (gcons g18 (gcons g58 (gcons g20 (gcons g12 (gcons g21 (gcons g45 (gcons g27 (gcons g41 (gcons g42 (gcons g75 (gcons g66 (gcons g76 (gcons g77 (gcons g94 (gcons g95 (gcons g93 (gcons g121 (gcons g98 (gcons g122 (gcons g124 (gcons g125 (gcons g127 (gcons g131 (gcons g132 (gcons g133 (gcons g134 (gcons g135 (gcons g136 gnil))))))))))))))))))))))))))))) r137 c137.2
def k137_4_0 : List Entry := [([23,56,607,124,96,60],[],[]),([23,342,862,36,76,52],[],[]),([39,58,92,350,108,32],[],[]),([39,58,92,364,18,92],[],[])]
set_option maxRecDepth 100000 in
theorem v137_4_0 : ∀ e ∈ k137_4_0, ¬ Live516.live basicOps goal 4 (wsOf c137.2 e).toFinset := level_sound hR137 4 k137_4_0 [] nil_dead (by decide +kernel)
def D137_4 : List Entry := k137_4_0
theorem w137_4 : ∀ e ∈ D137_4, ¬ Live516.live basicOps goal 4 (wsOf c137.2 e).toFinset := v137_4_0
def k137_5_0 : List Entry := [([19,300,20,25,853],[],[]),([19,300,20,25,1117],[],[]),([19,300,20,29,853],[],[]),([19,300,20,29,1117],[],[]),([19,300,20,55,56],[],[]),([19,300,20,55,60],[],[]),([19,300,20,71,56],[],[]),([19,300,20,71,60],[],[]),([19,300,20,71,76],[],[]),([19,300,20,853,94],[],[]),([23,56,607,124,96],[],[0]),([23,57,358,840,28],[],[]),([23,57,358,840,60],[],[]),([23,57,568,28,853],[],[]),([23,57,568,28,1117],[],[]),([23,60,607,124,96],[],[]),([23,61,568,28,853],[],[]),([23,61,568,28,1117],[],[]),([23,61,568,44,853],[],[]),([23,61,568,44,1117],[],[]),([23,87,88,840,28],[],[]),([23,87,92,840,28],[],[]),([23,87,92,840,44],[],[]),([23,103,88,840,28],[],[]),([23,103,92,840,28],[],[]),([23,103,92,840,44],[],[]),([23,103,108,840,44],[],[]),([23,103,108,840,76],[],[]),([23,296,44,853,94],[],[]),([23,310,56,28,853],[],[]),([23,310,56,28,1117],[],[]),([23,342,862,36,76],[],[1]),([23,590,52,60,853],[],[]),([23,591,68,76,364],[1],[]),([23,591,68,92,364],[],[]),([27,92,95,636,32],[],[]),([39,50,110,124,96],[],[]),([39,58,92,350,108],[],[2]),([39,58,92,364,18],[],[3]),([39,58,92,364,86],[],[]),([39,58,366,124,96],[],[2]),([39,62,366,124,96],[],[]),([39,590,52,60,93],[2],[]),([39,590,52,60,853],[],[]),([47,50,110,124,96],[],[]),([87,636,847,84,56],[],[]),([87,636,847,84,92],[16],[]),([87,636,847,84,108],[],[])]
set_option maxRecDepth 100000 in
theorem v137_5_0 : ∀ e ∈ k137_5_0, ¬ Live516.live basicOps goal 5 (wsOf c137.2 e).toFinset := level_sound hR137 5 k137_5_0 (D137_4.map (wsOf c137.2)) (map_dead w137_4) (by decide +kernel)
def D137_5 : List Entry := k137_5_0
theorem w137_5 : ∀ e ∈ D137_5, ¬ Live516.live basicOps goal 5 (wsOf c137.2 e).toFinset := v137_5_0
def k137_6_0 : List Entry := [([19,26,56,1125],[],[]),([19,26,56,1389],[],[]),([19,26,60,1125],[],[]),([19,26,60,1389],[],[]),([19,26,86,72],[],[]),([19,26,86,76],[],[]),([19,26,102,72],[],[]),([19,26,102,76],[],[]),([19,26,102,92],[],[]),([19,94,94,100],[],[]),([19,110,124,96],[24,22,26],[]),([19,300,20,25],[0,10,1,28],[0,1]),([19,300,20,29],[0,10,28],[2,3]),([19,300,20,55],[0,28,23],[4,5]),([19,300,20,63],[0,28,23],[]),([19,300,20,71],[0,16],[6,7,8]),([19,300,20,79],[0,24],[]),([19,300,20,847],[0,28,23],[]),([19,300,20,853],[0,28,22],[9,0,2]),([19,300,20,1117],[0,28,22,14,24,23],[1,3]),([19,300,1125,110],[],[9]),([19,359,652,52],[16],[]),([23,56,327,76],[],[]),([23,56,343,92],[],[]),([23,56,343,636],[16],[]),([23,56,575,64],[],[]),([23,56,575,380],[1],[]),([23,56,607,124],[],[10]),([23,56,621,102],[],[]),([23,56,847,100],[],[]),([23,56,1125,78],[],[]),([23,56,1125,110],[],[]),([23,56,1389,70],[],[]),([23,57,326,44],[],[]),([23,57,342,44],[],[]),([23,57,358,44],[],[]),([23,57,358,92],[],[]),([23,57,358,840],[],[11,12]),([23,57,568,28],[0,1,28],[12,13,14]),([23,57,568,1125],[],[13,0]),([23,57,568,1389],[],[14,1]),([23,60,87,92],[],[]),([23,60,343,92],[],[]),([23,60,343,636],[16],[]),([23,60,607,124],[],[15]),([23,60,621,102],[],[]),([23,60,847,100],[],[]),([23,60,1125,78],[],[]),([23,60,1125,110],[],[]),([23,60,1389,70],[],[])]
set_option maxRecDepth 100000 in
theorem v137_6_0 : ∀ e ∈ k137_6_0, ¬ Live516.live basicOps goal 6 (wsOf c137.2 e).toFinset := level_sound hR137 6 k137_6_0 (D137_5.map (wsOf c137.2)) (map_dead w137_5) (by decide +kernel)
def k137_6_1 : List Entry := [([23,61,326,40],[],[]),([23,61,342,40],[],[]),([23,61,358,40],[],[]),([23,61,358,92],[],[]),([23,61,568,28],[0,1,28],[16,17]),([23,61,568,44],[10,0,28],[18,19]),([23,61,568,1125],[],[16,18]),([23,61,568,1389],[],[17,19]),([23,62,102,92],[],[]),([23,70,72,877],[],[]),([23,70,72,1125],[],[]),([23,70,76,877],[],[]),([23,70,76,1125],[],[]),([23,71,88,28],[],[]),([23,86,29,296],[],[]),([23,86,29,316],[],[]),([23,86,41,316],[],[]),([23,86,61,328],[],[]),([23,86,70,76],[],[]),([23,86,86,88],[],[]),([23,86,86,92],[],[]),([23,86,86,108],[],[]),([23,86,102,88],[],[]),([23,86,102,92],[],[]),([23,86,102,108],[],[]),([23,87,88,840],[],[20,4]),([23,87,92,840],[],[21,22]),([23,87,840,28],[0,22],[21]),([23,87,840,44],[0,28,23],[4,22]),([23,87,840,76],[0,28,23],[20,21]),([23,94,94,100],[],[]),([23,95,840,44],[0,28,23],[]),([23,95,840,76],[0,28,23],[]),([23,103,88,840],[],[23,6]),([23,103,92,840],[],[24,25]),([23,103,108,840],[],[26,27]),([23,103,840,28],[0,24],[24,11]),([23,103,840,44],[0,16],[6,25,26]),([23,103,840,76],[0,16],[23,24,12,27]),([23,111,840,44],[0],[]),([23,111,840,76],[1,0,24],[]),([23,296,30,1125],[0],[16,0,18]),([23,296,30,1389],[0],[17,1,19]),([23,296,44,847],[0,28,23],[]),([23,296,44,853],[0,28,22],[28,13,16]),([23,296,44,1117],[0,28,22,14,24,23],[14,17]),([23,296,46,1125],[0],[]),([23,296,46,1389],[0],[]),([23,296,1125,110],[],[9,28]),([23,310,56,28],[10,1,28],[29,30])]
set_option maxRecDepth 100000 in
theorem v137_6_1 : ∀ e ∈ k137_6_1, ¬ Live516.live basicOps goal 6 (wsOf c137.2 e).toFinset := level_sound hR137 6 k137_6_1 (D137_5.map (wsOf c137.2)) (map_dead w137_5) (by decide +kernel)
def k137_6_2 : List Entry := [([23,310,56,1125],[],[29]),([23,310,56,1389],[],[30]),([23,310,94,588],[],[]),([23,310,316,54],[],[]),([23,310,316,1125],[10],[29]),([23,310,316,1389],[10],[30]),([23,310,846,36],[5],[]),([23,318,312,1125],[],[]),([23,318,312,1389],[],[]),([23,342,56,46],[1],[]),([23,342,56,60],[1,28,22,23],[]),([23,342,56,62],[6],[]),([23,342,57,76],[6,28,23],[]),([23,342,57,92],[],[]),([23,342,70,60],[3],[]),([23,342,70,72],[3],[]),([23,342,334,52],[3],[]),([23,342,350,52],[5],[]),([23,342,846,36],[3],[]),([23,342,862,36],[5],[31]),([23,343,72,76],[1,6],[]),([23,343,72,92],[],[]),([23,574,52,1125],[],[29]),([23,574,52,1389],[],[30]),([23,590,52,46],[1],[]),([23,590,52,60],[1,14,5,28,16],[32]),([23,590,52,62],[0],[]),([23,590,52,1125],[],[32]),([23,591,68,76],[1,0,28],[33]),([23,591,68,92],[],[34]),([23,591,68,380],[1],[33,34]),([23,623,140,112],[6],[10,15]),([23,847,52,124],[],[]),([23,1119,48,88],[],[]),([23,1119,48,92],[],[]),([23,1391,48,88],[],[]),([23,1391,48,92],[],[]),([27,60,1125,110],[],[28]),([27,76,1125,110],[],[]),([27,92,95,116],[],[]),([27,92,95,636],[28],[35]),([27,92,101,110],[],[]),([27,92,1389,34],[28,23],[35]),([27,94,372,110],[],[]),([31,86,102,108],[],[]),([31,102,380,54],[16],[]),([31,623,140,112],[6,24,21],[]),([39,50,110,124],[],[36]),([39,50,124,102],[],[]),([39,50,1397,44],[],[])]
set_option maxRecDepth 100000 in
theorem v137_6_2 : ∀ e ∈ k137_6_2, ¬ Live516.live basicOps goal 6 (wsOf c137.2 e).toFinset := level_sound hR137 6 k137_6_2 (D137_5.map (wsOf c137.2)) (map_dead w137_5) (by decide +kernel)
def k137_6_3 : List Entry := [([39,50,1661,36],[],[]),([39,58,60,1125],[],[29]),([39,58,60,1389],[],[30]),([39,58,72,1125],[],[]),([39,58,76,350],[],[]),([39,58,76,1125],[],[]),([39,58,76,1389],[],[]),([39,58,92,101],[22],[]),([39,58,92,350],[],[37]),([39,58,92,364],[22,23,0,10,8],[38,39]),([39,58,92,1389],[23],[]),([39,58,94,372],[22],[]),([39,58,104,1381],[],[]),([39,58,108,109],[],[]),([39,58,108,1381],[],[]),([39,58,110,124],[],[]),([39,58,110,380],[],[]),([39,58,124,102],[],[]),([39,58,316,1125],[10],[]),([39,58,316,1389],[10],[]),([39,58,366,124],[],[40,37]),([39,58,380,102],[],[39]),([39,58,1397,44],[],[]),([39,58,1661,36],[],[]),([39,62,366,124],[],[41]),([39,62,380,102],[],[]),([39,574,52,1125],[10],[]),([39,574,52,1389],[10],[]),([39,590,52,60],[3,2,28,14,5,16],[42,43]),([39,590,52,1125],[],[43]),([39,879,140,112],[10],[40,41]),([47,50,110,124],[],[44]),([47,50,124,102],[],[]),([47,50,1397,44],[],[]),([47,50,1661,36],[],[]),([47,54,102,92],[],[]),([47,54,308,1125],[],[]),([47,54,308,1389],[],[]),([47,86,102,108],[],[]),([47,102,92,862],[],[]),([47,102,380,70],[16],[]),([47,570,56,1125],[],[]),([47,570,56,1389],[],[]),([47,570,1397,44],[],[]),([47,879,140,112],[24,21,10],[]),([55,50,108,1381],[],[]),([55,50,1397,44],[],[]),([55,58,60,1125],[],[]),([55,58,316,1125],[],[]),([55,58,1397,44],[],[])]
set_option maxRecDepth 100000 in
theorem v137_6_3 : ∀ e ∈ k137_6_3, ¬ Live516.live basicOps goal 6 (wsOf c137.2 e).toFinset := level_sound hR137 6 k137_6_3 (D137_5.map (wsOf c137.2)) (map_dead w137_5) (by decide +kernel)
def k137_6_4 : List Entry := [([55,78,66,108],[],[]),([55,78,66,124],[],[]),([55,94,66,108],[],[]),([55,574,52,365],[],[]),([55,574,52,1125],[],[]),([55,590,52,877],[],[]),([55,590,52,1125],[],[]),([55,855,56,88],[],[]),([55,855,56,92],[],[]),([55,855,92,68],[],[]),([55,893,598,56],[],[]),([55,893,598,60],[],[]),([63,50,1397,44],[],[]),([63,54,72,1125],[],[]),([63,54,76,846],[16],[]),([63,54,76,1125],[],[]),([63,54,86,88],[],[]),([63,54,86,92],[],[]),([63,86,74,76],[],[]),([63,86,74,92],[],[]),([63,86,74,108],[],[]),([63,86,74,300],[],[]),([71,51,300,20],[22],[]),([71,55,88,296],[],[]),([71,58,316,21],[],[]),([71,59,124,588],[],[]),([71,62,86,108],[],[]),([71,62,102,108],[],[]),([71,78,102,108],[],[]),([71,94,70,88],[],[]),([71,94,70,92],[],[]),([71,358,846,36],[21],[]),([71,358,862,36],[3],[]),([71,574,52,46],[],[]),([71,574,78,52],[],[]),([71,574,78,68],[],[]),([71,574,94,52],[],[]),([71,574,94,68],[],[]),([71,574,366,52],[21],[]),([71,574,582,40],[23],[]),([71,574,582,56],[],[]),([71,590,52,46],[],[]),([71,590,52,62],[23],[]),([71,606,52,46],[],[]),([71,606,52,62],[23],[]),([71,847,52,88],[],[]),([71,847,52,92],[],[]),([71,863,52,88],[],[]),([71,863,52,92],[],[31]),([71,1119,68,92],[3,5],[])]
set_option maxRecDepth 100000 in
theorem v137_6_4 : ∀ e ∈ k137_6_4, ¬ Live516.live basicOps goal 6 (wsOf c137.2 e).toFinset := level_sound hR137 6 k137_6_4 (D137_5.map (wsOf c137.2)) (map_dead w137_5) (by decide +kernel)
def k137_6_5 : List Entry := [([71,1119,68,108],[3,5],[]),([87,78,66,92],[],[]),([87,636,839,56],[16],[]),([87,636,847,80],[16],[]),([87,636,847,84],[16],[45,46,47]),([87,847,68,92],[16],[46]),([87,847,68,108],[],[47]),([295,58,102,92],[],[]),([295,62,102,92],[],[]),([295,62,102,380],[16],[]),([295,78,94,100],[],[]),([295,110,124,96],[24,17,6,21],[]),([295,590,52,334],[16],[]),([295,590,52,1125],[],[]),([295,590,350,52],[],[]),([295,590,1397,76],[],[]),([303,54,72,1125],[],[]),([303,54,76,1125],[],[]),([303,54,76,1389],[],[46]),([303,54,92,101],[],[]),([303,54,92,1389],[],[47]),([303,54,94,372],[],[]),([303,54,104,1381],[],[]),([303,54,108,109],[],[]),([303,54,108,1381],[],[]),([303,54,110,124],[],[]),([303,54,110,380],[],[]),([303,54,124,102],[],[]),([303,54,1397,44],[],[]),([303,54,1661,36],[],[45]),([303,62,102,92],[],[]),([303,62,102,380],[16],[]),([303,78,64,1125],[],[]),([303,78,68,334],[16],[]),([303,78,68,1125],[],[]),([303,102,92,862],[],[]),([303,367,140,112],[6],[]),([303,606,48,56],[7,3,28,9,23],[]),([303,1119,56,108],[],[]),([303,1119,60,80],[],[]),([303,1119,60,84],[],[]),([303,1119,60,100],[],[]),([319,54,76,621],[],[33]),([319,54,76,1125],[],[32]),([319,54,92,101],[],[]),([319,54,92,621],[],[34]),([319,54,94,372],[],[]),([319,54,108,621],[],[]),([319,54,108,1381],[],[]),([319,54,637,36],[],[])]
set_option maxRecDepth 100000 in
theorem v137_6_5 : ∀ e ∈ k137_6_5, ¬ Live516.live basicOps goal 6 (wsOf c137.2 e).toFinset := level_sound hR137 6 k137_6_5 (D137_5.map (wsOf c137.2)) (map_dead w137_5) (by decide +kernel)
def k137_6_6 : List Entry := [([319,54,1397,44],[],[]),([319,86,74,88],[],[]),([319,86,74,92],[],[]),([319,86,302,52],[],[]),([319,590,48,1125],[],[]),([319,1119,64,88],[8],[]),([319,1119,64,108],[8],[]),([327,58,102,88],[],[]),([327,58,102,92],[],[]),([327,58,102,108],[],[]),([327,62,102,108],[],[]),([327,94,70,92],[],[]),([327,94,70,108],[],[]),([335,50,102,108],[],[]),([335,51,300,20],[22,23],[]),([335,70,78,96],[],[]),([335,70,78,100],[],[]),([335,86,29,36],[],[]),([335,86,70,76],[],[]),([335,86,78,100],[],[]),([335,366,862,32],[8],[]),([335,590,48,42],[],[]),([365,847,86,92],[8],[]),([365,847,86,108],[],[]),([365,847,86,124],[],[]),([575,54,76,109],[],[42]),([575,54,76,1125],[],[43]),([575,54,78,124],[],[]),([575,54,92,101],[],[]),([575,54,94,372],[],[]),([575,54,108,1381],[],[]),([575,54,1397,44],[],[]),([575,66,1397,44],[],[]),([575,74,108,1381],[],[]),([575,74,1397,44],[],[]),([591,50,102,108],[],[]),([847,86,90,108],[],[]),([1119,50,74,108],[],[]),([1119,86,90,108],[],[]),([1125,62,59,60],[],[]),([1125,62,59,88],[],[]),([1125,62,59,92],[],[]),([1125,62,63,52],[],[]),([1125,62,63,112],[],[]),([1125,62,63,116],[],[]),([1125,62,95,116],[],[])]
set_option maxRecDepth 100000 in
theorem v137_6_6 : ∀ e ∈ k137_6_6, ¬ Live516.live basicOps goal 6 (wsOf c137.2 e).toFinset := level_sound hR137 6 k137_6_6 (D137_5.map (wsOf c137.2)) (map_dead w137_5) (by decide +kernel)
def D137_6 : List Entry := k137_6_0 ++ (k137_6_1 ++ (k137_6_2 ++ (k137_6_3 ++ (k137_6_4 ++ (k137_6_5 ++ (k137_6_6))))))
theorem w137_6 : ∀ e ∈ D137_6, ¬ Live516.live basicOps goal 6 (wsOf c137.2 e).toFinset := (app_dead v137_6_0 (app_dead v137_6_1 (app_dead v137_6_2 (app_dead v137_6_3 (app_dead v137_6_4 (app_dead v137_6_5 v137_6_6))))))
def k137_7_0 : List Entry := [([19,26,56],[6,0,10,28],[0,1]),([19,26,60],[6,28],[2,3]),([19,26,86],[0,28,23],[4,5]),([19,26,94],[0,28,23],[]),([19,26,102],[0,16],[6,7,8]),([19,26,110],[0],[]),([19,26,342],[6,22],[]),([19,26,1397],[0],[0,2]),([19,26,1661],[0],[1,3]),([19,62,1397],[6],[]),([19,62,1661],[6],[]),([19,78,86],[6,28,23],[]),([19,78,1397],[6],[]),([19,94,86],[6],[]),([19,94,94],[6,16,28,23],[9]),([19,94,102],[6,28,23],[]),([19,94,110],[6,28,23],[]),([19,94,298],[0,6],[]),([19,110,102],[6,28,23],[]),([19,110,124],[6,23,24,26],[10]),([19,124,102],[6,23],[]),([19,124,327],[0],[]),([19,300,20],[10,3,14,5,22,24,28],[11,12,13,14,15,16,17,18,19]),([19,300,1119],[0,28,23],[17]),([19,300,1125],[0,28,6,22],[20,18]),([19,300,1389],[0,28,6,22,14,24,23],[19]),([19,343,76],[0],[]),([19,359,76],[0],[]),([19,359,108],[0,28,27],[]),([19,359,652],[21,16,0],[21]),([19,574,1397],[6],[]),([19,574,1661],[6],[]),([19,590,1397],[6],[]),([19,1119,52],[28,23],[]),([19,1119,116],[14,28,23,5],[]),([19,1391,52],[28,23],[]),([19,1397,44],[6,28,21],[]),([19,1397,126],[20,21],[20]),([19,1661,36],[24,6,21,14,23],[21]),([23,54,78],[10],[]),([23,54,94],[10,28,23],[]),([23,54,110],[10],[]),([23,54,1397],[10],[2]),([23,54,1661],[10],[3]),([23,56,311],[0],[]),([23,56,327],[0,1,28,23],[22]),([23,56,343],[0,16],[23,24]),([23,56,575],[6,1],[25,26]),([23,56,591],[6,28,23],[]),([23,56,607],[6,28],[27])]
set_option maxRecDepth 100000 in
theorem v137_7_0 : ∀ e ∈ k137_7_0, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_0 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_1 : List Entry := [([23,56,621],[6,28,10,22,23,0],[28,26]),([23,56,847],[10,16,28,23],[29]),([23,56,1119],[10,28,23],[]),([23,56,1125],[10,28,22],[30,31]),([23,56,1389],[10,28,23,24,14],[32,24]),([23,57,326],[10],[33,25]),([23,57,342],[10,28,23],[34,22]),([23,57,358],[10,16],[35,36,37]),([23,57,568],[0,10,1,28],[38,11,37,39,40]),([23,57,598],[1],[]),([23,57,846],[14,1],[]),([23,57,1397],[10],[2,39]),([23,57,1661],[10],[3,40]),([23,60,55],[14],[]),([23,60,71],[28,23],[]),([23,60,87],[24,16],[41]),([23,60,311],[0],[]),([23,60,327],[0,28,23],[]),([23,60,343],[0,16],[42,43]),([23,60,575],[6],[]),([23,60,591],[6,28,23],[]),([23,60,607],[6,28],[44]),([23,60,621],[6,28,22,23],[45]),([23,60,847],[14,16,28,23],[46]),([23,60,1119],[24,28,23],[]),([23,60,1125],[28,22],[47,48]),([23,60,1389],[24,28,23,14],[49,43]),([23,61,326],[14],[50]),([23,61,342],[28,23],[51]),([23,61,358],[24,16],[52,53]),([23,61,568],[0,1,28],[54,55,56,57]),([23,61,598],[1],[]),([23,61,846],[14,1],[]),([23,61,1397],[10,28],[56]),([23,61,1661],[10,24],[57]),([23,62,70],[10,14],[]),([23,62,86],[10,3,28,23],[]),([23,62,102],[10,24,16],[58]),([23,62,1397],[10,28],[]),([23,62,1661],[10,24],[]),([23,70,72],[10,28,16],[59,60]),([23,70,76],[28,16],[61,62]),([23,70,78],[10,14],[]),([23,70,94],[14,28,23],[]),([23,70,893],[6],[59,61]),([23,70,1397],[14],[60,62]),([23,71,56],[0,5],[25]),([23,71,88],[10,5],[63]),([23,71,92],[10,14,5],[]),([23,78,70],[10],[])]
set_option maxRecDepth 100000 in
theorem v137_7_1 : ∀ e ∈ k137_7_1, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_1 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_2 : List Entry := [([23,78,86],[14,28,23],[]),([23,78,893],[6],[]),([23,78,1397],[14],[]),([23,86,29],[22],[64,65]),([23,86,41],[0],[64,66]),([23,86,42],[0],[]),([23,86,61],[6],[65,66,67]),([23,86,62],[6,28,23],[]),([23,86,70],[10,28,23],[5,68]),([23,86,72],[10,28,22,23],[]),([23,86,73],[10,28,23],[5,67]),([23,86,76],[28,22,23],[]),([23,86,77],[10,28,23],[]),([23,86,78],[10,28],[]),([23,86,86],[14,16,28,23],[69,70,71]),([23,86,94],[14],[]),([23,86,102],[24,16,28,23],[72,73,74]),([23,86,110],[24,28,21],[]),([23,86,334],[10],[]),([23,87,56],[0],[64]),([23,87,76],[6],[65,22]),([23,87,88],[10],[63,75]),([23,87,92],[10,22],[76]),([23,87,840],[0,28,23],[77,78,79,75,76]),([23,94,70],[10],[]),([23,94,78],[10,28,23],[]),([23,94,86],[14],[]),([23,94,94],[14,16,28,23],[80]),([23,94,102],[24,28,21],[]),([23,94,110],[24,28,23],[]),([23,94,298],[0],[65]),([23,94,318],[6,23],[64]),([23,95,568],[22],[]),([23,95,840],[0,28,23],[81,82]),([23,102,42],[0,28,27],[]),([23,102,62],[6],[]),([23,102,72],[10,24,28,27],[]),([23,102,76],[24,28,27],[]),([23,102,78],[10,24],[]),([23,102,92],[24,28,27],[]),([23,102,110],[24,28,21],[]),([23,102,614],[22],[]),([23,102,622],[],[]),([23,103,56],[0,26],[]),([23,103,76],[6,26],[]),([23,103,88],[10],[63,83]),([23,103,92],[10,24],[84]),([23,103,108],[24],[36,53,85]),([23,103,840],[0,16],[86,87,88,83,84,85,37]),([23,110,70],[10],[])]
set_option maxRecDepth 100000 in
theorem v137_7_2 : ∀ e ∈ k137_7_2, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_2 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_3 : List Entry := [([23,110,102],[24,28,21],[]),([23,110,614],[],[]),([23,110,622],[],[]),([23,111,840],[0,24,1],[89,90]),([23,296,30],[0,3,1,10,14,5,22,24,28],[54,11,55,78,81,87,89,91,92]),([23,296,44],[10,2,3,14,5,22,24,28],[38,54,79,82,88,90,93,94,95]),([23,296,46],[0,10,3,28],[96,97]),([23,296,1119],[0,28,23],[17,93]),([23,296,1125],[0,28,22],[98,18,91,94,96,39,56]),([23,296,1389],[0,28,22,14,24,23],[19,92,95,97,40,57]),([23,310,56],[0,6,10,3,1,8,28],[99,100,101]),([23,310,94],[],[102]),([23,310,316],[6,3,10,28],[99,103,102,104,105]),([23,310,846],[5],[106]),([23,310,1397],[10],[100,104]),([23,310,1661],[10],[101,105]),([23,318,86],[8],[]),([23,318,312],[0,6,1,28],[107,108]),([23,318,1397],[0,10],[107]),([23,318,1661],[0,10],[108]),([23,342,56],[6,28,22,1,23],[109,110,111]),([23,342,57],[6,28,23],[112,113]),([23,342,61],[6],[]),([23,342,70],[3],[114,115]),([23,342,78],[3],[]),([23,342,318],[6,22,23],[]),([23,342,334],[3],[116]),([23,342,350],[5],[117]),([23,342,838],[6,3],[]),([23,342,846],[3],[118]),([23,342,854],[],[]),([23,342,862],[5],[119]),([23,343,72],[0,6,1],[120,121]),([23,350,38],[0],[]),([23,350,70],[3],[]),([23,359,72],[0],[]),([23,359,108],[0],[23,42]),([23,359,652],[16,0],[24,43]),([23,566,78],[3],[]),([23,566,1397],[6,10],[107]),([23,566,1661],[6,10],[108]),([23,574,52],[0,10,8,1,3,28],[99,122,123]),([23,574,70],[],[103]),([23,574,1397],[10],[122,104]),([23,574,1661],[10],[123,105]),([23,575,396],[10,7,8],[]),([23,582,78],[8],[]),([23,582,1397],[],[]),([23,590,52],[0,14,5,1,28,16],[124,125,126,127]),([23,590,70],[5],[])]
set_option maxRecDepth 100000 in
theorem v137_7_3 : ∀ e ∈ k137_7_3, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_3 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_4 : List Entry := [([23,590,1397],[14],[127]),([23,591,68],[0,28,1],[128,129,130]),([23,591,396],[14],[130,26]),([23,607,68],[0,6,23],[]),([23,623,68],[0],[]),([23,623,140],[6],[131,27,44]),([23,637,118],[6],[28,45]),([23,847,48],[10,14],[]),([23,847,52],[10,3,28,8,5],[132]),([23,863,48],[10,3],[]),([23,863,52],[10,8,3],[116]),([23,879,48],[10,24],[]),([23,879,52],[10,28,27],[]),([23,1119,48],[5],[133,134]),([23,1119,52],[5],[117]),([23,1119,116],[14,5],[29,46]),([23,1391,48],[24],[135,136]),([23,1391,52],[],[]),([23,1397,78],[6],[30,47]),([23,1397,126],[24],[31,48,98]),([23,1661,70],[6],[32,49]),([27,60,1119],[0,28,23],[93]),([27,60,1125],[0,28,6,22],[137,94]),([27,60,1389],[0,28,6,22,14,24,23],[95]),([27,62,1397],[0],[96]),([27,62,1661],[0],[97]),([27,72,1125],[0,28,6,16],[]),([27,76,1119],[0,28,23],[]),([27,76,1125],[0,28,6,22],[138]),([27,76,1389],[0,28,6,22,24,4,23],[]),([27,78,1397],[0],[]),([27,92,87],[0,28,9,24],[]),([27,92,95],[0,28,24],[139,140]),([27,92,101],[0,28,6,9],[141]),([27,92,1389],[0,28,23,6,24,14],[142,140]),([27,94,102],[0,28,9,24],[]),([27,94,110],[0,28,23],[]),([27,94,366],[0,28,23,24],[]),([27,94,372],[0,9],[143]),([27,104,1381],[0,28,24,6],[]),([27,108,87],[0,28,21,22],[]),([27,108,109],[0,28,6,21,14],[]),([27,108,1381],[0,28,9,21],[]),([27,110,102],[0,28,21,22],[]),([27,110,124],[0,21,6,14],[]),([27,110,380],[0,28,6,21,14],[]),([27,124,102],[0,23,6],[]),([27,1391,52],[0,28,20,24,23],[]),([27,1397,44],[0,28,6,9,21],[]),([27,1397,126],[20,21],[143,137,138,98])]
set_option maxRecDepth 100000 in
theorem v137_7_4 : ∀ e ∈ k137_7_4, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_4 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_5 : List Entry := [([27,1661,36],[0,28,6,21,14,24,23],[]),([31,54,1397],[0],[]),([31,54,1661],[0],[]),([31,70,893],[0],[]),([31,70,1397],[0],[]),([31,86,102],[0,16,28,23],[144]),([31,86,110],[0,28,21],[]),([31,86,318],[0,6,23],[]),([31,102,92],[24,28,27],[]),([31,102,110],[0,28,21,22],[]),([31,102,380],[28,21,0,16],[145]),([31,102,614],[22,21],[]),([31,310,1397],[0],[]),([31,310,1661],[0],[]),([31,342,41],[0],[]),([31,342,318],[0,6,23],[]),([31,607,64],[0,23],[]),([31,623,64],[0],[]),([31,623,140],[6,24,21],[146]),([31,637,118],[6],[]),([31,1391,48],[23],[]),([31,1397,78],[6],[]),([31,1397,126],[24],[20]),([31,1661,70],[6,24],[145]),([39,50,78],[6],[]),([39,50,94],[6,28,23],[]),([39,50,110],[6,28],[147]),([39,50,124],[6,22,23],[148]),([39,50,1397],[22],[149]),([39,50,1661],[23],[150]),([39,58,60],[0,6,28],[99,151,152]),([39,58,72],[10,14,6,28,16],[153]),([39,58,76],[6,2,28],[154,155,156]),([39,58,78],[6],[]),([39,58,88],[28,22,6,23],[]),([39,58,92],[6,22,28,0,10,8],[157,158,159,160]),([39,58,94],[6,28,23],[161]),([39,58,104],[6,24,28],[162]),([39,58,108],[28,6,10,8],[163,164]),([39,58,110],[6,28],[165,166]),([39,58,124],[6,22,23],[167]),([39,58,316],[6,3,10,28],[168,169]),([39,58,366],[24],[170,154,158]),([39,58,380],[6,23,0,10,8],[171,159]),([39,58,1397],[22,10],[172,161,151,153,155,162,164,100,168]),([39,58,1661],[23,24,10,16],[173,166,152,156,160,101,169]),([39,62,366],[24],[174]),([39,62,380],[28,22,23],[175]),([39,62,1397],[22],[]),([39,62,1661],[23],[])]
set_option maxRecDepth 100000 in
theorem v137_7_5 : ∀ e ∈ k137_7_5, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_5 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_6 : List Entry := [([39,70,94],[10,28,23],[]),([39,70,1397],[10],[]),([39,78,70],[10,8],[]),([39,78,86],[10,28,23],[]),([39,78,1149],[10],[]),([39,78,1397],[10],[]),([39,86,72],[8,28,22,0,10,23],[]),([39,86,76],[28,8,22,23],[]),([39,86,94],[10],[]),([39,86,110],[10,28,21],[]),([39,94,70],[10,28,23],[]),([39,94,86],[10],[]),([39,94,102],[10,28,21],[]),([39,94,846],[],[102]),([39,94,862],[2],[]),([39,102,92],[24,28,8,21],[]),([39,102,110],[10,28,21],[]),([39,110,70],[10],[]),([39,110,102],[10,28,21],[]),([39,359,108],[0],[]),([39,359,652],[16,0],[]),([39,574,52],[0,10,2,28,7],[176,177]),([39,574,70],[],[103]),([39,574,1397],[],[151,176,168,104]),([39,574,1661],[],[152,177,169,105]),([39,590,52],[0,2,8,14,5,28,16],[178,179]),([39,590,1397],[14],[179]),([39,847,52],[5],[106]),([39,863,52],[8,23],[]),([39,863,60],[10,28,23],[]),([39,879,52],[8,28,27],[]),([39,879,140],[10],[180,170,174]),([39,893,118],[10],[171,175]),([39,1119,48],[5],[]),([39,1119,52],[5],[]),([39,1119,116],[10],[]),([39,1391,48],[10],[]),([39,1391,52],[],[]),([39,1397,94],[10],[]),([39,1397,126],[10],[]),([39,1661,86],[10],[]),([47,50,94],[0,28,23],[]),([47,50,110],[0,28],[181]),([47,50,124],[6,22,23],[182]),([47,50,1397],[22,0],[183]),([47,50,1661],[23,0],[184]),([47,54,86],[0,8,28,23],[]),([47,54,102],[0,8,16],[185]),([47,54,308],[0,6,1,28],[186,187]),([47,54,1397],[0],[2,186])]
set_option maxRecDepth 100000 in
theorem v137_7_6 : ∀ e ∈ k137_7_6, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_6 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_7 : List Entry := [([47,54,1661],[0],[3,187]),([47,70,842],[],[]),([47,70,862],[],[]),([47,70,1149],[0],[]),([47,70,1397],[0],[]),([47,86,78],[0,28,23],[]),([47,86,102],[0,16,28,23],[188]),([47,86,110],[0,28,21],[]),([47,86,334],[0,8,23],[]),([47,102,78],[0],[]),([47,102,92],[24,10,28,27],[189]),([47,102,110],[0,28,21,22],[]),([47,102,380],[28,21,0,16],[190]),([47,102,878],[21],[189]),([47,570,56],[0,1,28],[191,192]),([47,570,94],[],[]),([47,570,1397],[],[193,2,191,186,107]),([47,570,1661],[],[3,192,187,108]),([47,606,48],[0,3,8,28,22,23],[]),([47,863,48],[8],[]),([47,879,48],[28,27],[]),([47,879,140],[24,21,10],[194]),([47,893,118],[10],[]),([47,1391,48],[23],[]),([47,1397,94],[10],[]),([47,1397,126],[10],[]),([47,1661,86],[24,10],[190]),([55,50,78],[6],[]),([55,50,94],[6,28,23],[]),([55,50,108],[28,17,6],[195]),([55,50,124],[6,22,16],[]),([55,50,1397],[22,16],[196,195]),([55,58,60],[0,6,28,16],[197]),([55,58,78],[6],[]),([55,58,94],[6,28,23],[]),([55,58,124],[6,22,16],[]),([55,58,316],[6,5,28,16],[198]),([55,58,1397],[22],[199,197,198]),([55,62,70],[10],[]),([55,62,86],[14,28,23],[]),([55,62,381],[6],[]),([55,62,846],[10],[]),([55,62,1397],[14],[]),([55,78,66],[10,16,28],[200,201]),([55,78,70],[10,3],[]),([55,78,86],[10,28,23],[]),([55,78,846],[],[]),([55,78,1149],[10],[]),([55,78,1397],[10],[]),([55,86,74],[14,5,28,23],[])]
set_option maxRecDepth 100000 in
theorem v137_7_7 : ∀ e ∈ k137_7_7, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_7 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_8 : List Entry := [([55,86,78],[14,28,23],[]),([55,86,94],[10],[]),([55,86,108],[28,17,21,23],[]),([55,94,66],[14,4,16,28,23],[202]),([55,94,70],[14,28,23],[]),([55,94,86],[10],[]),([55,94,846],[],[]),([55,94,862],[4],[]),([55,574,52],[0,4,28,16],[203,204]),([55,574,70],[],[]),([55,574,381],[6],[203]),([55,574,1397],[],[197,204,198]),([55,590,52],[0,4,10,3,5,28,16],[205,206]),([55,590,70],[14,3],[]),([55,590,1149],[10],[205]),([55,590,1397],[10],[206]),([55,839,56],[3],[]),([55,839,60],[3],[]),([55,839,92],[6,3],[]),([55,839,140],[6,14],[]),([55,847,48],[10],[]),([55,847,52],[3],[]),([55,855,56],[6],[207,208]),([55,855,60],[],[]),([55,855,92],[6],[209]),([55,863,48],[14],[]),([55,863,52],[],[]),([55,863,60],[14,28,23],[]),([55,893,598],[10],[210,211]),([55,1119,48],[3],[]),([55,1119,52],[3],[]),([55,1397,94],[14],[]),([63,50,94],[0,28,23],[]),([63,50,124],[6,22,16],[]),([63,50,1397],[22],[212]),([63,54,72],[10,28,1,16],[213]),([63,54,76],[28,1,14,24,16],[214,215]),([63,54,86],[0,28,23],[216,217]),([63,54,94],[0,28,23],[]),([63,54,381],[0,1],[]),([63,54,862],[16],[214]),([63,54,1397],[0],[213,215]),([63,70,862],[16],[]),([63,70,1149],[2,0],[]),([63,70,1397],[0],[]),([63,86,66],[0,28,23],[]),([63,86,74],[0,22,16,23],[218,219,220,221]),([63,86,78],[0,28,23],[]),([63,86,334],[0,23],[221]),([63,606,48],[0,5,28,22,23],[])]
set_option maxRecDepth 100000 in
theorem v137_7_8 : ∀ e ∈ k137_7_8, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_8 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_9 : List Entry := [([63,855,56],[1],[]),([63,863,48],[],[]),([63,1397,94],[14],[]),([71,50,42],[0,1],[]),([71,50,78],[6],[]),([71,50,94],[6],[]),([71,50,110],[6,28,21],[]),([71,51,56],[0,6],[]),([71,51,300],[22],[222]),([71,55,56],[0],[66]),([71,55,88],[10,28,23],[223,67]),([71,55,92],[28,23],[]),([71,55,296],[22],[222,223]),([71,58,60],[28,9,6,23],[]),([71,58,76],[6,10,28,9,23],[110,120]),([71,58,78],[6,10],[111]),([71,58,88],[6,28,9,16],[]),([71,58,92],[6,28,9,23],[121]),([71,58,94],[6],[]),([71,58,104],[24,6,28,9],[]),([71,58,108],[28,21,6,22],[]),([71,58,110],[6,28,21],[]),([71,58,316],[6,28,9,23],[224]),([71,59,60],[0],[]),([71,59,76],[0,28,23],[]),([71,59,92],[6,28,23],[112]),([71,59,104],[6,28,23],[]),([71,59,108],[6,28,23],[113]),([71,59,120],[6,28,23],[]),([71,59,124],[6,28,23],[225]),([71,59,588],[6,23,28],[225]),([71,62,70],[10,28,23],[]),([71,62,78],[10],[]),([71,62,86],[14,16,28,23],[226]),([71,62,94],[14],[]),([71,62,102],[24,16,28,23],[227]),([71,62,110],[24,28,21],[]),([71,62,846],[10],[]),([71,63,588],[6,23],[]),([71,71,56],[0,3],[]),([71,71,88],[10,3,28,23],[]),([71,71,92],[10,28,23],[]),([71,78,66],[10,28,23],[]),([71,78,70],[10,3],[]),([71,78,86],[10],[]),([71,78,102],[10,16,21],[228]),([71,78,846],[23],[]),([71,87,56],[0,5],[]),([71,87,124],[14,28,23],[]),([71,94,66],[14,28,23],[])]
set_option maxRecDepth 100000 in
theorem v137_7_9 : ∀ e ∈ k137_7_9, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_9 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_10 : List Entry := [([71,94,70],[14],[229,230]),([71,94,86],[10],[]),([71,102,74],[24,21,28,23],[]),([71,102,78],[24,28,23],[]),([71,102,94],[10],[]),([71,102,108],[24,28,20,23],[]),([71,103,76],[20,21],[]),([71,103,124],[24,28,23],[]),([71,110,66],[24,28,23],[]),([71,110,70],[24,28,23],[]),([71,110,86],[10,28,23],[]),([71,358,78],[21],[]),([71,358,846],[21,23],[231]),([71,358,862],[3,21],[232]),([71,359,124],[0,28,23],[]),([71,366,70],[],[]),([71,366,846],[23],[]),([71,574,37],[0,6,28,9,23],[]),([71,574,49],[0,23],[]),([71,574,52],[0,22,23],[233]),([71,574,53],[0,28,9,23],[]),([71,574,70],[],[]),([71,574,78],[],[234,235]),([71,574,86],[],[]),([71,574,94],[],[236,237]),([71,574,358],[23],[]),([71,574,366],[21],[238]),([71,574,582],[23],[239,240]),([71,590,52],[0,28,23],[241,242]),([71,590,70],[3],[]),([71,590,86],[],[]),([71,606,52],[0,28,23],[243,244]),([71,606,70],[5],[]),([71,606,86],[],[]),([71,839,56],[3,28,23],[]),([71,839,60],[28,23],[]),([71,839,72],[6,3],[]),([71,839,92],[6,3],[]),([71,847,48],[10,28,23],[]),([71,847,52],[3,10],[245,246,118]),([71,855,56],[6,28,23],[]),([71,855,60],[28,23],[]),([71,855,72],[6,5],[]),([71,855,76],[0],[]),([71,855,92],[6,5],[]),([71,855,124],[6,28,23],[]),([71,863,48],[14,28,23],[]),([71,863,52],[5],[247,248,119]),([71,871,56],[6,28,23],[]),([71,871,60],[28,23],[])]
set_option maxRecDepth 100000 in
theorem v137_7_10 : ∀ e ∈ k137_7_10, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_10 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_11 : List Entry := [([71,871,72],[6,21],[]),([71,871,76],[0],[]),([71,871,92],[6,21],[]),([71,871,124],[6,28,23],[]),([71,879,48],[24,28,23],[]),([71,879,52],[21,28,23],[238]),([71,1119,48],[10,28,23],[]),([71,1119,52],[14,10,3,5],[]),([71,1119,64],[3],[]),([71,1119,68],[22,23,3,5],[249,250]),([71,1135,48],[10,28,23],[]),([71,1135,52],[3,21],[]),([79,50,110],[0,28,21],[]),([79,54,102],[0,28,21],[]),([79,54,110],[0,28,23],[]),([79,100,59],[0,28,23,21],[]),([79,100,63],[0,28,23,21],[]),([79,102,74],[0,28,23,21],[]),([79,102,78],[0,28,23,21],[]),([79,358,78],[],[]),([79,871,56],[0,28,23],[]),([79,871,72],[21],[]),([79,871,124],[24,21,28,23],[]),([79,879,48],[0,28,23,21],[]),([87,58,78],[6],[]),([87,58,110],[6,28,23,21],[]),([87,62,70],[10],[]),([87,62,78],[10,24],[]),([87,62,102],[24,28,23],[]),([87,62,110],[24,21,28,23],[]),([87,78,66],[10,16,28,27],[251]),([87,78,70],[10,3],[]),([87,78,102],[10,28,23],[]),([87,92,839],[10,28,27],[]),([87,92,847],[10],[]),([87,92,855],[24,28,23],[]),([87,92,863],[24,28,23],[]),([87,92,1119],[10,28,23],[]),([87,110,74],[24,21,28,23],[]),([87,110,94],[10,21,28,23],[]),([87,636,54],[24,17,21,16],[]),([87,636,839],[10,17,16],[252]),([87,636,847],[10,16],[253,254]),([87,839,60],[],[]),([87,847,52],[3,28,27],[]),([87,847,64],[24,16],[253]),([87,847,68],[24,16],[255,256,254]),([87,871,60],[],[]),([87,879,52],[21],[231]),([87,1135,52],[3],[232])]
set_option maxRecDepth 100000 in
theorem v137_7_11 : ∀ e ∈ k137_7_11, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_11 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_12 : List Entry := [([95,50,110],[0,28,23],[]),([95,54,102],[0,28,23],[]),([95,54,110],[0,28,23],[]),([95,102,66],[0,28,23],[]),([95,102,334],[0,28,21,23],[]),([95,871,56],[],[]),([95,879,48],[],[]),([295,58,102],[6,3,16],[257]),([295,58,1397],[6],[2,191]),([295,58,1661],[6],[3,192]),([295,62,70],[0],[]),([295,62,86],[0,28,23],[]),([295,62,102],[0,16],[258,259]),([295,62,1397],[6],[]),([295,62,1661],[24,6],[259]),([295,78,66],[6],[]),([295,78,86],[6,28,23],[]),([295,78,94],[6,16,28,23],[260]),([295,78,350],[6,16,22],[]),([295,78,1397],[6],[]),([295,94,66],[6,10],[]),([295,94,86],[6],[]),([295,94,102],[6,28,9],[]),([295,94,110],[6,28,23],[]),([295,94,862],[14],[]),([295,110,66],[6,28,27],[]),([295,110,102],[6,28,21],[]),([295,110,124],[6,17,21,24],[261]),([295,124,102],[6,23],[]),([295,590,52],[6,8,14,3,24,28,16],[262,263]),([295,590,350],[16],[264,262]),([295,590,1397],[14],[265,263]),([295,1119,52],[28,23],[264]),([295,1119,116],[10,28,23],[]),([295,1391,52],[28,20],[]),([295,1397,44],[6,28,9,21,10],[193,265]),([295,1397,126],[20,21,10],[]),([295,1661,36],[24,6,21,14,23],[252]),([303,50,1397],[10],[]),([303,50,1661],[10],[253]),([303,54,72],[28,7,16],[266]),([303,54,76],[14,0,6,28,7,3],[255,267,268]),([303,54,78],[0,14],[]),([303,54,88],[10,3,28,22,7,23],[]),([303,54,92],[28,7,0],[269,256,270]),([303,54,94],[0,28,23],[271]),([303,54,104],[24,28,7],[272]),([303,54,108],[28,7,3],[273,274]),([303,54,110],[0,28],[275,276]),([303,54,124],[7,22,23],[277])]
set_option maxRecDepth 100000 in
theorem v137_7_12 : ∀ e ∈ k137_7_12, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_12 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_13 : List Entry := [([303,54,1397],[22,10],[278,271,151,266,267,272,274,122,176]),([303,54,1661],[23,24,10,16],[279,276,254,152,268,270,123,177]),([303,62,70],[0],[]),([303,62,86],[0,28,23],[]),([303,62,102],[0,16],[280,281]),([303,62,1397],[10],[]),([303,62,1661],[24],[281]),([303,70,74],[10],[]),([303,70,94],[10,28,23],[]),([303,70,862],[7],[]),([303,70,1397],[10],[]),([303,78,64],[28,8,16],[282]),([303,78,68],[14,3,24,6,28,8,10,16],[283,284]),([303,78,86],[10,28,23],[]),([303,78,350],[22,16],[283]),([303,78,1397],[10],[282,284]),([303,86,74],[10,3],[]),([303,86,94],[10],[]),([303,86,110],[10,28,21],[]),([303,94,86],[10],[]),([303,94,102],[10,28,21],[]),([303,102,74],[10],[]),([303,102,92],[24,28,7,21],[285]),([303,102,110],[10,28,21],[]),([303,102,878],[],[285]),([303,110,102],[10,28,21],[]),([303,367,140],[6],[286]),([303,381,118],[6],[]),([303,606,48],[6,3,28,9,7,23],[287]),([303,1119,48],[22],[]),([303,1119,52],[10],[]),([303,1119,56],[10,16,28,23],[288]),([303,1119,60],[10,16,28,23],[289,290,291]),([303,1119,116],[10],[]),([303,1391,48],[],[]),([303,1391,52],[10],[]),([303,1397,62],[6],[]),([303,1397,126],[10],[]),([303,1661,54],[6],[]),([311,58,1397],[6],[]),([311,62,86],[0,28,23],[]),([311,62,1397],[6],[]),([311,78,1397],[6],[]),([311,94,66],[6,14],[]),([311,108,1381],[6,28,9,17],[]),([311,1397,44],[6,28,9,16],[]),([319,50,70],[10],[]),([319,50,637],[6],[]),([319,50,1397],[14],[]),([319,54,76],[10,0,28,14,5,16],[125,128,292,293])]
set_option maxRecDepth 100000 in
theorem v137_7_13 : ∀ e ∈ k137_7_13, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_13 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_14 : List Entry := [([319,54,78],[0,10],[126]),([319,54,88],[14,5,28,22,23],[]),([319,54,92],[28,0,16],[294,129,295]),([319,54,94],[0,28,23],[296]),([319,54,108],[14,5,28,17],[297,298]),([319,54,124],[18,22,16,5],[]),([319,54,637],[14,6,23,16],[299,130,292,295,297,203]),([319,54,1397],[22,14,16],[300,296,197,293,298,127,204]),([319,62,38],[0,1],[]),([319,62,70],[0],[]),([319,62,86],[0,28,23],[]),([319,62,637],[6],[]),([319,62,1397],[14],[]),([319,70,74],[10,5],[]),([319,70,94],[10,28,23],[]),([319,70,862],[16],[]),([319,70,1397],[10],[]),([319,86,74],[14],[301,302]),([319,86,86],[10,14,28,23],[]),([319,86,94],[10],[]),([319,86,302],[6,23],[303]),([319,86,862],[10],[]),([319,94,38],[6,28,23],[]),([319,94,86],[10],[]),([319,94,100],[28,17,21,23],[]),([319,351,68],[6],[303]),([319,590,48],[6,5,28,16],[304]),([319,590,86],[],[]),([319,590,1397],[10],[304]),([319,606,48],[6,5,28,9,16],[]),([319,606,86],[],[]),([319,1119,48],[8],[]),([319,1119,52],[10],[]),([319,1119,64],[14,8],[305,306]),([319,1119,68],[14],[]),([319,1397,62],[6],[]),([327,58,72],[6,10,28,22,23],[]),([327,58,76],[6,28,22,23],[]),([327,58,94],[6],[]),([327,58,102],[6,16],[307,308,309]),([327,58,110],[6],[]),([327,62,86],[0],[]),([327,62,102],[0,16,21],[310]),([327,94,66],[6],[]),([327,94,70],[6,14,16,28,23],[236,311,312,209]),([327,94,78],[6],[]),([327,110,66],[6,28,23],[]),([327,110,70],[6,28,23,21],[]),([335,50,70],[10],[]),([335,50,78],[10],[])]
set_option maxRecDepth 100000 in
theorem v137_7_14 : ∀ e ∈ k137_7_14, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_14 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_15 : List Entry := [([335,50,94],[14],[]),([335,50,102],[24,16],[313]),([335,50,110],[24],[]),([335,50,846],[10],[]),([335,51,300],[22,23],[314]),([335,54,78],[0],[]),([335,54,94],[0],[]),([335,54,110],[0,21],[]),([335,55,296],[22,23],[314]),([335,59,60],[6,23],[66]),([335,59,88],[10,28,23],[]),([335,59,92],[28,23],[]),([335,62,38],[0,28,23],[]),([335,62,70],[0],[]),([335,62,86],[0],[]),([335,62,96],[24,28,23],[]),([335,62,100],[28,21,23],[]),([335,62,102],[0,28,21],[]),([335,63,52],[0,6,23],[]),([335,63,112],[0,28,23],[]),([335,63,116],[0,28,23],[]),([335,70,74],[10,8],[]),([335,70,78],[10,28,23],[315,316]),([335,70,94],[10],[]),([335,70,110],[10],[]),([335,79,52],[6,23,8],[]),([335,86,29],[14],[317,303]),([335,86,70],[14],[318]),([335,86,74],[14],[]),([335,86,78],[14,16,28,23],[319]),([335,86,86],[10],[]),([335,86,94],[10],[]),([335,95,52],[6,23],[317]),([335,95,116],[14,28,23],[]),([335,102,74],[24,28,23],[]),([335,102,78],[24,21,28,23],[]),([335,102,94],[10,28,23],[]),([335,110,66],[24],[]),([335,110,70],[24],[]),([335,110,86],[10],[]),([335,111,68],[20,21,28,23],[]),([335,366,862],[8,21],[320]),([335,590,48],[6,10,8,28,9,23],[321]),([335,590,66],[8,23],[]),([335,1119,48],[10,8],[]),([335,1119,52],[14,28,23],[]),([335,1119,572],[10,16],[]),([335,1135,48],[8,21],[]),([335,1135,52],[10,28,23],[]),([343,58,110],[6,24,28,23],[])]
set_option maxRecDepth 100000 in
theorem v137_7_15 : ∀ e ∈ k137_7_15, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_15 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_16 : List Entry := [([343,62,102],[0,28,23],[]),([343,110,78],[6,24,21,28,23],[]),([351,50,70],[10,24,28,27],[]),([351,50,78],[10],[]),([351,50,110],[24,28,23],[]),([351,54,78],[0],[]),([351,54,110],[0,28,23],[]),([351,70,74],[10,8],[]),([351,70,78],[10],[]),([351,70,110],[10,28,23],[]),([351,102,70],[24,21,28,23],[]),([351,102,86],[10,28,23],[]),([351,124,96],[6,20,21,10,14,16],[131,146,286,180,194]),([351,1135,48],[8,28,23],[320]),([365,847,82],[10],[]),([365,847,86],[10,14,18,23,16,8],[322,323,324,205]),([575,50,1397],[10],[]),([575,54,76],[8,0,10,3,28,14,5,16],[325,178,249,326]),([575,54,78],[0,10,28,8,3],[327,322]),([575,54,88],[22,23],[]),([575,54,92],[28,16],[328,323]),([575,54,94],[0,28,23],[329]),([575,54,108],[14,5,28,17,10,3],[250,324,330]),([575,54,124],[18,23,16],[]),([575,54,1397],[22,14,10,16],[331,329,326,330,179,206]),([575,62,86],[0,28,23],[]),([575,62,1397],[10],[]),([575,66,74],[6,10,5],[]),([575,66,94],[6,28,23],[]),([575,66,124],[6,22,16],[]),([575,66,1397],[22,10],[332,304]),([575,70,862],[16],[262]),([575,70,1397],[10,14],[263]),([575,74,94],[6,28,23],[]),([575,74,108],[28,17,6],[333]),([575,74,124],[6,22,16],[]),([575,74,1397],[22,16],[334,333]),([575,86,74],[10,14],[]),([575,86,94],[10,28,23],[]),([575,94,100],[28,17,21,8],[]),([575,606,86],[10],[]),([575,1397,110],[10],[]),([591,50,102],[10,3,16],[335]),([591,54,78],[0,10,23],[242]),([591,54,94],[0],[]),([591,54,110],[0,21],[]),([591,62,86],[0],[]),([591,62,96],[24,28,20,8],[]),([591,62,100],[28,21,8],[]),([591,62,102],[0,28,21],[])]
set_option maxRecDepth 100000 in
theorem v137_7_16 : ∀ e ∈ k137_7_16, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_16 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_17 : List Entry := [([591,66,72],[6,3,10,8,28,9,23],[287,305]),([591,66,74],[6,10,3,8],[]),([591,66,88],[6,14,28,9,16],[]),([591,66,92],[6,28,9,23],[]),([591,66,94],[6],[]),([591,66,104],[24,6,28,9],[]),([591,66,108],[28,21,6,22,10,8],[306]),([591,66,110],[6,28,21],[]),([591,70,102],[10,28,21],[]),([591,74,94],[6],[]),([591,74,110],[6,28,21],[]),([591,86,74],[10],[]),([591,86,94],[10],[]),([591,102,74],[10,28,23],[]),([591,102,94],[10,28,23],[]),([607,54,78],[0,10,28,27],[]),([607,54,110],[0,28,23],[]),([607,66,74],[6,10],[]),([607,66,110],[6,28,23,21],[]),([847,50,66],[14,5,28,23],[]),([847,54,74],[0,28,23],[]),([847,54,78],[0,23],[244]),([847,54,94],[0],[]),([847,62,66],[0,28,23],[]),([847,62,70],[0,28,23],[]),([847,62,86],[0],[]),([847,62,100],[28,17,21,23],[]),([847,66,74],[6,5],[]),([847,66,94],[6],[]),([847,70,74],[14,28,23],[]),([847,70,94],[10,28,23],[]),([847,74,94],[6],[]),([847,74,108],[28,17,6,9],[]),([847,86,74],[10],[]),([847,86,82],[10,22,23],[]),([847,86,90],[10,16,28,23],[336]),([847,86,94],[10,23],[]),([1119,50,74],[24,20,16,28,23],[337]),([1119,50,78],[24],[]),([1119,50,94],[10],[]),([1119,54,74],[0,28,23],[]),([1119,54,78],[0],[]),([1119,54,94],[0],[]),([1119,66,74],[6],[]),([1119,66,78],[6],[]),([1119,66,94],[6],[]),([1119,70,74],[24,28,23],[]),([1119,70,78],[24,20,26,23],[]),([1119,70,94],[10,28,23],[]),([1119,86,74],[10],[])]
set_option maxRecDepth 100000 in
theorem v137_7_17 : ∀ e ∈ k137_7_17, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_17 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def k137_7_18 : List Entry := [([1119,86,78],[10,26,23],[]),([1119,86,90],[10,16,28,23],[338]),([1119,86,94],[10],[]),([1125,62,59],[28,9],[339,340,341]),([1125,62,63],[28,9],[342,343,344]),([1125,62,79],[10,12],[]),([1125,62,95],[14,15,16],[345])]
set_option maxRecDepth 100000 in
theorem v137_7_18 : ∀ e ∈ k137_7_18, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := level_sound hR137 7 k137_7_18 (D137_6.map (wsOf c137.2)) (map_dead w137_6) (by decide +kernel)
def D137_7 : List Entry := k137_7_0 ++ (k137_7_1 ++ (k137_7_2 ++ (k137_7_3 ++ (k137_7_4 ++ (k137_7_5 ++ (k137_7_6 ++ (k137_7_7 ++ (k137_7_8 ++ (k137_7_9 ++ (k137_7_10 ++ (k137_7_11 ++ (k137_7_12 ++ (k137_7_13 ++ (k137_7_14 ++ (k137_7_15 ++ (k137_7_16 ++ (k137_7_17 ++ (k137_7_18))))))))))))))))))
theorem w137_7 : ∀ e ∈ D137_7, ¬ Live516.live basicOps goal 7 (wsOf c137.2 e).toFinset := (app_dead v137_7_0 (app_dead v137_7_1 (app_dead v137_7_2 (app_dead v137_7_3 (app_dead v137_7_4 (app_dead v137_7_5 (app_dead v137_7_6 (app_dead v137_7_7 (app_dead v137_7_8 (app_dead v137_7_9 (app_dead v137_7_10 (app_dead v137_7_11 (app_dead v137_7_12 (app_dead v137_7_13 (app_dead v137_7_14 (app_dead v137_7_15 (app_dead v137_7_16 (app_dead v137_7_17 v137_7_18))))))))))))))))))
def k137_8_0 : List Entry := [([19,26],[6,0,10,3,1,14,5,22,24,28,8],[0,1,2,3,4,5,6,7,8]),([19,62],[6,10,3,14,7,28],[9,10]),([19,78],[6,14,5,10,8,22,24,16,28],[11,12]),([19,94],[6,22,10,8,14,24,23],[2,13,14,15,16,17]),([19,110],[6,24,26,10,8,14,16,22,28,21],[18,19]),([19,124],[28,23,6,10,8,14,0,24,27],[20,21]),([19,300],[0,6,10,14,3,5,24,22,28],[22,23,24,25]),([19,327],[0,6,5,14,4,28],[21]),([19,343],[0,6,22,23],[2,26,6,17]),([19,359],[0,6,26,24,16,27],[27,28,29]),([19,574],[6,3,7,28],[30,31]),([19,590],[6,4,8,14,5,16,28],[32]),([19,1119],[6,5,16,28,23],[33,34]),([19,1391],[6,26,28,23,24],[35,23]),([19,1397],[6,28,22,10,14,24,21,0],[36,37,7,9,12,24,30,32]),([19,1661],[6,28,23,24,14,10,16,0],[38,29,8,10,25,31]),([23,54],[0,10,3,8,14,22,24,28],[1,39,40,41,42,43]),([23,55],[10,1,7,2,3],[]),([23,56],[6,0,10,1,14,22,24,28,16],[44,45,46,47,48,49,50,51,52,53,54]),([23,57],[0,10,1,14,22,24,28],[1,55,56,57,58,59,60,61,62]),([23,60],[1,14,22,24,28,16],[63,64,65,66,67,68,69,70,71,72,73,74,75,76]),([23,61],[28,10,6,1,14,22,24],[77,78,79,80,81,82,83,84]),([23,62],[10,3,28,14,22,24,8],[85,86,87,88,89]),([23,63],[10,28,6,0,3,8],[]),([23,70],[0,14,5,4,10,22,24,16,28],[90,91,92,93,94,95]),([23,71],[14,4,5],[96,97,98,55,77]),([23,78],[14,5,10,22,24,16,28],[99,100,101,102]),([23,79],[14,0,5,1],[]),([23,86],[0,28,22,10,14,24,23],[103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118]),([23,87],[28,22,23],[119,120,121,122,103,56,78,123]),([23,94],[28,22,6,0,10,14,24,23],[103,124,125,126,127,128,129,130,131]),([23,95],[28,22,6,23,1],[103,132,133]),([23,102],[0,24,26,10,16,22,27],[134,135,136,137,138,139,140,141,142]),([23,103],[24,16,26],[143,144,145,146,147,57,79,148]),([23,110],[24,26,10,14,16,22,27],[149,150,151,152]),([23,111],[24,26,1],[153]),([23,296],[0,10,3,14,5,22,24,28],[22,154,155,156,58,80,123,133,148,153,157,158,159]),([23,310],[10,0,6,2,8,28],[160,161,162,163,164,165]),([23,311],[10,6,2,0,3],[]),([23,318],[0,10,7,1,8,5,28],[166,167,168,169]),([23,327],[0,14,6,4,5],[44,66]),([23,342],[28,0,6,22,23],[170,171,172,173,174,132,175,176,177,59,81,141,151,178,179,180,181]),([23,343],[28,22,6,23,0],[182,120,130,45,67]),([23,350],[0,22,6,1,3,5,23],[183,184,142,152]),([23,359],[0,24,6,16,26],[185,144,186,187,46,68]),([23,566],[6,10,2,1,3,28],[188,167,178,189,190]),([23,574],[10,6,0,3,28],[191,192,162,179,193,194]),([23,575],[6,10,0,7,28,3,8],[195]),([23,582],[6,14,4,1,16,8,5,28],[196,180,197]),([23,590],[14,6,0,5,16,28],[198,199,60,82,163,181,200])]
set_option maxRecDepth 100000 in
theorem v137_8_0 : ∀ e ∈ k137_8_0, ¬ Live516.live basicOps goal 8 (wsOf c137.2 e).toFinset := level_sound hR137 8 k137_8_0 (D137_7.map (wsOf c137.2)) (map_dead w137_7) (by decide +kernel)
def k137_8_1 : List Entry := [([23,591],[6,14,0,28,5],[96,201,202,47,69]),([23,607],[6,22,0,23],[119,203,131,175,48,70]),([23,623],[6,24,0,28,26],[143,204,205,49,71]),([23,637],[6,28,0,23,10,8,1,14,24,27],[206,195,202,50,72,94,101]),([23,847],[10,3,8,14,5],[207,208]),([23,863],[10,3,8,28,23],[209,210,118,176]),([23,879],[10,3,24,26],[211,212]),([23,1119],[14,5,16,28,23],[213,214,215,177,51,73]),([23,1391],[24,26,28,23],[216,217,52,74,157]),([23,1397],[28,20,22,6,0,10,14,21],[218,219,42,53,61,75,83,88,95,102,158,164,168,189,193,197,200]),([23,1661],[24,28,23,14,6,0,10,16],[220,187,43,54,62,76,84,89,159,165,169,190,194]),([27,60],[0,6,14,2,3,5,24,22,28],[155,221,222,223]),([27,62],[0,6,14,2,3,28],[156,224,225]),([27,72],[0,6,10,14,3,24,16,28],[226]),([27,76],[0,6,10,3,4,5,24,22,28],[227,228,229]),([27,78],[0,6,10,14,3,4,5,28,16],[230]),([27,88],[0,6,10,3,14,5,24,22,23],[]),([27,92],[0,6,10,3,14,5,24,28],[231,232,233,234]),([27,94],[0,6,10,3,14,5,24,28,23],[235,236,237,238]),([27,104],[0,6,10,24,14,3,5,28],[239]),([27,108],[0,6,10,3,14,5,22,26,28],[240,241,242]),([27,110],[0,6,10,24,3,14,5,22,26,28,21],[243,244,245]),([27,124],[0,6,10,28,3,14,5,22,23],[246]),([27,1391],[0,26,28,23,24],[247,237,221,227,157]),([27,1397],[0,28,22,6,14,24,21],[248,249,238,222,224,226,228,230,239,242,158]),([27,1661],[0,28,23,6,24,14,16],[250,245,223,225,229,234,159]),([31,54],[0,6,3,10,14,2,28,8],[251,252]),([31,70],[0,6,5,14,10,3,4,28,16],[253,254]),([31,86],[0,6,22,10,3,14,5,24,23],[2,255,256,257]),([31,102],[0,6,26,24,10,3,16,22,27],[258,259,260,261]),([31,310],[0,2,6,3,8,28],[262,263]),([31,342],[0,6,3,28,23,5],[264,265,6,261]),([31,607],[0,22,23,6],[2,266,257,265]),([31,623],[0,24,26,28,6],[267,268]),([31,637],[0,28,23,6,10,8,14,24,27],[269,253]),([31,1391],[0,26,28,23],[270,23]),([31,1397],[0,28,9,22,10,14,24,21],[271,272,7,251,254,24,262]),([31,1661],[0,28,23,24,14,10,16,6],[273,260,8,252,25,263]),([39,50],[6,10,3,14,22,24,28],[274,275,276,277,278,279]),([39,58],[6,10,0,14,22,24,28,2,8],[280,281,282,283,284,285,286,287,288,289,290,160,291,292,293,294,295]),([39,62],[10,2,3,14,8,22,28],[296,297,298,299]),([39,70],[0,10,2,3,8,22,24,16,28],[300,301]),([39,78],[10,2,14,8,22,24,16,28,5],[302,303,304,305]),([39,86],[0,10,2,3,8,14,24,28,23],[306,307,308,309]),([39,94],[10,2,3,8,14,24,28,23],[310,311,312,161,313,314]),([39,102],[0,10,2,3,8,16,22,28,21],[315,316]),([39,110],[10,2,24,8,14,16,22,28,27],[317,318]),([39,327],[0,10,14,3,2],[]),([39,343],[0,10,3,28,23,2],[]),([39,359],[0,10,24,3,16,2],[319,320])]
set_option maxRecDepth 100000 in
theorem v137_8_1 : ∀ e ∈ k137_8_1, ¬ Live516.live basicOps goal 8 (wsOf c137.2 e).toFinset := level_sound hR137 8 k137_8_1 (D137_7.map (wsOf c137.2)) (map_dead w137_7) (by decide +kernel)
def k137_8_2 : List Entry := [([39,574],[10,6,3,8,28],[280,321,322,291,162,313,323,324]),([39,590],[10,14,0,3,8,5,16,28],[325,314,326]),([39,847],[10,8,5],[327,163]),([39,863],[10,8,28,23],[328,329]),([39,879],[10,8,26,28],[330,331,292,296]),([39,893],[10,28,8,23,14,24,27],[332,293,297,304]),([39,1119],[10,5,16,28,23],[333,334,335]),([39,1391],[10,26,28,23],[336,337]),([39,1397],[10,28,20,22,0,14,21],[338,339,278,42,294,298,301,305,164,262,323,326]),([39,1661],[10,28,23,24,14,0,16],[340,320,279,43,295,299,165,263,324]),([47,50],[0,6,10,14,5,22,24,28],[341,342,343,344,345]),([47,54],[0,10,1,14,5,22,8,24,28],[1,346,347,348,349,350]),([47,70],[0,10,5,4,28,16],[351,352,353,354]),([47,86],[0,10,8,14,5,24,28,23],[346,355,356,357,358,166]),([47,102],[0,10,8,26,16,22,27],[359,360,361,362,363]),([47,570],[0,6,28],[1,364,365,348,167,351,366,367]),([47,606],[0,10,22,3,8,23],[368,352,363]),([47,863],[0,10,8,28,23],[369,346,358]),([47,879],[0,26,10,8,28,24],[370,371]),([47,893],[0,28,23,6,8,14,24,27,10],[372,353]),([47,1391],[0,26,28,23,10],[373]),([47,1397],[0,28,20,22,10,14,21],[374,375,344,349,354,168,366]),([47,1661],[0,28,23,24,14,10,16],[376,362,345,350,169,367]),([55,50],[6,14,5,10,22,16,28],[377,378,379,380,381]),([55,58],[6,14,0,22,24,16,28,4],[382,383,384,385,386,387]),([55,62],[14,4,5,10,22,24,16,28],[388,389,390,391,392]),([55,78],[10,3,22,24,16,28],[393,394,395,396,397,398]),([55,86],[0,14,4,5,10,16,28,23],[399,400,401,402]),([55,94],[14,4,5,10,24,16,28,23],[403,404,405,406,407]),([55,343],[0,14,5,28,23,4],[]),([55,574],[14,6,5,16,28],[382,408,409,386,410,396,406,411]),([55,590],[10,14,0,3,5,24,16,28],[412,413,391,407,414,415]),([55,839],[10,6,14,28,3],[416,417,418,419]),([55,847],[10,3],[420,421]),([55,855],[14,6,28,23],[422,423,424]),([55,863],[14,28,23],[425,426,114,427]),([55,893],[14,28,23,16,6,0,10],[94,390,410,428,397,414]),([55,1119],[10,3,28,23],[429,430]),([55,1397],[14,28,20,22,16,0,10],[431,381,95,387,392,301,398,411,415]),([63,50],[0,6,14,10,3,22,24,16,28],[432,433,434]),([63,54],[0,14,10,3,1,22,24,16,28],[435,436,437,438,439,440,441]),([63,70],[0,10,14,3,2,24,28,16],[442,443,444]),([63,86],[0,14,10,3,24,16,28,23],[445,437,446,447,448]),([63,606],[0,14,22,5,16,23],[449,440,442]),([63,855],[0,6,28,23,14],[450]),([63,863],[0,28,23,14],[451,437,448]),([63,893],[0,28,23,16,6,10],[439,443]),([63,1397],[0,28,20,22,16,10],[452,434,441,444]),([71,50],[6,28,22,10,14,24,23],[453,454,455,456]),([71,51],[6,28,23],[2,457,17,458])]
set_option maxRecDepth 100000 in
theorem v137_8_2 : ∀ e ∈ k137_8_2, ¬ Live516.live basicOps goal 8 (wsOf c137.2 e).toFinset := level_sound hR137 8 k137_8_2 (D137_7.map (wsOf c137.2)) (map_dead w137_7) (by decide +kernel)
def k137_8_3 : List Entry := [([71,55],[28,6,23],[459,130,460,461,462,106]),([71,58],[6,28,22,0,14,24,23,10],[463,464,465,466,467,468,469,470,471,170,182,472]),([71,59],[0,6,28,22,23],[107,473,474,475,476,477,478,479,462,171,480]),([71,62],[28,22,0,10,14,24,23],[106,2,481,482,483,484,485,486,26,120,487]),([71,63],[28,6,22,0,23],[458,106,172,488]),([71,71],[10,2,28,23,3],[489,490,491]),([71,78],[10,3,14,24,28,22,23],[492,493,494,495,174,496]),([71,79],[10,0,3,28,23],[]),([71,87],[14,4,16,28,23,5],[497,498]),([71,94],[14,5,10,24,16,28,22,23],[499,500,501]),([71,95],[14,0,5,28,23],[]),([71,102],[0,24,21,20,10,16,28,23],[502,503,504,505]),([71,103],[24,20,16,28,23,21],[506,507]),([71,110],[24,21,10,14,16,28,23],[508,509,510]),([71,111],[24,20,28,21,23],[]),([71,358],[24,0,20,22,21,16,23],[511,512,513]),([71,359],[24,20,22,16,0,21,23],[506,514]),([71,366],[0,24,20,28,5,23,3],[515,516]),([71,574],[28,22,6,0,23],[463,517,474,518,519,520,521,522,523,524,472,480,488,175,265,525,526,527,496,512,516]),([71,590],[10,3,22,23],[528,529,530,118,487,176,513]),([71,606],[14,5,22,16,23],[531,532,533,177]),([71,839],[10,6,22,23,3],[534,535,536,473,537,178]),([71,847],[10,3,28,23],[538,539,179]),([71,855],[14,6,22,16,23],[540,541,542,543,544,545,180]),([71,863],[14,5,28,23],[546,547,181]),([71,871],[24,6,22,16,23],[548,549,550,551,552,553,525]),([71,879],[24,21,28,23],[554,555,526]),([71,1119],[10,3,14,5,28,23],[556,557,558,559]),([71,1135],[10,3,21,28,23],[560,561]),([79,50],[0,6,22,10,3,14,5,24,23],[562]),([79,54],[0,22,10,3,14,5,24,23],[563,564]),([79,70],[0,10,3,2,28,22,23],[184]),([79,86],[0,14,5,4,16,28,22,23],[]),([79,96],[0,24,20,22,10,3,14,5,23],[]),([79,100],[0,21,10,3,14,5,28,22,23],[565,566]),([79,102],[0,24,21,10,3,14,5,28,23],[567,568]),([79,358],[0,20,21,28,24,16,23],[569]),([79,871],[0,6,16,28,23,21],[570,571,572]),([79,879],[0,21,24,28,23],[573]),([87,58],[6,24,0,26,14,16,21,27],[574,575,185]),([87,62],[24,17,0,10,16,21,28,27],[576,577,578,579,27,144,511,569]),([87,78],[10,3,14,16,21,28,26,27],[580,581,582]),([87,92],[24,0,17,5,10,21,28,27],[28,186,319,514,583,584,585,586,587]),([87,110],[24,17,0,22,21,10,16,23],[588,579,589,506]),([87,636],[28,0,17,21,24,16,10],[590,29,187,320,591,592]),([87,839],[10,6,26,24,27,3,16],[593,583,591]),([87,847],[10,26,3,16],[594,595,596,584,592]),([87,871],[24,6,21,28,23,16],[597,585]),([87,879],[24,21,28,23,16],[598,579,512,586]),([87,1135],[10,21,3,24,28,23,16],[599,513,587])]
set_option maxRecDepth 100000 in
theorem v137_8_3 : ∀ e ∈ k137_8_3, ¬ Live516.live basicOps goal 8 (wsOf c137.2 e).toFinset := level_sound hR137 8 k137_8_3 (D137_7.map (wsOf c137.2)) (map_dead w137_7) (by decide +kernel)
def k137_8_4 : List Entry := [([95,50],[0,6,24,10,3,14,5,21,28,27],[600]),([95,54],[0,24,10,3,14,5,21,28,27],[601,602,515]),([95,70],[0,10,24,3,2,28,27],[]),([95,102],[0,24,21,10,3,14,5,28,23],[603,601,604]),([95,871],[0,6,28,23,24],[605]),([95,879],[0,28,23,24],[606,601,604,516]),([295,58],[6,10,1,14,3,22,24,28],[1,416,534,607,364,536,608,609]),([295,62],[6,0,10,14,22,24,28],[610,611,612,473,613,614]),([295,78],[6,10,3,22,24,16,28],[615,416,616,617,418,618,188,619]),([295,94],[6,10,3,14,24,28,23],[620,534,621,617,622,623,537,365,624]),([295,110],[6,10,3,26,14,16,22,28,21],[625,626,627]),([295,124],[6,10,23,14,3,24,27],[628,419]),([295,590],[6,10,14,3,24,16,28],[629,630,624,631]),([295,1119],[6,16,28,23,10],[632,617,633,618,630]),([295,1391],[6,26,28,23,24,10],[634]),([295,1397],[6,28,22,10,14,24,21],[635,636,608,613,619,189,366,631]),([295,1661],[6,28,23,24,14,10,16],[637,591,609,614,190,367]),([303,50],[10,3,14,7,28],[595,638,639]),([303,54],[0,10,6,14,22,24,28,7,3],[280,640,641,642,643,644,645,646,647,648,649,191,321,596,650,651]),([303,62],[10,0,8,14,22,24,28],[652,653,654,655,656]),([303,70],[6,10,3,7,22,24,16,28],[657,658,192,322,659,660]),([303,78],[10,3,14,8,22,24,16,28],[661,662,663,664,665]),([303,86],[6,10,3,7,14,24,28,23],[666,667,668]),([303,94],[10,3,7,8,14,24,28,23],[669,670]),([303,102],[6,10,3,7,16,22,28,21],[671,672,673,674]),([303,110],[10,3,24,8,14,16,22,28,21],[675]),([303,335],[6,10,14,8,7],[]),([303,351],[6,10,8,28,23,7],[]),([303,367],[6,10,24,8,28,7],[676]),([303,381],[6,28,10,8,22,23,7],[677,195]),([303,606],[10,22,6,3,8,23],[678,659,674]),([303,1119],[10,16,28,23],[679,680,681,682,683,664]),([303,1391],[10,26,28,23],[684,685]),([303,1397],[10,28,9,22,14,24,21],[686,687,638,650,42,655,660,665,30,193,323]),([303,1661],[10,28,23,24,14,6,16],[688,592,639,651,43,656,31,194,324]),([311,58],[6,14,10,8,22,5,24,16,28],[540,542,689]),([311,62],[6,0,14,10,8,22,24,16,28],[690,543,691]),([311,78],[6,10,14,7,8,28,16],[196,692]),([311,94],[6,14,5,10,8,24,16,28,23],[693,540,544]),([311,108],[6,14,19,17,10,8,22,5,28],[545,694]),([311,124],[6,14,23,16,10,8],[]),([311,1397],[6,28,22,16,10],[695,689,691,692,694,197]),([319,50],[14,5,10,22,24,16,28],[696,546,96,697,698]),([319,54],[0,14,6,22,16,28,10,5],[382,699,700,701,702,703,704,705,198,201,408,706,707]),([319,62],[14,0,10,22,24,16,28,5],[708,709,710,711,712]),([319,70],[6,10,5,14,8,22,24,16,28],[713,714,199,409,715,716]),([319,71],[10,6,5,14],[]),([319,86],[6,14,5,10,24,16,28,23],[546,717,718,719,720,721]),([319,87],[14,22,6,23,5],[]),([319,94],[14,5,22,10,16,23],[722,723,724])]
set_option maxRecDepth 100000 in
theorem v137_8_4 : ∀ e ∈ k137_8_4, ¬ Live516.live basicOps goal 8 (wsOf c137.2 e).toFinset := level_sound hR137 8 k137_8_4 (D137_7.map (wsOf c137.2)) (map_dead w137_7) (by decide +kernel)
def k137_8_5 : List Entry := [([319,351],[6,14,22,23],[725,720]),([319,381],[6,28,14,23,16,10,8],[202,697,706,94,711,410]),([319,590],[10,14,6,5,24,8,16,28],[726,727,721,728]),([319,606],[14,22,6,5,16,23],[729,730,715]),([319,1119],[10,8,28,23],[731,732,733,734]),([319,1397],[14,28,9,22,16,10],[735,698,707,95,712,716,665,32,200,411,728]),([327,58],[6,22,10,8,1,14,24,23],[736,737,422,738,739,740]),([327,62],[6,22,10,8,14,0,24,23],[741,742]),([327,78],[6,10,8,7,28,22,23],[]),([327,94],[6,14,22,10,8,24,16],[743,744,422,745,424]),([327,110],[6,24,21,10,8,14,16,28],[746,747]),([327,366],[6,20,28,21,24,16],[]),([335,50],[28,6,22,10,14,24,23],[104,2,748,749,425,750,751,752,119,266,753]),([335,51],[28,0,22,6,9,23],[104,754,518]),([335,54],[0,28,6,22,14,24,23],[463,755,756,757,203,519]),([335,55],[0,28,22,9,23],[105,517,758,520]),([335,59],[0,28,23],[759,131,760,761,104,758]),([335,62],[28,0,22,10,14,24,23],[762,763,764,765,766,767]),([335,63],[28,23,0],[2,768,257,769,770,754]),([335,70],[6,10,8,14,24,28,22,23],[771,772,773,774,521]),([335,71],[10,6,8,28,9,23],[]),([335,79],[10,7,28,23,8],[775]),([335,86],[6,14,22,10,24,16,23],[776,425,777,778,779,780,781,725,523]),([335,87],[14,28,9,22,23],[776]),([335,95],[14,16,28,23],[782,720,783,776]),([335,102],[6,24,21,10,14,16,28,23],[784,785,786]),([335,103],[24,20,28,9,21,23],[]),([335,110],[24,21,20,10,14,16,28,23],[787,788,789]),([335,111],[24,20,28,23,21],[790]),([335,358],[6,24,20,23,16,28,8],[525]),([335,366],[24,6,20,22,21,16,23],[526,791]),([335,367],[6,24,20,22,21,23],[790]),([335,590],[10,8,22,23],[792,793,753,118,791]),([335,1119],[10,8,14,28,23],[794,795,796]),([335,1135],[10,8,21,28,23],[797,798]),([343,58],[6,24,10,8,14,16,21,28],[548,799,550,571]),([343,62],[6,24,10,8,14,16,21,0,28],[800,551]),([343,78],[6,10,24,7,8,28,21],[]),([343,92],[6,14,24,17,19,10,8,21,28],[553,572]),([343,110],[6,24,21,10,8,14,16,28],[548,801,552]),([343,124],[6,24,23,10,8,14,16],[]),([351,50],[24,17,0,10,16,21,28,27],[802,803,554,804,143,267]),([351,54],[0,24,6,26,14,16,21,27],[805,806,204]),([351,70],[6,10,8,14,16,21,28,27],[807,808,809]),([351,102],[6,24,17,21,10,16,28,23],[554,810,811,790]),([351,124],[24,17,25,21,6,10],[812,205,268,676,331,371]),([351,1135],[10,21,8,28,23],[813,791]),([365,102],[6,24,23,28,17,26,10,16],[206,269,677,332,372]),([365,847],[10,14,23,6,8,24,16],[814,815,414]),([575,50],[10,3,8,11,5,28,16],[558,814,816])]
set_option maxRecDepth 100000 in
theorem v137_8_5 : ∀ e ∈ k137_8_5, ¬ Live516.live basicOps goal 8 (wsOf c137.2 e).toFinset := level_sound hR137 8 k137_8_5 (D137_7.map (wsOf c137.2)) (map_dead w137_7) (by decide +kernel)
def k137_8_6 : List Entry := [([575,54],[0,10,14,22,16,28,8,3,5],[817,818,819,820,821,822,823,325,412,559,815,824]),([575,62],[10,0,14,8,22,24,16,28,5],[825,826]),([575,66],[6,10,14,22,24,16,28],[827,828,829,726,830]),([575,70],[6,10,3,14,11,8,24,28,16],[629,413,831,832]),([575,74],[6,10,14,3,22,16,28],[833,834,835,836]),([575,86],[10,3,14,11,8,24,16,28,23],[837,838,727]),([575,94],[10,3,11,14,8,16,28,23],[839]),([575,350],[10,14,3,8,16,22],[]),([575,606],[10,14,5,16,22,23],[840,831,630]),([575,1397],[10,28,20,22,16],[841,816,824,301,826,830,832,836,665,326,631,415,728]),([591,50],[10,3,22,8,14,24,23],[209,429,842,368,793]),([591,54],[0,10,22,14,24,23],[843,844,845,528]),([591,62],[10,0,22,8,14,24,23],[846,847,848,849]),([591,66],[6,10,22,14,24,23,3,8],[850,851,852,853,854,855,856,857,678,792,733]),([591,70],[6,10,3,8,14,24,28,23],[209,732,858,734,529]),([591,74],[6,10,22,3,14,24,23],[859,860]),([591,86],[10,3,14,8,24,16,28,22,23],[429,861,732,862,530]),([591,87],[10,14,3,28,23],[]),([591,102],[10,3,24,21,8,14,16,28,23],[863,864]),([591,103],[10,24,3,28,21,23],[]),([591,110],[10,3,24,21,8,14,16,28,23],[]),([591,366],[10,24,3,22,8,16],[]),([607,50],[10,3,8,13,26,27],[]),([607,54],[0,10,24,14,16,21,28,27,3],[865,866]),([607,66],[6,10,24,14,16,21,28,27],[867,868]),([607,70],[6,10,3,13,8,26,21],[]),([607,102],[10,3,24,13,21,16,28,23],[]),([847,50],[14,5,22,10,24,16,23],[869,213,333,449]),([847,54],[0,14,22,10,24,16,23],[870,871,872,531]),([847,62],[14,0,22,10,16,23],[873,874,875,876]),([847,66],[6,14,22,5,10,24,16,23],[877,878,729]),([847,67],[6,14,5,28,23,16,15],[722]),([847,70],[6,14,5,10,24,16,28,23],[213,879,680,880,840,532]),([847,71],[14,6,5,28,15],[]),([847,74],[6,14,22,5,10,16,23],[881,882]),([847,86],[10,5,14,24,16,28,22,23],[333,883,884,680,885,886,730,533]),([847,87],[10,5,15,14],[]),([847,100],[14,24,15,19,22,5,10,23],[34,215,335,633,683]),([847,101],[14,24,5,28,15,23],[]),([1119,50],[24,17,0,20,10,16,28,26,23],[887,888,889]),([1119,54],[0,24,20,10,14,16,28,23],[890,891,892]),([1119,66],[6,24,20,22,10,14,16,23,26],[893,894,895]),([1119,70],[6,24,17,20,10,16,28,23],[896,897,898]),([1119,86],[10,17,24,20,16,28,26,23],[899,900,901,902]),([1125,62],[28,20,6,9,10,14,21,22],[903,904,905,906,218,271,686,735,338,374,431,452,841]),([1125,110],[24,20,21,10,14,16],[37,219,249,272,339,375,636,687]),([1389,54],[6,24,17,25,21,10,16,23],[220,273,688,590,340,376])]
set_option maxRecDepth 100000 in
theorem v137_8_6 : ∀ e ∈ k137_8_6, ¬ Live516.live basicOps goal 8 (wsOf c137.2 e).toFinset := level_sound hR137 8 k137_8_6 (D137_7.map (wsOf c137.2)) (map_dead w137_7) (by decide +kernel)
def D137_8 : List Entry := k137_8_0 ++ (k137_8_1 ++ (k137_8_2 ++ (k137_8_3 ++ (k137_8_4 ++ (k137_8_5 ++ (k137_8_6))))))
theorem w137_8 : ∀ e ∈ D137_8, ¬ Live516.live basicOps goal 8 (wsOf c137.2 e).toFinset := (app_dead v137_8_0 (app_dead v137_8_1 (app_dead v137_8_2 (app_dead v137_8_3 (app_dead v137_8_4 (app_dead v137_8_5 v137_8_6))))))
def k137_9_0 : List Entry := [([19],[6,28,10,14,22,24,0,8,16],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]),([23],[28,6,0,10,14,22,24,16],[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60]),([27],[0,28,6,14,22,24,10,3,5],[61,62,63,64,65,66,67,68,69,70,71,72,36,73,74,75]),([31],[28,0,10,14,22,24,6,3,5],[0,76,77,78,79,6,80,81,82,83,84,85,86,87]),([39],[10,0,3,2,14,22,24,28,8,16],[88,16,89,90,91,92,93,94,95,96,37,38,80,97,98,99,100,101,102,103,104,105,106,107,108,109]),([47],[10,0,14,22,24,28,5,8],[110,111,112,113,114,39,115,116,117,118,119,120,121,122]),([55],[14,0,5,4,10,22,24,16,28],[123,24,124,125,91,126,127,128,7,40,97,129,130,131,132,133,134,135,136,137,138]),([63],[14,0,10,22,24,16,28,3],[139,140,141,142,143,144,145,146,147]),([71],[28,22,0,10,14,24,23,16],[148,149,28,150,151,152,153,154,93,155,156,157,127,158,159,160,161,162,163,164,8,41,42,81,98,129,165,166,167,168,169,170,171,172,173,174,175,176,177,178]),([79],[28,0,22,10,14,24,23,3,5],[179,180,181,182,183,184,185,43,186,187,188]),([87],[24,0,26,10,16,22,27],[189,190,191,192,193,9,44,99,165,166,186,194,195,196,197,198,199]),([95],[24,0,10,14,16,22,28,3,27],[200,201,202,203,167,204,205]),([295],[6,10,14,22,24,28,3,16],[206,207,208,209,210,211,45,115,212,132,171,195,213,214,215,216]),([303],[10,6,3,14,7,22,24,28,16],[217,218,16,219,220,221,222,223,224,225,10,46,47,226,227,228,229,100,230,133,172,196,231,232,233,234]),([311],[6,14,10,22,16,28,8,5],[235,236,237,238,239,240,48,173,241]),([319],[14,6,5,10,22,24,16,28],[242,243,24,244,245,246,221,247,248,249,11,49,50,226,250,251,130,252,253,102,174,254,255]),([327],[6,28,22,10,14,24,23,8,16],[256,257,258,259,260,261,134,144,197,204]),([335],[28,22,6,10,14,24,23,16],[262,263,264,265,28,266,267,268,269,270,223,271,272,273,249,274,275,276,277,278,51,82,227,250,279,280,281,168,282,103,117,135,145,198,205,283,284]),([343],[6,24,10,16,22,28,8,21],[285,286,287,288,289,290,279,175,187]),([351],[24,6,26,10,14,16,22,28,27],[291,292,293,294,295,52,83,228,261,280,281,104,118,176,188,296]),([365],[28,23,6,10,14,24,27],[297,53,84,229,251,105,119,136,146,298]),([575],[10,14,3,8,22,11,24,16,28],[299,300,91,301,302,303,304,221,305,306,101,212,307,131,252,308,54,177,283,298,309]),([591],[10,22,3,8,14,24,23,16],[310,311,93,312,313,314,315,223,316,317,306,318,319,320,116,230,307,321,169,282,55,137,199,254,296]),([607],[10,24,3,26,14,16,22,8,27],[322,323,324,325,326,321,56,178,284]),([847],[14,22,5,10,16,23],[327,328,127,329,330,331,332,333,334,249,335,336,306,337,338,143,253,308,170,12,57,106,213,231]),([1119],[24,22,20,26,10,14,16,23],[339,340,341,342,343,13,58,73,85,107,120,214,232]),([1125],[28,20,22,10,14,21],[344,345,14,59,74,86,108,121,138,147,215,233,241,255,309]),([1389],[24,28,23,14,10,16],[346,194,15,60,75,87,109,122,216,234])]
set_option maxRecDepth 100000 in
theorem v137_9_0 : ∀ e ∈ k137_9_0, ¬ Live516.live basicOps goal 9 (wsOf c137.2 e).toFinset := level_sound hR137 9 k137_9_0 (D137_8.map (wsOf c137.2)) (map_dead w137_8) (by decide +kernel)
def D137_9 : List Entry := k137_9_0
theorem w137_9 : ∀ e ∈ D137_9, ¬ Live516.live basicOps goal 9 (wsOf c137.2 e).toFinset := v137_9_0
def k137_10_0 : List Entry := [([],[10,14,22,24,28,16],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])]
set_option maxRecDepth 100000 in
theorem v137_10_0 : ∀ e ∈ k137_10_0, ¬ Live516.live basicOps goal 10 (wsOf c137.2 e).toFinset := level_sound hR137 10 k137_10_0 (D137_9.map (wsOf c137.2)) (map_dead w137_9) (by decide +kernel)
def D137_10 : List Entry := k137_10_0
theorem w137_10 : ∀ e ∈ D137_10, ¬ Live516.live basicOps goal 10 (wsOf c137.2 e).toFinset := v137_10_0
theorem g137 : GoodC c137 := claim_sound2 D137_10 c137 w137_10 (by decide +kernel)
def c138 : Claim := (7, available 0xbdef77bdbbbc00000000000000000000000000 106 inputs)
def r138 : List RE := [(0xa82d720d90b400000000000000000000000000,106,0),(0x39ce6739333800000000000000000000000000,107,1)]
def d138 : List Entry := [([],[0,1],[])]
def e138 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g138 : GoodC c138 := claim_sound [c44,c131] (gcons g44 (gcons g131 gnil)) r138 d138 e138 c138 (by decide +kernel)
def c139 : Claim := (7, available 0xbf00000e73777a00000000000000005cefbd9bbf 0 inputs)
def r139 : List RE := [(0x8e00000a0350720000000000000000482d0c828e,1,0),(0xbb00000000775a00000000000000000007bc01bb,0,1)]
def d139 : List Entry := [([],[0,1],[])]
def e139 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g139 : GoodC c139 := claim_sound [c48,c103] (gcons g48 (gcons g103 gnil)) r139 d139 e139 c139 (by decide +kernel)
def c140 : Claim := (7, available 0x7bdec00000017bdbbbd0000000000000000000 76 inputs)
def r140 : List RE := [(0x681cc0000001505a8390000000000000000000,76,0),(0x5ad68000000139c99ac0000000000000000000,78,1)]
def d140 : List Entry := [([],[0,1],[])]
def e140 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g140 : GoodC c140 := claim_sound [c49,c108] (gcons g49 (gcons g108 gnil)) r140 d140 e140 c140 (by decide +kernel)
def c141 : Claim := (7, available 0xbf000000000000739bbbd0000000003adb37dfbf 0 inputs)
def r141 : List RE := [(0x8e000000000000501a839000000000281906868e,1,0),(0xb70000000000000003b9d000000000000003dfb7,0,1)]
def d141 : List Entry := [([],[0,1],[])]
def e141 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g141 : GoodC c141 := claim_sound [c50,c127] (gcons g50 (gcons g127 gnil)) r141 d141 e141 c141 (by decide +kernel)
def c142 : Claim := (7, available 0x7bdeef7b777a00000000000000000000000000 105 inputs)
def r142 : List RE := [(0x681cea0b507200000000000000000000000000,105,0),(0x39ce6739333800000000000000000000000000,107,1)]
def d142 : List Entry := [([],[0,1],[])]
def e142 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g142 : GoodC c142 := claim_sound [c51,c131] (gcons g51 (gcons g131 gnil)) r142 d142 e142 c142 (by decide +kernel)
def c143 : Claim := (9, available 0xbf7bdeef7b777b7bdbbbd0000000007effbfdfbf 0 inputs)
def r143 : List RE := [(0x8e681cea0b5073505a839000000000683d0e868e,1,0),(0xc0018c00b0062005803100000000000380c060c,2,1),(0x1d035ac15b056a0ad82b500000000006789c4e1d,0,2),(0xbb00000000775a00000000000000000007bc01bb,0,3),(0xb70000000000000003b9d000000000000003dfb7,0,4),(0xbf00000e73777a00000000000000005cefbd9bbf,0,5),(0x7bdec00000017bdbbbd0000000000000000000,76,6),(0xbf000000000000739bbbd0000000003adb37dfbf,0,7),(0x7bdeef7b777a00000000000000000000000000,105,8)]
def d143 : List Entry := [([],[0,2,3,4,6,8],[0,1,2,3,4])]
def e143 : List (List Entry) := [[([23],[0,2,3,4,6,8],[0,1,2,3,4,5,6,7,8,9]),([31],[0,2,3,4,6,8],[0,10,11,12,13]),([39],[2,0,3,4,6,8],[14,1,15,16,17,18,19,7,12,20]),([47],[2,0,3,4,6,8],[14,21,11,8,13]),([303],[0,2,1,3,4,6,8],[1,11,9,20])],[([23,45],[0],[0]),([23,54],[0],[1,2]),([23,56],[0,2,5,6,7,8,3,4],[0]),([23,57],[0],[1,0]),([23,60],[5,6,7,8],[]),([23,61],[2,0],[]),([23,62],[0],[]),([23,310],[0,2],[3]),([23,318],[0,2],[]),([23,574],[2,1],[3]),([31,54],[0,2],[]),([31,62],[0,5,6,7,8],[]),([31,310],[0,2],[]),([31,318],[0,2],[]),([39,45],[2],[4]),([39,56],[0,2,5,6,7,8,3,4],[4]),([39,57],[0,2],[2,4]),([39,60],[5,6,7,8],[]),([39,61],[0,2],[]),([39,62],[0,2],[]),([39,574],[0,1],[3]),([47,54],[0],[])],[([23,45,312],[],[]),([23,54,28],[],[]),([23,54,60],[],[]),([23,310,316],[0,2],[]),([39,45,312],[],[])]]
set_option maxRecDepth 100000 in
theorem g143 : GoodC c143 := claim_sound [c52,c29,c84,c103,c127,c139,c140,c141,c142] (gcons g52 (gcons g29 (gcons g84 (gcons g103 (gcons g127 (gcons g139 (gcons g140 (gcons g141 (gcons g142 gnil))))))))) r143 d143 e143 c143 (by decide +kernel)
def c144 : Claim := (9, available 0xff00001ef7fffe0000000bbbbbbbbeddeffdbbff 0 inputs)
def r144 : List RE := [(0xfb00000000ffde000000000bb00bae8007fc01fb,0,0)]
def d144 : List Entry := [([],[0],[])]
def e144 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g144 : GoodC c144 := claim_sound [c114] (gcons g114 gnil) r144 d144 e144 c144 (by decide +kernel)
def c145 : Claim := (6, available 0xff000000000000000000033333333c99cb75bbff 0 inputs)
def r145 : List RE := [(0xfb000000000000000000000330032c80037401fb,0,0)]
def d145 : List Entry := [([],[0],[])]
def e145 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g145 : GoodC c145 := claim_sound [c112] (gcons g112 gnil) r145 d145 e145 c145 (by decide +kernel)
def c146 : Claim := (6, available 0x1ef7fffe00000000000000000000000000 105 inputs)
def r146 : List RE := [(0xffde00000000000000000000000000,105,0)]
def d146 : List Entry := [([],[0],[])]
def e146 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g146 : GoodC c146 := claim_sound [c113] (gcons g113 gnil) r146 d146 e146 c146 (by decide +kernel)
def c147 : Claim := (5, available 0xb5addee0000000000000000000 77 inputs)
def r147 : List RE := [(0x5dce0000000000000000000,77,0)]
def d147 : List Entry := [([],[0],[])]
def e147 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g147 : GoodC c147 := claim_sound [c97] (gcons g97 gnil) r147 d147 e147 c147 (by decide +kernel)
def c148 : Claim := (6, available 0xf7bffff0000000000000000000 76 inputs)
def r148 : List RE := [(0xb5addee0000000000000000000,77,0)]
def d148 : List Entry := [([],[0],[])]
def e148 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g148 : GoodC c148 := claim_sound [c147] (gcons g147 gnil) r148 d148 e148 c148 (by decide +kernel)
def c149 : Claim := (6, available 0xffffc000000000000000000000000000000000 134 inputs)
def r149 : List RE := [(0xdef78000000000000000000000000000000000,135,0)]
def d149 : List Entry := [([],[0],[])]
def e149 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g149 : GoodC c149 := claim_sound [c116] (gcons g116 gnil) r149 d149 e149 c149 (by decide +kernel)
def c150 : Claim := (9, available 0xff000000000000f7bffff77777777dbbdb77ffff 0 inputs)
def r150 : List RE := [(0xf70000000000000007fdf00007775d800003fff7,0,0)]
def d150 : List Entry := [([],[0],[])]
def e150 : List (List Entry) := []
set_option maxRecDepth 100000 in
theorem g150 : GoodC c150 := claim_sound [c136] (gcons g136 gnil) r150 d150 e150 c150 (by decide +kernel)
def c151 : Claim := (12, inputs)
def r151 : List RE := [(0x60f781fdeeee07ef77703eeeeeee03f7b6eb7560,5,0),(0xe001f80ec007c076003ccccccc0360340a0400,10,1),(0x400701c1ce0c060e706030e0e0e0038730c86440,6,2),(0x60d6818000ee07ad6550200ee00e038006e80160,5,3),(0x3dee00000000000ee00ee00077b0037400,10,4),(0x60b58175acaa0400077030000eee038000037560,5,5),(0x1ef70000eeee0000077b6e80000,19,6),(0x8ee83dfa0fd0f7d07e87bdddddddfb683d0e868e,1,7),(0xc0039c00f00e600780730d0d0d0f300380c060c,2,8),(0x8ac8358000d0d7906c86a00dd00deb00050c008a,1,9),(0x86a82d720d90b4000685b0000ddddb0000028686,1,10),(0x8e681cea0b5073505a839000000000683d0e868e,1,11),(0x8e00001a07d0f600000009999999ba482d0c828e,1,12),(0xe83dc0000001d07e87b0000000000000000000,76,13),(0x8e000000000000d03e87b555555579281906868e,1,14),(0xe83dfa0fd0f600000000000000000000000000,105,15),(0x5d077bc1df0dee0ef86f70f0f0f0f78778dc6e5d,0,16),(0x1d035ac15b056a0ad82b500000000006789c4e1d,0,17),(0x5d000000d70dee00000000b0b0b0b68568dc2a5d,0,18),(0x5d00000000000006b86f70707070758358546e5d,0,19),(0xfbdef78000ffdfbdeddee00ff00fef8007fc01fb,0,20),(0xdef780000001bdeddee0000000000000000000,77,21),(0xf7bdef77bdbbbc0007fdf0000fffdf800003fff7,0,22),(0xbdef77bdbbbc00000000000000000000000000,106,23),(0xbf7bdeef7b777b7bdbbbd0000000007effbfdfbf,0,24),(0xbf00000e73777a00000000000000005cefbd9bbf,0,25),(0x7bdec00000017bdbbbd0000000000000000000,76,26),(0xbf000000000000739bbbd0000000003adb37dfbf,0,27),(0x7bdeef7b777a00000000000000000000000000,105,28),(0xff00001ef7fffe0000000bbbbbbbbeddeffdbbff,0,29),(0xff000000000000000000033333333c99cb75bbff,0,30),(0x1ef7fffe00000000000000000000000000,105,31),(0xf7bffff0000000000000000000,76,32),(0xffffc000000000000000000000000000000000,134,33),(0xff000000000000f7bffff77777777dbbdb77ffff,0,34)]
def R151 : List RR := r151.map (resolve [c7,c0,c6,c16,c17,c23,c24,c35,c34,c40,c45,c52,c53,c54,c55,c56,c88,c84,c85,c87,c118,c119,c137,c138,c143,c139,c140,c141,c142,c144,c145,c146,c148,c149,c150] c151.2)
theorem hR151 : ∀ y ∈ R151, RInv c151.2.toFinset y := res_inv [c7,c0,c6,c16,c17,c23,c24,c35,c34,c40,c45,c52,c53,c54,c55,c56,c88,c84,c85,c87,c118,c119,c137,c138,c143,c139,c140,c141,c142,c144,c145,c146,c148,c149,c150] (gcons g7 (gcons g0 (gcons g6 (gcons g16 (gcons g17 (gcons g23 (gcons g24 (gcons g35 (gcons g34 (gcons g40 (gcons g45 (gcons g52 (gcons g53 (gcons g54 (gcons g55 (gcons g56 (gcons g88 (gcons g84 (gcons g85 (gcons g87 (gcons g118 (gcons g119 (gcons g137 (gcons g138 (gcons g143 (gcons g139 (gcons g140 (gcons g141 (gcons g142 (gcons g144 (gcons g145 (gcons g146 (gcons g148 (gcons g149 (gcons g150 gnil))))))))))))))))))))))))))))))))))) r151 c151.2
def k151_6_0 : List Entry := [([19,300,20,29,87,76],[],[]),([19,300,20,29,103,92],[],[]),([19,300,20,29,327,56],[],[]),([19,300,20,29,343,76],[],[]),([19,300,20,29,359,92],[],[]),([19,300,20,1391,50,76],[],[]),([19,300,21,45,614,76],[],[]),([19,300,21,45,630,92],[],[]),([19,301,36,45,614,76],[],[]),([19,301,36,45,630,92],[],[]),([23,61,119,108,1112,44],[],[]),([23,61,119,108,1112,76],[],[]),([23,61,135,124,1112,44],[],[]),([23,61,135,124,1112,76],[],[]),([23,61,359,56,840,28],[],[]),([23,61,359,56,840,44],[],[]),([23,61,375,108,1112,44],[],[]),([23,61,375,108,1112,76],[],[]),([23,61,375,1112,76,20],[],[]),([23,61,391,124,1112,44],[],[]),([23,61,391,124,1112,76],[],[]),([23,61,391,1112,76,20],[],[]),([23,61,568,28,87,76],[],[]),([23,61,568,28,103,92],[],[]),([23,61,568,44,87,76],[],[]),([23,61,568,44,103,92],[],[]),([23,61,569,44,358,76],[],[]),([23,61,569,44,374,92],[],[]),([23,61,569,60,358,76],[],[]),([23,61,569,60,374,92],[],[]),([23,103,840,44,61,36],[],[]),([23,119,92,57,72,28],[],[]),([23,119,108,840,44,61],[],[]),([23,119,840,44,61,36],[],[]),([23,135,92,57,72,28],[],[]),([23,135,124,840,44,61],[],[]),([23,135,840,44,61,36],[],[]),([23,296,30,45,358,76],[],[]),([23,296,30,45,374,92],[],[]),([23,296,30,1663,64,76],[],[]),([23,296,44,1391,66,76],[],[]),([87,59,108,77,68,60],[],[]),([87,59,124,77,68,60],[],[])]
set_option maxRecDepth 100000 in
theorem v151_6_0 : ∀ e ∈ k151_6_0, ¬ Live516.live basicOps goal 6 (wsOf c151.2 e).toFinset := level_sound hR151 6 k151_6_0 [] nil_dead (by decide +kernel)
def D151_6 : List Entry := k151_6_0
theorem w151_6 : ∀ e ∈ D151_6, ¬ Live516.live basicOps goal 6 (wsOf c151.2 e).toFinset := v151_6_0
def k151_7_0 : List Entry := [([19,26,60,103,92],[],[]),([19,26,60,119,108],[],[]),([19,26,60,359,92],[],[]),([19,26,60,375,108],[],[]),([19,26,61,358,40],[],[]),([19,26,61,374,92],[],[]),([19,26,61,390,108],[],[]),([19,26,102,29,316],[],[]),([19,26,1935,48,92],[],[]),([19,300,20,29,71],[7,24],[]),([19,300,20,29,87],[7,20,29],[0]),([19,300,20,29,103],[7,22,34],[1]),([19,300,20,29,327],[7,24],[2]),([19,300,20,29,343],[7,18,20,29],[3]),([19,300,20,29,359],[7,19,22,34],[4]),([19,300,20,29,1119],[7,24],[]),([19,300,20,29,1135],[7,24],[]),([19,300,20,29,1391],[7,29],[]),([19,300,20,71,45],[24],[]),([19,300,20,71,60],[16],[]),([19,300,20,71,61],[16,24],[]),([19,300,20,87,60],[16],[]),([19,300,20,87,76],[16],[3]),([19,300,20,87,126],[7],[]),([19,300,20,95,118],[7],[]),([19,300,20,103,60],[16],[]),([19,300,20,103,92],[16],[4]),([19,300,20,103,126],[7],[]),([19,300,20,111,118],[7],[]),([19,300,20,1391,50],[7,16],[5]),([19,300,20,1391,54],[7],[]),([19,300,21,45,598],[0],[]),([19,300,21,45,614],[0,20],[6]),([19,300,21,45,630],[0,22],[7]),([19,300,21,87,76],[7],[]),([19,300,21,95,568],[0,24],[]),([19,300,21,103,76],[7],[]),([19,300,21,103,92],[7],[]),([19,300,21,119,76],[7],[]),([19,300,21,119,108],[7],[]),([19,300,21,358,76],[16],[6]),([19,300,21,358,126],[0],[]),([19,300,21,374,92],[16],[7]),([19,300,21,374,126],[0],[]),([19,300,21,1663,64],[],[]),([19,301,36,45,598],[0],[]),([19,301,36,45,614],[0,20],[8]),([19,301,36,45,630],[0,22],[9]),([19,301,36,87,76],[],[]),([19,301,36,95,568],[0,11],[])]
set_option maxRecDepth 100000 in
theorem v151_7_0 : ∀ e ∈ k151_7_0, ¬ Live516.live basicOps goal 7 (wsOf c151.2 e).toFinset := level_sound hR151 7 k151_7_0 (D151_6.map (wsOf c151.2)) (map_dead w151_6) (by decide +kernel)
def k151_7_1 : List Entry := [([19,301,36,103,76],[],[]),([19,301,36,103,92],[],[]),([19,301,36,119,76],[],[]),([19,301,36,119,108],[],[]),([19,301,36,358,76],[16],[8]),([19,301,36,358,126],[0],[]),([19,301,36,374,92],[16],[9]),([19,301,36,374,126],[0],[]),([19,301,36,1663,64],[],[]),([19,359,76,53,60],[],[]),([23,47,134,108,604],[],[]),([23,47,150,124,604],[],[]),([23,60,47,118,92],[],[]),([23,60,47,134,108],[],[]),([23,60,343,58,92],[],[]),([23,60,343,58,108],[],[]),([23,61,61,870,40],[1],[]),([23,61,103,1112,28],[7,24],[]),([23,61,103,1112,44],[7],[]),([23,61,103,1112,76],[7,24],[]),([23,61,119,108,1112],[],[10,11]),([23,61,119,1112,28],[7,29],[]),([23,61,119,1112,44],[7,20],[10]),([23,61,119,1112,76],[7,20,29],[11]),([23,61,135,124,1112],[],[12,13]),([23,61,135,1112,28],[7,34],[]),([23,61,135,1112,44],[7,22],[12]),([23,61,135,1112,76],[7,22,34],[13]),([23,61,358,41,332],[],[]),([23,61,358,42,92],[],[]),([23,61,358,42,108],[],[]),([23,61,359,56,840],[],[14,15]),([23,61,359,1112,28],[7,24],[]),([23,61,359,1112,44],[7],[15]),([23,61,359,1112,76],[7,24],[14]),([23,61,375,108,1112],[],[16,17]),([23,61,375,1112,28],[7,29],[]),([23,61,375,1112,44],[7,18,20],[16]),([23,61,375,1112,76],[7,20,29],[18,17]),([23,61,391,124,1112],[],[19,20]),([23,61,391,1112,28],[7,34],[]),([23,61,391,1112,44],[7,19,22],[19]),([23,61,391,1112,76],[7,22,34],[21,20]),([23,61,568,28,71],[7,24],[]),([23,61,568,28,87],[7,20,29],[22]),([23,61,568,28,103],[7,22,34],[23]),([23,61,568,28,1119],[7,24],[]),([23,61,568,28,1135],[7,24],[]),([23,61,568,28,1391],[7,29],[]),([23,61,568,44,71],[7,24],[15])]
set_option maxRecDepth 100000 in
theorem v151_7_1 : ∀ e ∈ k151_7_1, ¬ Live516.live basicOps goal 7 (wsOf c151.2 e).toFinset := level_sound hR151 7 k151_7_1 (D151_6.map (wsOf c151.2)) (map_dead w151_6) (by decide +kernel)
def k151_7_2 : List Entry := [([23,61,568,44,87],[7,18,20,29],[24]),([23,61,568,44,103],[7,19,22,34],[25]),([23,61,568,44,1119],[7,24],[]),([23,61,568,44,1135],[7,24],[]),([23,61,568,44,1391],[7,29],[]),([23,61,569,44,342],[0],[]),([23,61,569,44,358],[0,20],[26]),([23,61,569,44,374],[0,22],[27]),([23,61,569,60,342],[0],[]),([23,61,569,60,358],[0,20],[28]),([23,61,569,60,374],[0,22],[29]),([23,61,569,76,342],[],[]),([23,61,569,76,358],[20],[]),([23,61,569,92,342],[],[]),([23,61,569,92,374],[22],[]),([23,61,569,374,92],[],[26,28]),([23,61,569,390,108],[],[27,29]),([23,61,614,72,44],[7,1],[]),([23,61,614,73,60],[7],[]),([23,61,614,73,92],[],[]),([23,61,614,73,108],[],[]),([23,61,1935,64,56],[],[]),([23,102,29,317,332],[],[]),([23,102,77,45,36],[],[]),([23,103,45,840,44],[24],[]),([23,103,45,840,60],[11],[]),([23,103,45,840,76],[24],[]),([23,103,92,840,28],[8],[]),([23,103,92,840,30],[7],[]),([23,103,92,840,44],[16],[]),([23,103,92,840,46],[7,16],[]),([23,103,92,841,44],[7],[]),([23,103,92,841,60],[],[]),([23,103,92,841,92],[],[]),([23,103,92,841,108],[],[]),([23,103,93,1112,28],[8,24],[]),([23,103,93,1112,44],[7,24],[]),([23,103,93,1112,60],[7,16],[]),([23,103,840,28,45],[11],[]),([23,103,840,28,61],[7,24],[]),([23,103,840,44,45],[11],[]),([23,103,840,44,61],[7,24],[30]),([23,111,568,57,76],[24],[]),([23,111,568,57,92],[],[]),([23,111,568,57,108],[],[]),([23,111,570,328,60],[11],[]),([23,111,570,328,76],[0,24],[]),([23,111,570,328,92],[],[]),([23,111,570,328,108],[],[]),([23,111,840,44,37],[24],[])]
set_option maxRecDepth 100000 in
theorem v151_7_2 : ∀ e ∈ k151_7_2, ¬ Live516.live basicOps goal 7 (wsOf c151.2 e).toFinset := level_sound hR151 7 k151_7_2 (D151_6.map (wsOf c151.2)) (map_dead w151_6) (by decide +kernel)
def k151_7_3 : List Entry := [([23,119,56,56,28],[16,1],[]),([23,119,56,56,30],[0,1],[]),([23,119,56,56,60],[16,1],[]),([23,119,92,57,44],[],[]),([23,119,92,57,72],[],[31]),([23,119,92,57,332],[],[31]),([23,119,92,840,28],[2,29],[]),([23,119,92,840,30],[7],[]),([23,119,92,840,44],[16],[]),([23,119,92,840,46],[7,16],[]),([23,119,92,841,44],[7],[]),([23,119,92,841,60],[],[]),([23,119,92,841,92],[],[]),([23,119,92,841,108],[],[]),([23,119,108,840,44],[16],[32]),([23,119,108,840,46],[7,16],[17,16]),([23,119,108,840,76],[16],[17]),([23,119,108,841,44],[],[]),([23,119,108,841,60],[],[]),([23,119,108,841,92],[7],[]),([23,119,108,841,108],[],[]),([23,119,158,1112,60],[7],[]),([23,119,158,1112,92],[7],[]),([23,119,840,44,61],[7,29,20],[33,32]),([23,127,150,1112,60],[7],[]),([23,127,150,1112,92],[7],[]),([23,135,92,57,44],[],[]),([23,135,92,57,72],[],[34]),([23,135,92,57,332],[],[34]),([23,135,92,840,28],[2,34],[]),([23,135,92,840,30],[7],[]),([23,135,92,840,44],[16],[]),([23,135,92,840,46],[7,16],[]),([23,135,92,841,44],[7],[]),([23,135,92,841,60],[],[]),([23,135,92,841,92],[],[]),([23,135,92,841,108],[],[]),([23,135,124,840,44],[16],[35]),([23,135,124,840,46],[7,16],[20,19]),([23,135,124,840,76],[16],[20]),([23,135,124,841,44],[],[]),([23,135,124,841,60],[],[]),([23,135,124,841,92],[7],[]),([23,135,124,841,108],[],[]),([23,135,158,1112,60],[7],[]),([23,135,158,1112,92],[7],[]),([23,135,840,44,61],[7,34,22],[36,35]),([23,143,150,1112,60],[7],[]),([23,143,150,1112,92],[7],[]),([23,296,30,45,342],[7,24],[])]
set_option maxRecDepth 100000 in
theorem v151_7_3 : ∀ e ∈ k151_7_3, ¬ Live516.live basicOps goal 7 (wsOf c151.2 e).toFinset := level_sound hR151 7 k151_7_3 (D151_6.map (wsOf c151.2)) (map_dead w151_6) (by decide +kernel)
def k151_7_4 : List Entry := [([23,296,30,45,358],[7,20,29],[37]),([23,296,30,45,374],[7,22,34],[38]),([23,296,30,87,76],[16,2,24],[]),([23,296,30,103,76],[16,2,29],[]),([23,296,30,103,92],[7,16],[37,24]),([23,296,30,119,76],[16,2,34],[]),([23,296,30,119,108],[7,16],[38,25]),([23,296,30,1663,64],[7,16],[39]),([23,296,30,1663,68],[],[]),([23,296,44,1391,66],[7,16],[40]),([23,296,44,1391,70],[7],[]),([23,296,1663,66,76],[7],[40]),([23,296,1663,66,92],[],[40,39]),([23,297,46,630,92],[0,16],[26,28]),([23,297,46,646,108],[0,16],[27,29]),([23,297,60,358,76],[16],[26]),([23,297,60,358,126],[0],[]),([23,297,60,374,92],[16],[27]),([23,297,60,374,126],[0],[]),([23,297,60,1663,64],[],[]),([23,358,29,313,76],[24,11],[]),([23,358,29,313,92],[11],[]),([23,358,29,313,108],[11],[]),([23,358,57,92,45],[20],[]),([23,358,57,108,45],[22],[]),([23,1935,66,88,108],[],[]),([23,1935,66,88,124],[],[]),([87,45,54,294,76],[24],[]),([87,45,54,294,92],[],[]),([87,45,54,294,108],[],[]),([87,45,307,72,300],[11],[]),([87,45,307,300,20],[24],[]),([87,51,300,20,45],[11],[]),([87,51,300,20,61],[24],[]),([87,51,300,21,316],[11],[]),([87,55,77,568,44],[24],[]),([87,55,92,77,36],[],[]),([87,55,92,77,68],[],[]),([87,55,93,568,44],[24],[]),([87,58,92,47,52],[],[]),([87,58,108,47,52],[],[]),([87,59,108,29,36],[],[]),([87,59,108,77,68],[],[41]),([87,59,124,29,36],[],[]),([87,59,124,77,68],[],[42]),([351,59,29,128,348],[],[]),([351,59,29,132,348],[],[]),([351,59,29,144,348],[],[]),([351,59,29,148,348],[],[]),([351,59,92,29,36],[],[])]
set_option maxRecDepth 100000 in
theorem v151_7_4 : ∀ e ∈ k151_7_4, ¬ Live516.live basicOps goal 7 (wsOf c151.2 e).toFinset := level_sound hR151 7 k151_7_4 (D151_6.map (wsOf c151.2)) (map_dead w151_6) (by decide +kernel)
def k151_7_5 : List Entry := [([351,59,92,29,112],[],[]),([351,59,92,29,116],[],[]),([351,59,92,29,128],[],[]),([351,59,92,29,132],[],[]),([1663,54,74,42,92],[],[])]
set_option maxRecDepth 100000 in
theorem v151_7_5 : ∀ e ∈ k151_7_5, ¬ Live516.live basicOps goal 7 (wsOf c151.2 e).toFinset := level_sound hR151 7 k151_7_5 (D151_6.map (wsOf c151.2)) (map_dead w151_6) (by decide +kernel)
def D151_7 : List Entry := k151_7_0 ++ (k151_7_1 ++ (k151_7_2 ++ (k151_7_3 ++ (k151_7_4 ++ (k151_7_5)))))
theorem w151_7 : ∀ e ∈ D151_7, ¬ Live516.live basicOps goal 7 (wsOf c151.2 e).toFinset := (app_dead v151_7_0 (app_dead v151_7_1 (app_dead v151_7_2 (app_dead v151_7_3 (app_dead v151_7_4 v151_7_5)))))
def k151_8_0 : List Entry := [([19,26,60,87],[7,24],[]),([19,26,60,103],[7,20,29],[0]),([19,26,60,119],[7,22,34],[1]),([19,26,60,343],[0],[]),([19,26,60,359],[0,20],[2]),([19,26,60,375],[0,22],[3]),([19,26,60,1391],[7,24],[]),([19,26,60,1407],[7,24],[]),([19,26,60,1663],[7,29],[]),([19,26,61,358],[7],[4]),([19,26,61,374],[7,18,20],[5]),([19,26,61,390],[7,19,22],[6]),([19,26,61,614],[7,24],[]),([19,26,102,29],[24,11],[7]),([19,26,102,61],[7,11,16],[7]),([19,26,102,76],[],[]),([19,26,102,77],[16],[]),([19,26,103,76],[7,16],[7]),([19,26,103,92],[16,7],[]),([19,26,110,298],[0],[7]),([19,26,111,568],[24],[]),([19,26,118,76],[],[]),([19,26,118,92],[],[]),([19,26,118,142],[7],[]),([19,26,119,76],[7,26],[]),([19,26,119,92],[16,7],[]),([19,26,119,108],[7,16],[5]),([19,26,126,134],[7],[]),([19,26,134,76],[],[]),([19,26,134,108],[],[]),([19,26,134,142],[7],[]),([19,26,135,76],[7,28],[]),([19,26,135,92],[16,7],[]),([19,26,135,124],[7,16],[6]),([19,26,142,134],[7],[]),([19,26,358,61],[7],[]),([19,26,375,108],[0,16],[2]),([19,26,391,124],[0,16],[3]),([19,26,1935,48],[7,16],[8]),([19,26,1935,52],[],[]),([19,110,298,61],[7,24],[]),([19,300,20,29],[7,16,20,22,24,1,29,34],[9,10,11,12,13,14,15,16,17]),([19,300,20,71],[7,24,16,20,22,29,26,34,28],[18,19,20,12]),([19,300,20,79],[7,24,16,20,22,29,26,34,28,1],[18]),([19,300,20,87],[7,29,26,16,20,22,34],[21,22,23,13]),([19,300,20,95],[7,29,26,16,20,22,34,1],[24]),([19,300,20,103],[7,34,28,16,20,22,29],[25,26,27,14]),([19,300,20,111],[7,34,28,16,20,22,29,1],[28]),([19,300,20,1119],[7,29,24,25,26,20,16],[15]),([19,300,20,1135],[7,34,24,27,28,22,16],[16])]
set_option maxRecDepth 100000 in
theorem v151_8_0 : ∀ e ∈ k151_8_0, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_0 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_1 : List Entry := [([19,300,20,1391],[7,34,29,26,16,20,22],[29,30,17]),([19,300,21,45],[0,16,7,20,22,24,29,34],[31,32,33]),([19,300,21,87],[0,7,11,16],[34]),([19,300,21,95],[0,7,24],[35]),([19,300,21,103],[0,7,12,16,20,29],[36,37]),([19,300,21,111],[0,7,29,26],[]),([19,300,21,119],[0,7,14,16,22,34],[38,39]),([19,300,21,127],[0,7,34,28],[]),([19,300,21,342],[0,7,24,16,20,22,29,26,34,28],[35,31]),([19,300,21,358],[0,7,29,16,20,26,22,34],[40,41,32]),([19,300,21,374],[0,7,34,16,20,22,28,29],[42,43,33]),([19,300,21,1391],[0,25,26,24],[]),([19,300,21,1407],[0,27,28,24],[]),([19,300,21,1663],[0,26,29,34,28],[44]),([19,300,103,92],[0,7],[40]),([19,300,103,142],[0],[41]),([19,300,119,108],[0,7],[42]),([19,300,119,142],[0],[43]),([19,300,1663,50],[0],[44]),([19,301,36,45],[0,16,7,20,22,24,29,34],[45,46,47]),([19,301,36,87],[0,7,11,16],[48]),([19,301,36,95],[0,7,24],[49]),([19,301,36,103],[0,7,12,16,20,29],[50,51]),([19,301,36,111],[0,7,29,26],[]),([19,301,36,119],[0,7,14,16,22,34],[52,53]),([19,301,36,127],[0,7,34,28],[]),([19,301,36,342],[0,7,11,16,20,22,29,26,34,28],[49,45]),([19,301,36,358],[0,7,12,16,20,26,22,34,29],[54,55,46]),([19,301,36,374],[0,7,14,16,20,22,28,29,34],[56,57,47]),([19,301,36,1391],[0,25,26,24],[]),([19,301,36,1407],[0,27,28,24],[]),([19,301,36,1663],[0,26,29,34,28],[58]),([19,301,374,92],[0,7],[54]),([19,301,374,142],[0],[55]),([19,301,390,108],[0,7],[56]),([19,301,390,142],[0],[57]),([19,301,1935,64],[0],[58]),([19,359,53,92],[7,24],[]),([19,359,76,53],[11,16],[59]),([19,1935,66,92],[7],[]),([19,1935,70,76],[],[]),([23,45,317,870],[11],[]),([23,45,359,92],[7],[]),([23,45,367,584],[11],[]),([23,45,375,56],[0,29,16],[]),([23,45,375,72],[0,13,29,16],[]),([23,45,375,92],[7],[]),([23,45,375,108],[7],[]),([23,45,391,56],[0,34,16],[]),([23,45,391,72],[0,15,34,16],[])]
set_option maxRecDepth 100000 in
theorem v151_8_1 : ∀ e ∈ k151_8_1, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_1 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_2 : List Entry := [([23,45,391,92],[7],[]),([23,45,391,124],[7],[]),([23,46,118,92],[],[]),([23,46,118,142],[0],[]),([23,46,134,108],[],[]),([23,46,134,142],[0],[]),([23,46,1935,48],[],[]),([23,47,118,300],[0,24],[]),([23,47,118,604],[0],[]),([23,47,134,108],[0,16],[60]),([23,47,134,604],[0,20],[60]),([23,47,150,124],[0,16],[61]),([23,47,150,604],[0,22],[61]),([23,47,332,870],[0],[]),([23,47,374,92],[7],[]),([23,47,382,328],[11,0],[]),([23,47,390,92],[7],[]),([23,47,390,108],[7],[]),([23,47,406,92],[7],[]),([23,47,406,124],[7],[]),([23,47,638,328],[0,11],[]),([23,60,47,102],[0],[]),([23,60,47,118],[0,20],[62]),([23,60,47,134],[0,22],[63]),([23,60,47,358],[],[]),([23,60,87,78],[7],[]),([23,60,103,58],[16],[]),([23,60,103,78],[7],[]),([23,60,103,92],[26],[]),([23,60,103,142],[16],[]),([23,60,111,134],[16],[]),([23,60,119,58],[16],[]),([23,60,119,78],[7],[]),([23,60,119,108],[28],[]),([23,60,119,142],[16],[]),([23,60,127,134],[16],[]),([23,60,343,50],[7],[]),([23,60,343,58],[16,20,22,1],[64,65]),([23,60,343,78],[7],[]),([23,60,343,590],[7,1],[]),([23,60,351,112],[29],[]),([23,60,351,116],[],[]),([23,60,351,128],[34],[]),([23,60,351,132],[],[]),([23,60,359,78],[7],[]),([23,60,359,92],[],[]),([23,60,359,142],[16],[]),([23,60,367,134],[0],[]),([23,60,375,78],[7],[]),([23,60,375,108],[],[])]
set_option maxRecDepth 100000 in
theorem v151_8_2 : ∀ e ∈ k151_8_2, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_2 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_3 : List Entry := [([23,60,375,142],[16],[]),([23,60,383,134],[0],[]),([23,60,607,58],[7],[]),([23,60,623,66],[7],[]),([23,60,623,134],[7],[]),([23,60,639,66],[7],[]),([23,60,639,134],[7],[]),([23,60,1663,50],[16],[]),([23,60,1663,54],[16],[]),([23,60,1663,66],[16],[]),([23,60,1663,70],[16,34,29,21,23],[]),([23,60,1663,86],[7],[]),([23,61,61,358],[11,8],[]),([23,61,61,870],[7,1,8],[66]),([23,61,103,92],[1,16],[]),([23,61,103,1112],[7,24],[67,68,69]),([23,61,119,72],[1],[]),([23,61,119,92],[1],[]),([23,61,119,108],[16],[70]),([23,61,119,1112],[7,20,29],[71,72,73,70]),([23,61,135,72],[1],[]),([23,61,135,92],[1],[]),([23,61,135,124],[16],[74]),([23,61,135,1112],[7,22,34],[75,76,77,74]),([23,61,358,40],[24,16,20,17],[]),([23,61,358,41],[16,1],[78]),([23,61,358,42],[16,20,22,24,1],[79,80]),([23,61,358,77],[7,1,11],[78]),([23,61,359,56],[16,24,1],[81]),([23,61,359,92],[7,1,16],[]),([23,61,359,1112],[7,24],[82,83,84,81]),([23,61,374,92],[],[]),([23,61,374,142],[16],[]),([23,61,375,72],[1],[]),([23,61,375,92],[7,1],[]),([23,61,375,108],[16],[85]),([23,61,375,1112],[7,18,20,29],[86,87,88,85]),([23,61,382,134],[16],[]),([23,61,390,108],[],[]),([23,61,390,142],[16],[]),([23,61,391,72],[1],[]),([23,61,391,92],[7,1],[]),([23,61,391,124],[16],[89]),([23,61,391,1112],[7,19,22,34],[90,91,92,89]),([23,61,398,134],[16],[]),([23,61,568,28],[7,8,20,22,24,1,29,34],[93,94,95,84,88,92,96,97,98]),([23,61,568,30],[7,8,20,22,24,1,29,34],[68,72,76]),([23,61,568,44],[7,16,20,22,24,1,29,34],[99,100,101,69,73,77,102,103,104]),([23,61,568,46],[7,16,20,22,24,1,29,34],[83,87,91]),([23,61,568,1391],[7,24],[96,102])]
set_option maxRecDepth 100000 in
theorem v151_8_3 : ∀ e ∈ k151_8_3, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_3 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_4 : List Entry := [([23,61,568,1407],[7,24],[97,103]),([23,61,568,1663],[7,29],[98,104]),([23,61,569,44],[7,0,1,20,22,24,29,34],[105,106,107]),([23,61,569,60],[7,16,20,22,24,0,29,34],[108,109,110]),([23,61,569,76],[20,7,0,16],[111,112]),([23,61,569,92],[22,7,0,16],[113,114]),([23,61,569,358],[0],[105,108,111,113]),([23,61,569,374],[0,20],[115,106,109,112]),([23,61,569,390],[0,22],[116,107,110,114]),([23,61,614,72],[7,1],[117]),([23,61,614,73],[7],[118,119,120]),([23,61,614,77],[7],[]),([23,61,614,334],[7,24],[]),([23,61,631,108],[16],[115]),([23,61,647,124],[16],[116]),([23,61,1935,64],[16],[121]),([23,61,1935,68],[],[]),([23,102,29,316],[],[]),([23,102,29,317],[16,11],[122]),([23,102,29,318],[16],[]),([23,102,29,333],[24,11],[122]),([23,102,61,333],[16,7,11],[122]),([23,102,63,348],[7],[]),([23,102,76,63],[7],[]),([23,102,77,45],[],[123]),([23,103,45,332],[16,1],[]),([23,103,45,840],[24],[124,125,126]),([23,103,77,348],[16,7],[122]),([23,103,92,77],[8,11],[]),([23,103,92,840],[7,16],[127,128,129,130]),([23,103,92,841],[7],[131,132,133,134]),([23,103,93,1112],[7,16,24],[135,136,137]),([23,103,840,28],[0,24,16,26,28],[138,127,139,124,82]),([23,103,840,30],[0,7,24,16],[135,124,136]),([23,103,840,44],[7,11,16,20,22,29,26,34,28],[140,141,125,129,137]),([23,103,840,46],[7,11,16],[84,125,83,130]),([23,103,840,76],[16,8,24,20,22,29,26,34,28],[127,135,84,126]),([23,103,841,44],[0,7,24],[131]),([23,103,841,60],[0,7,11,16],[132]),([23,103,841,92],[16,11],[131]),([23,103,841,108],[11,16],[133]),([23,103,841,124],[11,16],[134]),([23,110,62,112],[],[]),([23,110,62,116],[],[]),([23,110,62,128],[],[]),([23,110,62,132],[],[]),([23,110,63,128],[0],[]),([23,110,63,132],[0],[]),([23,110,63,144],[0],[]),([23,110,63,148],[0],[])]
set_option maxRecDepth 100000 in
theorem v151_8_4 : ∀ e ∈ k151_8_4, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_4 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_5 : List Entry := [([23,110,298,57],[24],[7]),([23,110,298,61],[16],[]),([23,111,78,128],[0,16,1],[]),([23,111,78,132],[0,16,1],[]),([23,111,78,144],[0,16,1],[]),([23,111,78,148],[0,16,1],[]),([23,111,78,840],[11],[]),([23,111,568,57],[24],[142,143,144]),([23,111,568,61],[24],[]),([23,111,570,328],[0,24],[145,146,147,148]),([23,111,840,44],[7,24,16,1,20,22,29,26,34,28],[149,125]),([23,111,840,46],[7,1,24],[125]),([23,111,840,76],[8,1,24,20,22,29,26,34,28],[126]),([23,111,841,60],[7,0,24],[145]),([23,111,841,92],[7,0,24],[146]),([23,111,841,108],[7,24],[147]),([23,111,841,124],[7,24],[148]),([23,118,76,43],[16,2,29],[]),([23,118,76,63],[7],[]),([23,119,56,56],[0,16,1],[150,151,152]),([23,119,92,57],[],[153,154,155]),([23,119,92,77],[8],[155]),([23,119,92,840],[7,16],[156,157,158,159]),([23,119,92,841],[7],[160,161,162,163]),([23,119,108,840],[7,16],[164,165,166,85]),([23,119,108,841],[7],[167,168,169,170]),([23,119,158,1112],[7],[171,172]),([23,119,840,28],[0,29,13,16,20,26],[156,86]),([23,119,840,44],[7,12,29,13,16,20,22,24,26,34],[173,158,164,171]),([23,119,840,46],[7,12,29,13,16,20],[88,87,159,165]),([23,119,840,76],[16,8,13,29,20,22,24,26,34],[156,88,166,172]),([23,119,841,44],[0,7,29,16],[160,167]),([23,119,841,60],[0,7,12,16,20],[161,168]),([23,119,841,92],[16,12,20,29],[160,169]),([23,119,841,108],[20,12,16,29],[167,162]),([23,119,841,124],[12,0,16,20,29],[163,170]),([23,127,150,1112],[7],[174,175]),([23,127,840,44],[7,29,13,16,1,20,22,24,26,34],[174]),([23,127,840,46],[7,1,29,13],[]),([23,127,840,76],[2,8,1,29,13,20,22,24,26,34],[175]),([23,127,841,60],[7,0,29,13],[]),([23,127,841,92],[16,7,0,29,13],[]),([23,127,841,108],[7,13,29,16],[]),([23,127,841,124],[0,29,16],[]),([23,134,76,43],[16,2,34],[]),([23,134,76,63],[7],[]),([23,135,92,57],[],[176,177,178]),([23,135,92,77],[8],[178]),([23,135,92,840],[7,16],[179,180,181,182]),([23,135,92,841],[7],[183,184,185,186])]
set_option maxRecDepth 100000 in
theorem v151_8_5 : ∀ e ∈ k151_8_5, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_5 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_6 : List Entry := [([23,135,124,840],[7,16],[187,188,189,89]),([23,135,124,841],[7],[190,191,192,193]),([23,135,158,1112],[7],[194,195]),([23,135,840,28],[0,34,15,16,22,28],[179,90]),([23,135,840,44],[7,14,34,15,16,20,22,24,28,29],[196,181,187,194]),([23,135,840,46],[7,14,34,15,16,22],[92,91,182,188]),([23,135,840,76],[16,8,15,34,20,22,24,28,29],[179,92,189,195]),([23,135,841,44],[0,7,34,16],[183,190]),([23,135,841,60],[0,7,14,16,22],[184,191]),([23,135,841,92],[16,14,22,34],[183,192]),([23,135,841,108],[14,0,16,22,34],[185,193]),([23,135,841,124],[22,14,16,34],[190,186]),([23,143,150,1112],[7],[197,198]),([23,143,840,44],[7,34,15,16,1,20,22,24,28,29],[197]),([23,143,840,46],[7,1,34,15],[]),([23,143,840,76],[2,8,1,34,15,20,22,24,28,29],[198]),([23,143,841,60],[7,0,34,15],[]),([23,143,841,92],[16,7,0,34,15],[]),([23,143,841,108],[0,34,16],[]),([23,143,841,124],[7,15,34,16],[]),([23,296,30,45],[7,16,2,20,22,24,1,29,34],[199,200,201,141,173,196]),([23,296,30,87],[7,24,16],[202,199,149,99]),([23,296,30,95],[7,11,1],[140]),([23,296,30,103],[7,29,16,20,13],[203,204,200,100]),([23,296,30,111],[7,12,29,1,13],[]),([23,296,30,119],[7,34,16,22,15],[205,206,201,101]),([23,296,30,127],[7,14,34,1,15],[]),([23,296,30,1391],[7,25,13,24,16],[96,102]),([23,296,30,1407],[7,27,15,24,16],[97,103]),([23,296,30,1663],[7,13,29,16],[207,208,98,104]),([23,296,44,1119],[7,29,24,2,8,25,13,20],[96]),([23,296,44,1135],[7,34,24,2,8,27,15,22],[97]),([23,296,44,1391],[7,34,29,2,8,13,20,22,24,26],[209,210,98]),([23,296,1663,66],[7,16],[211,212,207,209]),([23,296,1663,70],[7],[208,210]),([23,297,46,614],[0,11,16],[145,105,108]),([23,297,46,630],[0,12,7,20,29,13,16],[213,106,109]),([23,297,46,646],[0,14,7,22,34,15,16],[214,107,110]),([23,297,60,342],[0,16,2,7,24,20,22,29,26,34,28],[146,105]),([23,297,60,358],[0,16,2,7,29,20,13,22,24,26,34],[215,216,106]),([23,297,60,374],[0,16,2,7,34,20,22,15,24,28,29],[217,218,107]),([23,297,60,1391],[0,25,13,24],[]),([23,297,60,1407],[0,27,15,24],[]),([23,297,60,1663],[0,13,29,34,15],[219]),([23,297,76,342],[0,20,7,16,26,24,3,22],[147,111]),([23,297,76,358],[0,20,13,7,16,26,29],[112]),([23,297,76,1391],[0,13,24],[]),([23,297,76,1407],[0,24],[]),([23,297,76,1663],[0,29,13],[]),([23,297,92,342],[0,22,7,16,28,24,5,20],[148,113])]
set_option maxRecDepth 100000 in
theorem v151_8_6 : ∀ e ∈ k151_8_6, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_6 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_7 : List Entry := [([23,297,92,374],[0,22,15,7,16,28,34],[114]),([23,297,92,1391],[0,24],[]),([23,297,92,1407],[0,15,24],[]),([23,297,92,1663],[0,29,15],[]),([23,297,358,45],[0],[]),([23,297,374,92],[0,16],[54,213,215,115]),([23,297,374,142],[0],[55,216]),([23,297,390,108],[0,16],[56,214,217,116]),([23,297,390,142],[0],[57,218]),([23,297,1935,64],[0],[58,219]),([23,358,29,54],[0],[]),([23,358,29,313],[24,11],[220,221,222]),([23,358,29,317],[11],[]),([23,358,55,92],[7,24],[]),([23,358,56,46],[7,16,1,24,26,28],[117]),([23,358,56,60],[24,16,8,20,22,29,26,34,28],[117]),([23,358,57,62],[11],[118]),([23,358,57,76],[16,8,24,20,22,29,26,34,28],[118,220,142]),([23,358,57,92],[20,24,7,16,26,22],[223,221,143,119]),([23,358,57,108],[22,24,7,16,28,20],[224,222,144,120]),([23,358,61,45],[11],[]),([23,358,63,572],[7,24],[]),([23,359,72,62],[7,1],[]),([23,359,72,76],[8,1,24,20,22,29,26,34,28],[]),([23,359,72,92],[9,24,16,26,1],[]),([23,359,72,108],[10,24,16,28,1],[]),([23,359,73,44],[11],[]),([23,359,73,92],[16,24],[220]),([23,359,73,108],[7,24],[221]),([23,359,73,124],[7,24],[222]),([23,375,72,62],[7,16],[]),([23,391,72,62],[7,16],[]),([23,639,70,152],[0,16,1],[]),([23,639,70,156],[0,16,1],[]),([23,655,70,152],[0,16,1],[]),([23,655,70,156],[0,16,1],[]),([23,1935,48,78],[7],[]),([23,1935,48,92],[],[]),([23,1935,50,92],[7,16],[]),([23,1935,50,108],[16],[212]),([23,1935,66,88],[7,16],[225,226]),([27,60,359,92],[0,7],[215]),([27,60,359,142],[0],[216]),([27,60,375,108],[0,7],[217]),([27,60,375,142],[0],[218]),([27,60,1663,66],[0],[219]),([27,76,95,112],[29,0,7,16,22,3],[]),([27,76,95,116],[7,3],[]),([27,76,95,638],[29,3],[]),([27,76,111,134],[7],[])]
set_option maxRecDepth 100000 in
theorem v151_8_7 : ∀ e ∈ k151_8_7, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_7 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_8 : List Entry := [([27,76,127,134],[7],[]),([27,76,359,60],[0],[]),([27,76,359,142],[0],[]),([27,76,375,108],[0],[]),([27,76,375,142],[0],[]),([27,76,1663,54],[7,34,3],[]),([27,76,1663,66],[0],[]),([27,92,95,128],[34,0,7,16,20,5],[]),([27,92,95,132],[7,5],[]),([27,92,95,654],[34,5],[]),([27,92,111,134],[7],[]),([27,92,127,134],[7],[]),([27,92,359,108],[0],[]),([27,92,359,142],[0],[]),([27,92,375,60],[0],[]),([27,92,375,142],[0],[]),([27,92,1663,54],[7,29,5],[]),([27,92,1663,66],[0],[]),([27,108,111,134],[7],[]),([27,108,127,134],[7],[]),([27,108,359,62],[0,11],[]),([27,108,359,108],[7],[]),([27,108,359,142],[0],[]),([27,108,375,62],[0,11],[]),([27,108,375,124],[7],[]),([27,108,375,142],[0],[]),([27,108,1663,54],[7],[]),([27,108,1663,66],[0],[]),([27,120,375,124],[],[]),([27,124,375,124],[],[]),([27,136,375,108],[],[]),([27,140,375,108],[],[]),([27,1935,66,76],[],[]),([31,102,55,92],[7],[]),([31,358,55,92],[24],[]),([31,358,63,572],[7,11],[]),([31,1935,52,78],[0],[]),([87,45,54,294],[0,24],[227,228,229]),([87,45,54,302],[0],[]),([87,45,307,72],[0,11],[230]),([87,45,307,300],[24],[231,7,230]),([87,45,311,92],[24],[]),([87,45,311,296],[11],[231]),([87,45,315,92],[24],[227,220]),([87,45,315,108],[24],[228,221]),([87,45,315,124],[24],[229,222]),([87,45,315,136],[24],[]),([87,45,315,140],[24],[]),([87,45,315,152],[24],[]),([87,45,315,156],[24],[])]
set_option maxRecDepth 100000 in
theorem v151_8_8 : ∀ e ∈ k151_8_8, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_8 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_9 : List Entry := [([87,50,42,76],[7],[]),([87,51,56,61],[0],[]),([87,51,56,77],[7,24],[]),([87,51,56,301],[7],[230]),([87,51,58,92],[7,24],[]),([87,51,58,572],[16],[7,230]),([87,51,300,20],[11,16,26,28,20,22],[232,233,231]),([87,51,300,21],[7,11,16],[59,234]),([87,51,300,61],[11],[59,234]),([87,51,301,36],[24],[231]),([87,55,46,76],[11],[]),([87,55,46,332],[7],[]),([87,55,77,348],[24],[122]),([87,55,77,568],[24,11],[235]),([87,55,92,77],[],[236,237]),([87,55,92,589],[7,11],[]),([87,55,93,568],[16,24],[238]),([87,55,296,30],[7,11,16],[235,238]),([87,58,92,43],[7,9],[]),([87,58,92,47],[7],[239]),([87,58,108,43],[7,10],[]),([87,58,108,47],[7],[240]),([87,59,108,29],[7],[241]),([87,59,108,77],[20],[242,223]),([87,59,124,29],[7],[243]),([87,59,124,77],[22],[244,224]),([87,59,140,588],[7,11,29,26,16,20,28],[]),([87,59,156,588],[7,11,34,28,16,22,26],[]),([87,63,76,38],[0],[]),([87,574,47,52],[24,0],[]),([87,574,47,128],[0,11],[]),([87,574,47,132],[0,11],[]),([87,574,47,144],[0,11],[]),([87,574,47,148],[0,11],[]),([87,574,52,46],[16,0,11],[]),([87,574,54,60],[24,0,7,16],[]),([87,574,54,62],[0,16],[]),([95,50,42,76],[],[]),([351,59,29,128],[0,16],[245]),([351,59,29,132],[0,16],[246]),([351,59,29,144],[0,16],[247]),([351,59,29,148],[0,16],[248]),([351,59,29,348],[16],[245,246,247,248]),([351,59,60,53],[7],[]),([351,59,61,332],[24,11],[]),([351,59,61,348],[7,11],[]),([351,59,77,348],[24,11],[]),([351,59,92,29],[16],[249,250,251,252,253]),([351,59,92,77],[11],[]),([351,63,52,61],[7],[])]
set_option maxRecDepth 100000 in
theorem v151_8_9 : ∀ e ∈ k151_8_9, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_9 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def k151_8_10 : List Entry := [([351,63,53,324],[24,11],[]),([351,63,53,384],[0,7],[]),([351,63,53,388],[0,7],[]),([351,63,53,400],[0,7],[]),([351,63,53,404],[0,7],[]),([351,63,69,384],[0,24],[]),([351,63,69,388],[0,24],[]),([351,63,69,400],[0,24],[]),([351,63,69,404],[0,24],[]),([351,63,129,400],[0,24],[]),([351,63,129,404],[0,24],[]),([351,63,133,400],[0,24],[]),([351,63,133,404],[0,24],[]),([1663,50,74,46],[7],[]),([1663,50,74,108],[7],[225]),([1663,50,74,124],[7],[226]),([1663,54,74,42],[0,16],[254]),([1663,70,78,132],[13],[])]
set_option maxRecDepth 100000 in
theorem v151_8_10 : ∀ e ∈ k151_8_10, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := level_sound hR151 8 k151_8_10 (D151_7.map (wsOf c151.2)) (map_dead w151_7) (by decide +kernel)
def D151_8 : List Entry := k151_8_0 ++ (k151_8_1 ++ (k151_8_2 ++ (k151_8_3 ++ (k151_8_4 ++ (k151_8_5 ++ (k151_8_6 ++ (k151_8_7 ++ (k151_8_8 ++ (k151_8_9 ++ (k151_8_10))))))))))
theorem w151_8 : ∀ e ∈ D151_8, ¬ Live516.live basicOps goal 8 (wsOf c151.2 e).toFinset := (app_dead v151_8_0 (app_dead v151_8_1 (app_dead v151_8_2 (app_dead v151_8_3 (app_dead v151_8_4 (app_dead v151_8_5 (app_dead v151_8_6 (app_dead v151_8_7 (app_dead v151_8_8 (app_dead v151_8_9 v151_8_10))))))))))
def k151_9_0 : List Entry := [([19,26,60],[7,0,20,22,24,1,29,34],[0,1,2,3,4,5,6,7,8]),([19,26,61],[7,16,0,20,22,24,1,29,34],[9,10,11,12]),([19,26,102],[0,7,24,11,16,20,22,29,26,34,28],[13,14,15,16]),([19,26,103],[7,24,11,16],[17,18,13,9]),([19,26,110],[7,24,16,20,22,29,26,34,28],[13,19]),([19,26,111],[7,24,16,1],[13,20]),([19,26,118],[0,7,26,12,16,20,22,34],[21,22,23]),([19,26,119],[7,29,12,16,20,26],[24,25,26,10]),([19,26,126],[7,26,0,16,20,22,34,29],[27]),([19,26,127],[7,29,26,16,1],[]),([19,26,134],[0,7,28,14,16,20,22,29],[28,29,30]),([19,26,135],[7,34,14,16,22,28],[31,32,33,11]),([19,26,142],[7,28,0,16,20,22,29,34],[34]),([19,26,143],[7,34,28,16,1],[]),([19,26,358],[7,0,24,16,20,22,26,28],[35,20,12]),([19,26,359],[7,24,0,16],[17,19,3]),([19,26,366],[0,24,11,16,1,26,28,20,22],[]),([19,26,375],[0,7,29,20,26,16],[24,36,4]),([19,26,391],[0,7,34,22,28,16],[31,37,5]),([19,26,1663],[7,25,26,24,16],[6]),([19,26,1679],[7,27,28,24,16],[7]),([19,26,1935],[7,26,29,16],[38,39,8]),([19,110,298],[7,24,16,26,28,20,22],[40]),([19,126,134],[7,12,34,32],[]),([19,142,134],[7,14,29,31],[]),([19,300,20],[16,20,22,24,29,34],[41,42,43,44,45,46,47,48,49,50]),([19,300,21],[7,16,20,22,24,29,34,0],[51,52,53,54,55,56,57,58,59,60,61,62,63]),([19,300,87],[0,24,7,16,20,22,29,26,34,28],[58]),([19,300,103],[0,29,7,16,20,26,22,34],[64,65,59]),([19,300,119],[0,34,7,16,20,22,28,29],[66,67,60]),([19,300,1391],[7,29,24,25,26,20],[48,61]),([19,300,1407],[7,34,24,27,28,22],[49,62]),([19,300,1663],[7,34,29,0,26,16,20,22,28],[68,50,63]),([19,301,36],[7,16,20,22,24,29,34,0],[69,70,71,72,73,74,75,76,77,78,79,80,81]),([19,301,358],[0,11,16,20,22,29,26,34,28],[76]),([19,301,374],[0,12,7,16,20,26,22,34,29],[82,83,77]),([19,301,390],[0,14,7,16,20,22,28,29,34],[84,85,78]),([19,301,1663],[0,25,26,24],[79]),([19,301,1679],[0,27,28,24],[80]),([19,301,1935],[0,26,29,34,28],[86,81]),([19,359,53],[7,11,16],[19,87,14]),([19,359,76],[0,24,7,16,20,22,26,28],[88,17]),([19,359,77],[7,24],[14,35,40]),([19,367,52],[0,7,24,16,20,22,29,26,34,28],[]),([19,367,128],[29,0,7,24,16,20,22,34,28],[]),([19,367,132],[7,26,0,16,20,22,34,28],[]),([19,367,144],[34,0,7,24,16,20,22,29,26],[]),([19,367,148],[7,28,0,16,20,22,29,26],[]),([19,375,76],[0,29,13,16,20,22,26],[24]),([19,375,108],[7,21,0,16,22,24,26,34,33],[36,82])]
set_option maxRecDepth 100000 in
theorem v151_9_0 : ∀ e ∈ k151_9_0, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_0 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_1 : List Entry := [([19,375,158],[7,32,29],[83]),([19,383,52],[0,7,29,16,20,22,24,26,34,33],[]),([19,383,150],[0,7,28,34],[]),([19,391,76],[0,34,15,16,20,22,28],[31]),([19,391,124],[7,23,0,16,20,24,28,29,33],[37,84]),([19,391,158],[7,31,34],[85]),([19,399,52],[0,7,34,16,20,22,24,28,29,33],[]),([19,399,150],[0,7,21,29],[]),([19,1935,52],[7,29,30,13,15],[]),([19,1935,66],[7,30,21],[89,86]),([19,1935,70],[7,34,29,13,15,0],[90]),([23,45,317],[0,16,7,20,22],[91]),([23,45,359],[0,11,16,24],[92]),([23,45,367],[0,7,24],[93]),([23,45,375],[0,16,20,29,7],[94,95,96,97]),([23,45,383],[0,29,7,16],[]),([23,45,391],[0,16,22,34,7],[98,99,100,101]),([23,45,399],[0,34,7,16],[]),([23,45,614],[0,11,24,16,20,22],[93,91]),([23,45,1663],[0,24,7],[]),([23,45,1679],[0,24,7],[]),([23,45,1935],[0,29,7],[]),([23,46,102],[0,7,16,20,22,29,26,34,28],[]),([23,46,118],[0,7,16,20,13,22,24,26,34,29],[102,103]),([23,46,134],[0,7,16,20,22,15,24,28,29,34],[104,105]),([23,46,614],[0,11,16,20,22,26,28],[]),([23,46,1663],[0,25,13,24],[]),([23,46,1679],[0,27,15,24],[]),([23,46,1935],[0,13,29,34,15],[106]),([23,47,118],[0,7,24,16],[107,108]),([23,47,134],[0,7,29,20,13,16],[109,110]),([23,47,150],[0,7,34,22,15,16],[111,112]),([23,47,332],[7,0,20,22,24,29,34],[108,110,112,113]),([23,47,374],[0,7,11,16],[114]),([23,47,382],[0,7,24],[107,115]),([23,47,390],[0,7,12,16,20],[116,117]),([23,47,398],[0,7,29,13],[]),([23,47,406],[0,7,14,16,22],[118,119]),([23,47,414],[0,7,34,15],[]),([23,47,638],[0,24,11],[120]),([23,47,654],[0,29,7,16],[95]),([23,47,670],[0,34,7,16],[99]),([23,47,886],[7,11,0,24,16],[115,120,113]),([23,60,47],[7,0,8,20,22,24,29,34,1],[121,122,123,124]),([23,60,87],[16,24,1,11,20,22,29,26,34,28],[125,124]),([23,60,95],[16,24,1,20,22,29,26,34,28],[]),([23,60,103],[16,29,1,20,21,22,24,26,34],[126,127,128,129]),([23,60,111],[16,29,1,20,22,24,26,34],[130]),([23,60,119],[16,34,1,20,22,23,24,28,29],[131,132,133,134]),([23,60,127],[16,34,1,20,22,24,28,29],[135])]
set_option maxRecDepth 100000 in
theorem v151_9_1 : ∀ e ∈ k151_9_1, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_1 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_2 : List Entry := [([23,60,343],[16,24,0,7,1,20,22,29,26,34,28],[136,137,9,138,12,113,139]),([23,60,351],[16,0,24,1,20,22,29,26,34,28],[140,141,142,143]),([23,60,359],[16,29,0,21,18,1,20,22,24,26,34],[144,145,146]),([23,60,367],[16,0,29,1,20,22,24,26,34],[147]),([23,60,375],[16,34,0,23,19,1,20,22,24,28,29],[148,149,150]),([23,60,383],[16,0,34,1,20,22,24,28,29],[151]),([23,60,607],[7,24,11,1,20,22,29,26,34,28],[152,9,139]),([23,60,623],[7,29,18,1,21,22,24,26,34],[153,154]),([23,60,639],[7,34,19,1,23,20,24,28,29],[155,156]),([23,60,1391],[16,29,24,25,21],[]),([23,60,1407],[16,34,24,27,23],[]),([23,60,1663],[16,34,29,21,7,22,24,26,23],[157,158,159,160,161]),([23,61,61],[0,7,8,20,22,1],[162,163]),([23,61,103],[16,24,11,1],[164,162,165]),([23,61,119],[16,29,20,1],[166,167,168,169]),([23,61,135],[16,34,22,1],[170,171,172,173]),([23,61,358],[7,16,1,11,20,22,29,26,34,28],[174,175,176,177,138]),([23,61,359],[16,24,11,1],[178,179,180]),([23,61,366],[16,1,24,20,22,29,26,34,28],[]),([23,61,374],[7,16,1,18,21,20,22,24,26,34],[153,144,181,182]),([23,61,375],[16,29,18,20,1],[183,184,185,186]),([23,61,382],[16,1,29,20,22,24,26,34],[187]),([23,61,390],[7,16,1,19,23,20,22,24,28,29],[155,148,188,189]),([23,61,391],[16,34,19,22,1],[190,191,192,193]),([23,61,398],[16,1,34,20,22,24,28,29],[194]),([23,61,568],[0,7,16,20,22,24,1,29,34],[195,196,197,198,165,169,173,180,186,193,199,200,201]),([23,61,569],[0,7,1,20,22,24,29,34],[202,203,204,205,206,207,208]),([23,61,614],[16,1,24,20,22,26,28],[209,210,211,212,163,91,113]),([23,61,615],[16,24,7,1],[179,206,91]),([23,61,622],[16,1,24,26,28,20,22],[]),([23,61,631],[16,29,7,1,20],[184,213,207]),([23,61,647],[16,34,7,1,22],[191,214,208]),([23,61,879],[7,24,1,11,16],[212]),([23,61,895],[7,29,1,16],[183]),([23,61,911],[7,34,1,16],[190]),([23,61,1663],[16,25,21,24],[199]),([23,61,1679],[16,27,23,24],[200]),([23,61,1935],[16,21,29],[215,216,201]),([23,102,29],[16,24,11],[217,218,219,220]),([23,102,61],[16,7,24,11],[217,218,221]),([23,102,62],[7,24,16,20,22,29,26,34,28],[14,17]),([23,102,63],[7,16,11],[219,222]),([23,102,76],[16,24,11,20,22,29,26,34,28],[223,18,114]),([23,102,77],[16,24,11,20,22,29,26,34,28],[224,220,221,222]),([23,103,45],[24,11,16,1],[225,226]),([23,103,76],[24,7,16,20,22],[217,225,179]),([23,103,77],[7,16,11,24],[225,227,218,177]),([23,103,78],[7,16,24],[219,138]),([23,103,92],[16,24,11,20,22,29,26,34,28],[228,92,114,229,230]),([23,103,93],[16,24,11],[227,220,231])]
set_option maxRecDepth 100000 in
theorem v151_9_2 : ∀ e ∈ k151_9_2, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_2 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_3 : List Entry := [([23,103,840],[0,7,16,24,20,22,29,26,34,28],[232,233,234,235,236,226,229,231,180]),([23,103,841],[7,11,16],[237,238,239,240,241,230]),([23,110,62],[7,0,24,16,20,22,29,26,34,28],[242,243,244,245]),([23,110,63],[7,11,0,24],[107,246,247,248,249]),([23,110,298],[16,24,26,28,0,20,22],[13,250,217,251,219,20,115]),([23,110,318],[7,24,11,26,28,16],[13]),([23,111,78],[7,11,16,1],[252,253,254,255,256]),([23,111,568],[24,16,20,22,1,26,28],[257,258,256,93,115]),([23,111,570],[16,24,1],[225,259,93]),([23,111,590],[7,24,11,16,1],[]),([23,111,840],[0,7,16,24,20,22,29,26,34,28,1],[260,261,262,226]),([23,111,841],[7,0,24],[263,264,265,266,259]),([23,118,42],[16,12,13,20,22,24,26,34,33],[]),([23,118,62],[7,13,29,16,20,22,24,26,34,33],[24]),([23,118,76],[16,29,20,22,24,26,34,33,7],[267,268,25,116]),([23,118,92],[20,29,21,7,16,22,24,26,34,33],[26,117]),([23,118,142],[16,13,29,34,23,20,24,26],[]),([23,119,56],[7,29,21,12,16,26,22],[269,95,183]),([23,119,58],[16,29,0,12,21],[95,153]),([23,119,76],[29,7,16,20,22,21,26],[184]),([23,119,78],[7,16,29,13],[144]),([23,119,92],[16,29,7,20,22,24,26,34,33],[270,271,96,116,272,273]),([23,119,108],[20,29,21,7,16,22,24,26,34,33],[97,117,181,185,274,275]),([23,119,158],[16,29,34,23],[182,276]),([23,119,840],[0,7,13,16,29,20,22,24,26,34],[277,278,279,280,272,274,276,186]),([23,119,841],[7,12,16,20,29],[281,282,283,284,285,273,275]),([23,126,134],[7,16,13,29,32,20,22,24,23,26],[]),([23,127,150],[16,29,34,23],[187,286]),([23,127,840],[0,7,16,29,13,20,22,24,26,34,1],[287,288,289,286]),([23,127,841],[7,0,29,13,16],[290,291,292,293]),([23,134,42],[16,14,15,20,22,24,28,29,33],[]),([23,134,62],[7,15,34,16,20,22,24,28,29,33],[31]),([23,134,76],[16,34,20,22,24,28,29,33,7],[294,295,32,118]),([23,134,108],[22,34,23,7,16,20,24,28,29,33],[33,119]),([23,134,142],[16,15,29,21,22,24,26],[]),([23,135,56],[7,34,23,14,16,28,20],[269,99,190]),([23,135,58],[16,34,0,14,23],[99,155]),([23,135,76],[34,7,16,20,22,23,28],[191]),([23,135,78],[7,16,34,15],[148]),([23,135,92],[16,34,7,20,22,24,28,29,33],[296,297,100,118,298,299]),([23,135,124],[22,34,23,7,16,20,24,28,29,33],[101,119,188,192,300,301]),([23,135,158],[16,29,34,21],[189,302]),([23,135,840],[0,7,15,16,34,20,22,24,28,29],[303,304,305,306,298,300,302,193]),([23,135,841],[7,14,16,22,34],[307,308,309,310,311,299,301]),([23,142,134],[7,16,15,29,34,31,20,22,24,21,26],[]),([23,143,150],[16,29,34,21],[194,312]),([23,143,840],[0,7,16,34,15,20,22,24,28,29,1],[313,314,315,312]),([23,143,841],[7,0,34,15,16],[316,317,318,319]),([23,296,30],[7,16,20,22,24,29,34],[195,320,321,322,323,324,325,326,197,198,234,235,260,261,278,279,287,288,304,305,313,314,327,328,329]),([23,296,44],[16,8,20,22,24,29,34],[195,236,262,280,289,306,315,330,331,332])]
set_option maxRecDepth 100000 in
theorem v151_9_3 : ∀ e ∈ k151_9_3, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_3 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_4 : List Entry := [([23,296,1391],[7,29,24,25,13,20,16],[48,327,330,199]),([23,296,1407],[7,34,24,27,15,22,16],[49,328,331,200]),([23,296,1663],[7,34,29,13,16,20,22,24,26],[333,334,50,329,332,201]),([23,297,46],[0,7,16,1,20,22,24,29,34],[202,203,238,263,282,290,308,316,335,336,337]),([23,297,60],[16,0,2,7,20,22,24,29,34],[202,338,339,340,239,264,283,291,309,317,341,342,343]),([23,297,76],[20,0,3,7,16,22,24,29,34],[344,345,204,240,265,284,292,310,318,346,347,348]),([23,297,92],[22,0,5,7,16,20,24,29,34],[349,350,205,241,266,285,293,311,319,351,352,353]),([23,297,358],[0,7,24,16,20,22,29,26,34,28],[354,259,76,335,338,344,349,206]),([23,297,374],[0,13,29,16,20,22,24,26,34],[355,356,77,336,339,345,207]),([23,297,390],[0,15,34,16,20,22,24,28,29],[357,358,78,337,340,350,208]),([23,297,1663],[0,25,13,24],[79,341,346,351]),([23,297,1679],[0,27,15,24],[80,342,347,352]),([23,297,1935],[0,13,29,34,15],[359,81,343,348,353]),([23,358,29],[0,24,11,16,20,22,1,26,28],[360,361,362]),([23,358,55],[7,24,16],[35,20,363]),([23,358,56],[7,16,24,20,22,29,26,34,28],[364,365,209]),([23,358,57],[7,16,20,22,24,29,26,34,28],[35,366,367,368,369,361,257,210]),([23,358,61],[16,7,24,20,22],[370,362,258,211]),([23,358,63],[7,16,24],[256,371]),([23,358,318],[7,24,16,20,22,26,28],[256,371,120,212]),([23,359,72],[7,0,16,20,22,24,29,26,34,28,1],[372,373,374,375]),([23,359,73],[7,24,16],[17,376,377,378,379,361,250]),([23,359,77],[7,16,24],[362,251]),([23,359,590],[7,11,0,16],[256,120,139]),([23,366,55],[7,0,11],[360]),([23,366,113],[0,29,24,11,16,1,28,20,22],[]),([23,366,117],[0,29,21,24,11,16,20,1,28,22],[]),([23,366,129],[0,34,24,11,16,1,26,20,22],[]),([23,366,133],[0,34,23,24,11,16,22,1,26,20],[]),([23,367,70],[0,7,16,1],[360]),([23,367,128],[29,24,0,7,16,1,20,22,34,28],[140]),([23,367,132],[29,0,21,26,7,16,20,1,22,34,28],[141]),([23,367,144],[34,24,0,7,16,1,20,22,29,26],[142]),([23,367,148],[34,0,23,28,7,16,22,1,20,29,26],[143]),([23,375,72],[7,0,16,20,22,29,26,1],[380]),([23,375,108],[29,21,7,0,16,26,22,34,33],[355,145,213]),([23,375,158],[16,29,32],[356,146]),([23,383,52],[0,29,16,20,22,24,12,26,34,33],[]),([23,383,54],[0,7,16,1,29],[]),([23,383,70],[0,7,16,1],[]),([23,383,150],[0,34,23,16],[147]),([23,391,72],[7,0,16,20,22,34,28,1],[381]),([23,391,124],[34,23,7,0,16,28,20,29,33],[357,149,214]),([23,391,158],[16,34,31],[358,150]),([23,399,52],[0,34,16,20,22,24,14,28,29,33],[]),([23,399,54],[0,7,16,1,34],[]),([23,399,70],[0,7,16,1],[]),([23,399,150],[0,29,21,16],[151]),([23,639,68],[7,0,29,12,13,16,26,20,22,1],[]),([23,639,70],[7,13,0,29,21,16,1],[382,383])]
set_option maxRecDepth 100000 in
theorem v151_9_4 : ∀ e ∈ k151_9_4, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_4 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_5 : List Entry := [([23,639,150],[7,29,32,16],[154]),([23,655,68],[7,0,34,14,15,16,28,20,22,1],[]),([23,655,70],[7,15,0,34,23,16,1],[384,385]),([23,655,150],[7,34,31,16],[156]),([23,1935,48],[29,34,13,30,16,20,22,24,26],[386,387]),([23,1935,50],[16,13],[388,389,215,333]),([23,1935,52],[29,34,7,21,30,16,22,24,26,23],[]),([23,1935,54],[7,16,13],[216,334]),([23,1935,66],[16,21,7],[390,388,359,159]),([23,1935,70],[16,34,29,13,21,23,0],[160]),([23,1935,86],[7,21,30,13,16],[161]),([27,60,343],[0,24,16,2,7,20,22,29,26,34,28],[338]),([27,60,359],[0,29,16,2,7,20,13,22,24,26,34],[391,392,339]),([27,60,375],[0,34,16,2,7,20,22,15,24,28,29],[393,394,340]),([27,60,1391],[7,29,24,2,8,25,13,20],[330,341]),([27,60,1407],[7,34,24,2,8,27,15,22],[331,342]),([27,60,1663],[7,34,29,2,8,13,20,22,24,26,15],[395,332,343]),([27,76,95],[7,24,3,16,22,4,29,26,34,28],[396,397,398]),([27,76,111],[7,29,3,16,22,24,26,34],[399]),([27,76,127],[7,34,3,16,22,24,28,29],[400]),([27,76,343],[0,24,20,3,7,16,22,29,26,34,28],[344]),([27,76,359],[0,29,20,13,3,16,22,24,26,34],[401,402,345]),([27,76,375],[0,34,20,3,7,16,22,15,24,28,29],[403,404]),([27,76,1391],[7,29,24,3,25,13],[398,346]),([27,76,1407],[7,34,24,3,27,15,22],[347]),([27,76,1663],[7,34,29,3,13,16,22,24,26,15],[405,406,348]),([27,92,95],[7,24,5,16,20,29,26,6,34,28],[407,408,409]),([27,92,111],[7,29,5,16,20,24,26,34],[410]),([27,92,127],[7,34,5,16,20,24,28,29],[411]),([27,92,343],[0,24,22,5,7,16,20,29,26,34,28],[349]),([27,92,359],[0,29,22,5,7,16,20,13,24,26,34],[412,413]),([27,92,375],[0,34,22,15,5,16,20,24,28,29],[414,415,350]),([27,92,1391],[7,29,24,5,25,13,20],[351]),([27,92,1407],[7,34,24,5,27,15],[409,352]),([27,92,1663],[7,34,29,5,13,16,20,24,26,15],[416,417,353]),([27,108,27],[0,24,7,16,20,22,29,26,34,28],[]),([27,108,111],[7,29,11,25,0,13,16,20,22,34],[418]),([27,108,127],[7,34,11,27,0,15,16,20,22,29],[419]),([27,108,359],[0,29,24,13,11,16,20,22,34,26],[420,421,422]),([27,108,375],[0,34,24,15,11,16,20,22,29,28],[423,424,425]),([27,108,1663],[7,34,29,11,13,0,16,20,22,15],[426,427]),([27,110,382],[7,24,29,25,13,20],[]),([27,110,398],[7,24,34,27,15,22],[]),([27,120,359],[0,24,29,7,16,20,22,34,28],[]),([27,120,375],[0,34,29,7,16,20,22,15,24,28],[428]),([27,120,1663],[7,34,24,29,27,15,22],[]),([27,124,119],[7,34,12,32],[]),([27,124,359],[0,24,29,21,26,7,16,20,22,34,28],[]),([27,124,375],[0,34,29,15,33,16,20,22,24,28],[429]),([27,124,1663],[7,34,24,26,27,15,22],[])]
set_option maxRecDepth 100000 in
theorem v151_9_5 : ∀ e ∈ k151_9_5, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_5 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_6 : List Entry := [([27,126,134],[0,7,12,34,29,16,20,22,24,26],[]),([27,136,359],[0,24,34,7,16,20,22,29,26],[]),([27,136,375],[0,29,34,7,16,20,13,22,24,26],[430]),([27,136,1663],[7,29,24,34,25,13,20],[]),([27,140,119],[7,29,13,31,34,20,22,14],[]),([27,140,359],[0,24,34,23,28,7,16,20,22,29,26],[]),([27,140,375],[0,29,34,13,33,16,20,22,24,26],[431]),([27,140,1663],[7,29,24,25,13,20],[]),([27,142,134],[0,7,13,29,34,16,20,22,24,26,23],[]),([27,359,60],[0,7,16,20,22,29,26,34,28],[]),([27,359,61],[0,24],[354]),([27,375,60],[0,7,16,20,13,22,24,26,34,33,29],[401]),([27,375,108],[0,20,4,7,29,21,16,22,26,34,33],[401,355,391,412,421,430,431]),([27,375,158],[0,34,23,29,21],[356,392,402,413,422]),([27,391,60],[0,7,16,20,22,15,24,28,29,33,34],[414]),([27,391,124],[0,22,6,7,34,23,16,20,28,29,33],[414,357,393,403,424,428,429]),([27,391,158],[0,29,21,34,23],[358,394,404,415,425]),([27,1935,52],[7,34,29,21,0,16,22,26,15],[]),([27,1935,66],[0,16,29,21,34,23],[432,359,395,406,417,427]),([31,102,55],[7,11,16,24],[107,433]),([31,102,318],[7,24,11,0,16,20,22,26,28],[]),([31,103,590],[0,7,24],[]),([31,110,54],[0,7,24,16,20,22,29,26,34,28],[]),([31,110,112],[24,0,7,29,16,20,22,34,28],[]),([31,110,116],[24,0,7,21,26,16,20,22,34,28],[]),([31,110,128],[24,0,7,34,16,20,22,29,26],[]),([31,110,132],[24,0,7,23,28,16,20,22,29,26],[]),([31,118,92],[20,0,29,21,7,16,22,24,26,34,33],[109]),([31,118,142],[16,13,29,0,32,20,22,24,23,26],[]),([31,119,108],[20,29,0,16,22,24,26,34,33,7],[109,64]),([31,119,158],[0,29,34,23],[65]),([31,126,54],[0,7,29,16,20,22,24,26,34,33],[]),([31,126,134],[0,29,7,23,34,16,20,24,26],[]),([31,134,108],[22,0,34,23,7,16,20,24,28,29,33],[111]),([31,134,142],[16,15,29,34,0,31,20,22,24,21,26],[]),([31,135,124],[22,34,0,16,20,24,28,29,33,7],[111,66]),([31,135,158],[0,29,34,21],[67]),([31,142,54],[0,7,34,16,20,22,24,28,29,33],[]),([31,142,134],[0,29,34,21,16,22,24,26],[]),([31,358,55],[7,11,16,24],[115,434]),([31,358,63],[7,0,24,11],[435,35]),([31,358,318],[7,24,0,16,20,22,26,28,11],[435,120]),([31,359,78],[0,7,24],[17]),([31,359,590],[0,7,11],[120]),([31,366,48],[7,0,16,20,22,24,29,34,26],[]),([31,375,56],[0,7,29,16,20,22,24,12,26,34,33],[]),([31,375,78],[0,7,29],[24]),([31,375,108],[20,4,7,16,26,22,34,33],[82,36]),([31,375,158],[0,34,23],[83]),([31,391,56],[0,7,34,16,20,22,24,14,28,29,33],[])]
set_option maxRecDepth 100000 in
theorem v151_9_6 : ∀ e ∈ k151_9_6, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_6 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_7 : List Entry := [([31,391,78],[0,7,34],[31]),([31,391,124],[22,6,7,16,28,20,29,33],[84,37]),([31,391,158],[0,29,21],[85]),([31,639,64],[7,29,12,13,16,26,20],[95]),([31,639,66],[7,13],[95]),([31,639,68],[0,7,16,26],[]),([31,639,150],[7,29,32],[]),([31,655,64],[7,34,14,15,16,28,22],[99]),([31,655,66],[7,15],[99]),([31,655,68],[0,7,16,28],[]),([31,655,150],[7,34,31],[]),([31,1935,48],[29,0,21,30,16,22,24,26],[]),([31,1935,50],[16,13],[68]),([31,1935,52],[0,29,34,16,20,22,24,26],[436]),([31,1935,66],[0,16,13],[86]),([31,1935,86],[7,30,13,15],[]),([87,45,54],[0,24,16,20,22,26,28],[437,438,360]),([87,45,307],[0,24],[19,439,440]),([87,45,311],[0,11,16],[441,442]),([87,45,315],[0,24,20,22],[443,444,445,446,447,448,449,442,437,361]),([87,45,319],[0,24],[440,438,362]),([87,50,42],[7,24,16,1,20,22,29,26,34,28],[450]),([87,51,56],[24,7,16,26,28,20,22],[451,452,453,439]),([87,51,58],[7,24,16],[19,454,439,455]),([87,51,300],[7,24,16,26,28,20,22],[456,457,458,455,440]),([87,51,301],[7,24],[459,14,440,453,40]),([87,55,45],[7,16,11,24],[251]),([87,55,46],[7,24],[460,14,35,461]),([87,55,77],[24,11,16],[251,462,463,218]),([87,55,92],[16,7,24,20,22,29,26,34,28],[464,16,222,441,363,434,465]),([87,55,93],[16,7,11,24],[462,466,221]),([87,55,296],[7,11,16,26,28,20,22],[456,467,463,466,442]),([87,55,297],[7,24,11,16],[14,459,442,250]),([87,55,589],[7,11,16],[460,461,465]),([87,58,46],[7,0,24,16,20,22,29,26,34,28],[]),([87,58,60],[7,24,0,16,20,22,29,11,26,34,28],[]),([87,58,76],[7,16,8,24,20,22,29,26,34,28],[365,373]),([87,58,92],[7,9,24,16,22,29,26,34,28],[468,469,374]),([87,58,108],[7,10,24,16,20,29,26,34,28],[470,471,375]),([87,58,120],[7,29,24,16,20,22,34,28],[]),([87,58,124],[7,25,26,16,20,22,34,28],[]),([87,58,136],[7,34,24,16,20,22,29,26],[]),([87,58,140],[7,27,28,16,20,22,29,26],[]),([87,58,316],[7,11,16,20,22,29,26,34,28],[]),([87,59,62],[7,11,0],[376]),([87,59,92],[16,8,24,20,22,29,26,34,28],[443,367,377]),([87,59,108],[20,24,7,16,22,29,26,34,28],[472,473,444,368,378]),([87,59,124],[22,24,7,16,20,29,26,34,28],[474,475,445,369,379]),([87,59,136],[29,7,24,16,20,22,34,28],[446]),([87,59,140],[29,26,7,16,20,22,34,28],[447,476])]
set_option maxRecDepth 100000 in
theorem v151_9_7 : ∀ e ∈ k151_9_7, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_7 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_8 : List Entry := [([87,59,152],[34,7,24,16,20,22,29,26],[448]),([87,59,156],[34,28,7,16,20,22,29,26],[449,477]),([87,59,588],[7,11,26,28,16,20,22,29,34],[461,476,477]),([87,63,76],[0,11,16,20,22,26,28],[478,256]),([87,63,77],[24,11],[438,458,370]),([87,63,588],[7,24,11,26,28,16],[]),([87,63,589],[16,7,24,11],[371,435]),([87,574,47],[16,11],[479,480,481,482,483]),([87,574,52],[0,24,7,11,16,20,22,29,26,34,28],[484]),([87,574,54],[0,16,24,20,22,7,11,29,26,34,28],[485,486]),([95,50,42],[0,7,24,16,1,20,22,29,26,34,28],[487]),([95,51,384],[7,29,0,24,16,20,22,34,28],[]),([95,51,388],[7,21,26,0,16,20,22,34,28],[]),([95,51,400],[7,34,0,24,16,20,22,29,26],[]),([95,51,404],[7,23,28,0,16,20,22,29,26],[]),([95,55,384],[29,0,24,16,20,22,34,28],[]),([95,55,388],[21,29,26,0,16,20,22,34,28],[]),([95,55,400],[34,0,24,16,20,22,29,26],[]),([95,55,404],[23,34,28,0,16,20,22,29,26],[]),([95,58,76],[7,0,16,24,20,22,29,2,34,26],[]),([95,58,92],[7,0,20,24,16,22,29,3,34,26],[]),([95,58,108],[7,0,22,24,16,20,29,5,34,26],[]),([95,58,120],[7,0,24,16,20,22,29],[]),([95,58,124],[7,0,24,16,20,22,34,26],[]),([95,58,136],[7,0,24,16,20,22,29,34],[]),([95,58,140],[7,0,24,16,20,22,29,26],[]),([95,113,384],[29,0,34,24,16,20,22],[]),([95,113,388],[29,0,24,23,28,16,20,22],[]),([95,117,384],[34,0,24,21,26,16,20,22],[]),([95,117,388],[21,29,26,0,23,28,16,20,22],[]),([343,58,76],[7,16,24,20,22,29,26,34,28],[]),([343,58,77],[7,16,24,20,22,29,26,34,28],[]),([351,59,29],[16,11,24],[488,489,490,491,492]),([351,59,60],[7,24,26,28,11,16],[14,493,461]),([351,59,61],[7,16,11],[494,495]),([351,59,77],[24,11,16],[494,496]),([351,59,92],[16,11,20,22,29,26,34,28,24],[497,498,16,492,465]),([351,59,93],[16,11,24],[492,495,496]),([351,63,52],[24,0,26,28,11,16,20,22],[499,479]),([351,63,53],[16,7,11],[500,501,502,503,504]),([351,63,69],[16,24,11],[500,505,506,507,508]),([351,63,128],[29,11,0,16,20,22,34,28,24],[488,480]),([351,63,129],[16,26,11,24],[488,501,505,509,510]),([351,63,132],[11,21,26,0,16,20,22,34,28],[489,481]),([351,63,133],[16,29,11,24],[489,502,506,511,512]),([351,63,144],[34,11,0,16,20,22,29,26,24],[490,482]),([351,63,145],[16,28,11,24],[490,503,507,509,511]),([351,63,148],[11,23,28,0,16,20,22,29,26],[491,483]),([351,63,149],[16,34,11,24],[491,504,508,510,512]),([367,54,136],[34,7,0,29,16,20,22,24,26],[382])]
set_option maxRecDepth 100000 in
theorem v151_9_8 : ∀ e ∈ k151_9_8, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_8 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def k151_9_9 : List Entry := [([367,54,137],[0,16,33,7,29,21,22,24,26,12],[]),([367,54,140],[34,0,21,7,33,29,16,22,24,26],[383]),([367,54,141],[0,34,16,7,29,21,22,24,26,12],[]),([383,54,136],[29,7,0,34,16,20,22,24,28],[384]),([383,54,137],[0,16,33,7,34,23,20,24,28,14],[]),([383,54,140],[29,0,21,7,33,34,16,20,22,24,28],[385]),([383,54,141],[0,29,16,7,34,23,20,24,28,14],[]),([1663,50,74],[7,16,21,29,34,22,26],[513,514,515,390]),([1663,50,78],[16,30,21,7,22,24,26],[89,388]),([1663,54,74],[7,16,0,29,34,20,22,24,26],[516]),([1663,54,78],[16,0,7,21,34,22,24,26,29,23],[]),([1663,66,74],[7,29,34,16,20,22,24,26],[]),([1663,66,78],[7,29,34,16,20,22,24,26],[]),([1663,70,74],[16,13,30,20,22,24,26],[]),([1663,70,78],[16,13,30,20,22,21,26,15],[517])]
set_option maxRecDepth 100000 in
theorem v151_9_9 : ∀ e ∈ k151_9_9, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := level_sound hR151 9 k151_9_9 (D151_8.map (wsOf c151.2)) (map_dead w151_8) (by decide +kernel)
def D151_9 : List Entry := k151_9_0 ++ (k151_9_1 ++ (k151_9_2 ++ (k151_9_3 ++ (k151_9_4 ++ (k151_9_5 ++ (k151_9_6 ++ (k151_9_7 ++ (k151_9_8 ++ (k151_9_9)))))))))
theorem w151_9 : ∀ e ∈ D151_9, ¬ Live516.live basicOps goal 9 (wsOf c151.2 e).toFinset := (app_dead v151_9_0 (app_dead v151_9_1 (app_dead v151_9_2 (app_dead v151_9_3 (app_dead v151_9_4 (app_dead v151_9_5 (app_dead v151_9_6 (app_dead v151_9_7 (app_dead v151_9_8 v151_9_9)))))))))
def k151_10_0 : List Entry := [([19,26],[7,0,16,20,22,24,29,34],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]),([19,110],[7,24,11,16,20,22,29,26,34,28],[2,22]),([19,126],[7,29,26,16,20,22,34,33],[23]),([19,142],[7,34,28,16,20,22,29,33],[24]),([19,300],[7,16,20,22,24,0,29,34],[25,26,27,28,29,30,31,32]),([19,301],[0,7,16,20,22,24,29,34],[33,34,35,36,37,38,39]),([19,359],[7,24,0,16,20,22,29,26,34,28],[2,40,41,42,14,15,34,22]),([19,367],[7,0,24,16,20,22,29,26,34,28],[43,44,45,46,47,16]),([19,375],[7,29,0,26,16,20,22,34,33],[48,49,50,17,35]),([19,383],[7,0,29,16,20,22,24,26,34,33],[51,52]),([19,391],[7,34,0,28,16,20,22,29,33],[53,54,55,18,36]),([19,399],[7,0,34,16,20,22,24,28,29,33],[56,57]),([19,1663],[7,29,24,25,21,16,22,34,28],[19,30,37]),([19,1679],[7,34,24,27,23,16,20,29,26],[20,31,38]),([19,1935],[7,34,29,13,21,16,22,24,26,15],[58,59,60,21,32,39]),([23,45],[0,7,16,20,22,24,29,34],[61,62,63,64,65,66,67,68,69,70,71]),([23,46],[7,0,16,20,22,24,29,34],[72,73,74,75,76,77,78]),([23,47],[7,0,16,20,22,24,29,34,1],[79,80,81,82,83,84,85,86,87,88,89,90,91,92]),([23,60],[16,7,20,22,24,29,34],[93,94,95,96,97,98,99,1,82,100,101,102,103,104,105,106,107,108,109,110,111]),([23,61],[16,7,1,20,22,24,29,34],[112,113,114,115,61,82,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137]),([23,102],[7,16,24,11,20,22,29,26,34,28],[138,139,140,141,142,143,3,83]),([23,103],[16,24,11,20,22,29,26,34,28],[144,145,146,147,148,149,138,62,83,116,117,150,151]),([23,110],[16,24,7,20,22,29,26,34,28],[138,152,153,154,155,5,84]),([23,111],[16,24,7,20,22,29,26,34,28,1],[144,156,138,63,84,118,157,158,159,160,161]),([23,118],[7,16,21,20,22,24,26,34,33],[162,163,164,165,166,7,85]),([23,119],[16,29,21,20,22,24,26,34,7,33],[167,168,169,170,171,172,173,64,85,119,120,174,175]),([23,126],[16,21,29,22,24,26,34,7,33],[176,9,86]),([23,127],[16,29,21,22,24,26,34,7,1,33],[177,65,86,121,178,179]),([23,134],[7,16,23,20,22,24,28,29,33],[180,181,182,183,184,11,87]),([23,135],[16,34,23,20,22,24,28,29,7,33],[185,186,187,188,189,190,191,66,87,122,123,192,193]),([23,142],[16,23,34,20,24,28,29,7,33],[194,13,88]),([23,143],[16,34,23,20,24,28,29,7,1,33],[195,67,88,124,196,197]),([23,296],[0,7,16,20,22,24,29,34],[25,198,199,125,150,160,174,178,192,196,200,201,202]),([23,297],[0,7,16,20,22,24,29,34],[33,203,204,205,206,207,208,209,126,151,161,175,179,193,197,210,211,212]),([23,358],[7,16,24,20,22,29,26,34,28],[213,214,215,216,217,218,157,219,68,75,92,127]),([23,359],[16,24,0,7,20,22,29,26,34,28],[3,220,221,145,222,147,213,207,68,92,154,158,223,100,128]),([23,366],[16,24,11,0,20,22,29,26,34,28],[213,224,225,226,227,228,129]),([23,367],[16,0,24,11,20,22,29,26,34,28,1],[229,230,231,232,233,213,101]),([23,375],[16,29,0,7,21,20,22,24,26,34,33],[234,169,170,235,236,208,102,130]),([23,383],[16,0,29,7,20,22,24,26,34,1,33],[237,238,239,240,103]),([23,391],[16,34,0,7,23,20,22,24,28,29,33],[241,187,188,242,243,209,104,131]),([23,399],[16,0,34,7,20,22,24,28,29,1,33],[244,245,246,247,105]),([23,623],[7,24,11,16,20,22,29,26,34,28],[152,156,3,89,155,159,219,223,106,132]),([23,639],[7,29,21,16,22,24,26,34,33],[167,168,248,249,250,90,107,133]),([23,655],[7,34,23,16,20,24,28,29,33],[185,186,251,252,253,91,108,134]),([23,1663],[16,29,24,25,21,7,22,34,28],[69,76,109,135,200,210]),([23,1679],[16,34,24,27,23,7,20,29,26],[70,77,110,136,201,211]),([23,1935],[16,34,29,21,7,22,24,26,23],[254,255,256,257,258,259,260,71,78,111,137,202,212]),([27,60],[16,0,7,20,22,24,2,8,29,34],[199,204,261,262,263,264,265,266]),([27,76],[20,0,7,16,22,24,3,29,34],[267,268,269,205,270,271,272,273,274,275])]
set_option maxRecDepth 100000 in
theorem v151_10_0 : ∀ e ∈ k151_10_0, ¬ Live516.live basicOps goal 10 (wsOf c151.2 e).toFinset := level_sound hR151 10 k151_10_0 (D151_9.map (wsOf c151.2)) (map_dead w151_9) (by decide +kernel)
def k151_10_1 : List Entry := [([27,92],[22,0,7,16,20,24,5,29,34],[276,277,278,206,279,280,281,282,283,284]),([27,104],[24,7,16,20,22,29,21,34,23],[]),([27,108],[24,0,7,16,20,22,29,11,34],[285,286,287,288,289,290]),([27,110],[7,24,0,16,20,22,29,11,26,34,28],[285,291,292]),([27,120],[29,7,16,20,22,24,0,34],[293,294,295]),([27,124],[29,0,21,7,16,22,24,26,34,20],[296,297,298,299]),([27,126],[7,29,0,16,20,22,24,26,34,33],[300]),([27,136],[34,7,16,20,22,24,0,29],[301,302,303]),([27,140],[34,0,23,7,16,20,24,28,29,22],[304,305,306,307]),([27,142],[7,34,0,16,20,22,24,28,29,33],[308]),([27,359],[0,24,7,16,20,22,29,26,34,28],[309,310,75,207,285,261,270,279,293,297,301,305]),([27,375],[0,29,13,16,20,22,24,26,34,33],[311,312,313,208,262,271,280,288,302,306]),([27,391],[0,34,15,16,20,22,24,28,29,33],[314,315,316,209,263,272,281,289,294,298]),([27,1663],[7,29,24,25,21,16,22,34,28],[291,76,264,273,282,303,307,200,210]),([27,1679],[7,34,24,27,23,16,20,29,26],[292,77,265,274,283,295,299,201,211]),([27,1935],[7,34,29,13,21,0,16,22,24,26,23],[317,318,78,266,275,284,290,202,212]),([31,102],[0,16,24,20,22,29,26,34,28,7],[2,319,320,79]),([31,103],[16,24,0,20,22,29,26,34,28,7],[83,79,321,27]),([31,110],[16,0,24,20,22,29,26,34,28],[322,323,324,325,326]),([31,118],[0,16,29,21,20,22,24,26,34,7,33],[327,328,80]),([31,119],[16,29,0,21,20,22,24,26,34,33,7],[329,330,80,28]),([31,126],[16,0,29,20,22,24,26,34,7,33],[331,332]),([31,134],[0,16,34,23,20,22,24,28,29,7,33],[333,334,81]),([31,135],[16,34,0,23,20,22,24,28,29,33,7],[335,336,81,29]),([31,142],[16,0,34,20,22,24,28,29,7,33],[337,338]),([31,358],[0,16,11,20,22,29,26,34,28,24],[339,340,341,68,14,92]),([31,359],[16,24,0,11,20,22,29,26,34,28],[83,342,34,68,92,343,15]),([31,366],[0,24,7,16,26,28,20,22,29,34],[344,16]),([31,375],[0,29,21,7,16,20,22,24,26,34,33],[345,346,347,348,35,17]),([31,391],[0,34,23,7,16,20,22,24,28,29,33],[349,350,351,352,36,18]),([31,623],[7,24,11,0,16,20,22,29,26,34,28],[2,83,89,320,321,341,343]),([31,639],[7,29,21,0,16,22,24,26,34,33],[353,354,355,356,90]),([31,655],[7,34,23,0,16,20,24,28,29,33],[357,358,359,360,91]),([31,1663],[16,29,24,25,21,7,22,34,28],[69,19,30,37]),([31,1679],[16,34,24,27,23,7,20,29,26],[70,20,31,38]),([31,1935],[16,34,29,21,0,7,22,24,26,23],[361,362,363,364,365,71,21,32,39]),([87,45],[0,24,16,20,22,29,26,34,28],[366,367,368,369,370,213]),([87,50],[7,16,24,20,22,29,26,34,28],[371]),([87,51],[7,16,24,20,22,29,26,34,28],[2,40,372,373,22,374,375,367]),([87,55],[16,7,11,24,20,22,29,26,34,28],[376,377,154,378,379,380,381,382,139,141,368,214,339,383]),([87,58],[7,16,24,20,22,29,26,34,28],[384,385,386,387,388,389,390,391,392,215,220,393]),([87,59],[7,16,24,20,22,29,26,34,28],[140,377,75,394,285,395,396,397,398,399,400,401,381,382,369,216,221,402]),([87,62],[16,24,7,20,22,29,26,34,28],[139,2,141,41,145,147,342]),([87,63],[16,7,24,20,22,29,26,34,28],[376,40,403,404,374,375,139,141,370,42,217,218,222,340,405,406]),([87,574],[16,24,7,11,20,22,29,26,34,28],[385,285,383,403,407,408,409,393,402,405,406,219,223,341,343]),([95,50],[7,16,24,20,22,29,26,34,28,0],[410,344]),([95,51],[7,0,24,16,20,22,29,26,34,28],[322,16,411,412,413,414]),([95,54],[0,16,24,7,20,22,29,26,34,28],[229,366]),([95,55],[16,7,0,24,20,22,29,26,34,28],[366,415,416,417,418,224]),([95,58],[0,7,16,24,20,22,29,26,34,28],[385,419,420,421,422,423,424,425])]
set_option maxRecDepth 100000 in
theorem v151_10_1 : ∀ e ∈ k151_10_1, ¬ Live516.live basicOps goal 10 (wsOf c151.2 e).toFinset := level_sound hR151 10 k151_10_1 (D151_9.map (wsOf c151.2)) (map_dead w151_9) (by decide +kernel)
def k151_10_2 : List Entry := [([95,112],[24,29,0,16,20,22,34,28],[44,230]),([95,113],[16,26,0,24,29,20,22,34,28],[411,415,426,427,225]),([95,116],[24,29,21,26,0,16,20,22,34,28],[45,231]),([95,117],[16,29,24,21,26,0,20,22,34,28],[412,416,428,429,226]),([95,128],[24,34,0,16,20,22,29,26],[46,232]),([95,129],[16,28,0,24,34,20,22,29,26],[413,417,426,428,227]),([95,132],[24,34,23,28,0,16,20,22,29,26],[47,233]),([95,133],[16,34,24,23,28,0,20,22,29,26],[414,418,427,429,228]),([103,58],[7,16,29,21,22,24,26,34,33],[384,234]),([103,62],[16,21,29,7,22,24,26,34,33],[48,169,170,346]),([103,92],[20,29,21,16,22,24,26,34,33],[49,235,312,347]),([103,142],[16,21,29,34,32,23,24,26],[50,236,313,348]),([111,50],[7,16,0,29,20,22,24,26,34,33],[410]),([111,54],[0,16,29,7,20,22,24,26,34,33],[239]),([111,134],[0,16,29,34,23,32,20,24,26],[52,240]),([119,58],[7,16,34,23,20,24,28,29,33],[384,241]),([119,62],[16,23,34,7,20,24,28,29,33],[53,187,188,350]),([119,108],[22,34,23,16,20,24,28,29,33],[54,242,315,351]),([119,142],[16,21,29,31,22,24,26],[55,243,316,352]),([127,50],[7,16,0,34,20,22,24,28,29,33],[410]),([127,54],[0,16,34,7,20,22,24,28,29,33],[246]),([127,134],[0,16,29,34,21,31,22,24,26],[57,247]),([343,58],[7,24,16,20,22,29,26,34,28],[430,431]),([343,62],[7,24,16,20,22,29,26,34,28],[]),([351,50],[16,11,20,22,29,26,34,28],[2]),([351,54],[7,16,11,20,22,29,26,34,28],[152,385,408,409]),([351,59],[7,16,11,20,22,29,26,34,28,24],[152,432,433,434,155,435,436,437,383]),([351,63],[16,11,20,22,29,26,34,28,24],[2,432,438,439,320,440,441,442,443,444,445,446,447,448,407]),([359,58],[7,29,16,20,22,24,26,34,33],[]),([359,62],[7,29,16,20,22,24,26,34,33],[]),([359,92],[7,20,29,9,21,16,22,24,26,34,33],[]),([359,142],[7,29,32,23,26,16,20],[]),([367,50],[16,21,7,29,22,24,26,34,33],[167,168,353,354]),([367,54],[7,16,21,29,22,24,26,34,33,0],[449,450,451,452,248,249,355]),([367,134],[7,16,21,29,23,32,26],[250,356]),([375,58],[7,34,16,20,22,24,28,29,33],[]),([375,62],[7,34,16,20,22,24,28,29,33],[]),([375,108],[7,22,34,10,23,16,20,24,28,29,33],[]),([375,142],[7,29,34,31,21,26,16,22],[]),([383,50],[16,23,7,34,20,24,28,29,33],[185,186,357,358]),([383,54],[7,16,23,34,20,24,28,29,33,0],[453,454,455,456,251,252,359]),([383,134],[7,16,21,29,31,22,26,34],[253,360]),([1663,50],[16,21,29,34,30,22,24,26],[457,458,59,258,318,364]),([1663,54],[16,21,29,34,30,22,24,26,23,0],[459,460,60,259]),([1663,66],[7,16,29,34,20,22,24,26],[461,462]),([1663,70],[7,16,21,29,30,22,24,26,23],[463,464,260,365])]
set_option maxRecDepth 100000 in
theorem v151_10_2 : ∀ e ∈ k151_10_2, ¬ Live516.live basicOps goal 10 (wsOf c151.2 e).toFinset := level_sound hR151 10 k151_10_2 (D151_9.map (wsOf c151.2)) (map_dead w151_9) (by decide +kernel)
def D151_10 : List Entry := k151_10_0 ++ (k151_10_1 ++ (k151_10_2))
theorem w151_10 : ∀ e ∈ D151_10, ¬ Live516.live basicOps goal 10 (wsOf c151.2 e).toFinset := (app_dead v151_10_0 (app_dead v151_10_1 v151_10_2))
def k151_11_0 : List Entry := [([19],[7,16,20,22,24,29,34],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]),([23],[16,7,20,22,24,29,34],[15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47]),([27],[7,16,20,22,24,29,34,0],[16,48,49,50,51,52,53,54,55,56,57,58,59,32,33,60,61,62,63,64,65]),([31],[16,7,20,22,24,0,29,34],[15,0,17,66,67,68,69,70,71,72,73,74,4,5,75,76,77,78,79,80,81,82,83,84,85]),([87],[16,24,20,22,29,26,34,28],[86,87,88,20,89,90,91,92,93,6,34,35,60,75,76,94]),([95],[16,24,0,20,22,29,26,34,28],[86,95,96,97,98,99,68,100,101,102,103,104,105,106,107,7,36,37,77]),([103],[16,29,21,20,22,24,26,34,33],[108,109,110,111,8,38,61,78]),([111],[16,29,21,22,24,26,34,0,33],[112,113,114,9,39]),([119],[16,34,23,20,22,24,28,29,33],[115,116,117,118,10,40,62,79]),([127],[16,34,23,20,24,28,29,0,33],[119,120,121,11,41]),([343],[7,16,24,20,22,29,26,34,28],[122,123]),([351],[16,24,7,11,20,22,29,26,34,28],[124,125,20,126,68,127,42,80,94]),([359],[7,16,29,20,22,24,26,34,33],[128,129,130,131]),([367],[16,29,7,21,22,24,26,34,33],[132,133,134,43,81]),([375],[7,16,34,20,22,24,28,29,33],[135,136,137,138]),([383],[16,34,7,23,20,24,28,29,33],[139,140,141,44,82]),([1391],[16,29,24,25,21,22,34,28],[12,45,63,83]),([1407],[16,34,24,27,23,20,29,26],[13,46,64,84]),([1663],[16,34,29,21,22,24,26,23],[142,143,144,145,14,47,65,85])]
set_option maxRecDepth 100000 in
theorem v151_11_0 : ∀ e ∈ k151_11_0, ¬ Live516.live basicOps goal 11 (wsOf c151.2 e).toFinset := level_sound hR151 11 k151_11_0 (D151_10.map (wsOf c151.2)) (map_dead w151_10) (by decide +kernel)
def D151_11 : List Entry := k151_11_0
theorem w151_11 : ∀ e ∈ D151_11, ¬ Live516.live basicOps goal 11 (wsOf c151.2 e).toFinset := v151_11_0
def k151_12_0 : List Entry := [([],[16,20,22,24,29,34],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18])]
set_option maxRecDepth 100000 in
theorem v151_12_0 : ∀ e ∈ k151_12_0, ¬ Live516.live basicOps goal 12 (wsOf c151.2 e).toFinset := level_sound hR151 12 k151_12_0 (D151_11.map (wsOf c151.2)) (map_dead w151_11) (by decide +kernel)
def D151_12 : List Entry := k151_12_0
theorem w151_12 : ∀ e ∈ D151_12, ¬ Live516.live basicOps goal 12 (wsOf c151.2 e).toFinset := v151_12_0
theorem g151 : GoodC c151 := claim_sound2 D151_12 c151 w151_12 (by decide +kernel)

end Check516

end PEqualNP.Outside.L_meta_8519

theorem PEqualNP.Outside.L_meta_8519 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)) t → 13 ≤ t :=
  fun t h => PEqualNP.Outside.L_meta_8519.Check516.final_bound 12 PEqualNP.Outside.L_meta_8519.Check516.g151 t h
