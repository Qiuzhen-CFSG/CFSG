module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.Evaluation
/-!
# Bounded certificates for the Fi23 fixed-letter calculation

Each decoded generator block is certified separately as a list of distinct
letters with an exact support bit mask. Disjoint masks combine these certificates
without reducing the full generator table in one computation. On a selected
cycle the inverse product has the action of that cycle; outside the support it
fixes the letter. These facts verify the generator edges of the ten word traces.

Source: ATLAS F23G1-p31671B0; application: GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck
variable {n : Nat}
def mask : List (Fin n) → Nat
  | [] => 0
  | x :: xs => (2 ^ x.val) ||| mask xs

theorem mask_spec (xs : List (Fin n)) (x : Fin n) :
    (mask xs).testBit x.val = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [mask]
  | cons a xs ih =>
    simp only [mask, Nat.testBit_or, Bool.or_eq_true, List.mem_cons, ← ih]
    simp only [Nat.testBit_two_pow, decide_eq_true_eq]
    exact or_congr ⟨fun h => Fin.ext h.symm, fun h => congrArg Fin.val h.symm⟩ Iff.rfl

structure Certificate (xs : List (Fin n)) (m : Nat) : Prop where
  nodup : xs.Nodup
  mem_iff : ∀ x, x ∈ xs ↔ m.testBit x.val = true

theorem certify (xs : List (Fin n)) (m : Nat)
    (hd : AtlasCarriers.checkFreshPoints xs 0 = true) (hm : mask xs = m) :
    Certificate xs m :=
  ⟨AtlasCarriers.nodup_of_checkFreshPoints xs hd, fun x => hm ▸ (mask_spec xs x).symm⟩

theorem Certificate.append {xs ys : List (Fin n)} {a b : Nat}
    (ha : Certificate xs a) (hb : Certificate ys b) (hab : a &&& b = 0) :
    Certificate (xs ++ ys) (a ||| b) := by
  constructor
  · apply List.nodup_append'.mpr
    refine ⟨ha.nodup, hb.nodup, List.disjoint_left.mpr ?_⟩
    intro x hx hy
    have h := congrArg (fun m => m.testBit x.val) hab
    rw [Nat.testBit_and, (ha.mem_iff x).mp hx, (hb.mem_iff x).mp hy] at h
    simp at h
  · intro x
    rw [List.mem_append, ha.mem_iff, hb.mem_iff, Nat.testBit_or, Bool.or_eq_true]

def unionMasks : List Nat → Nat
  | [] => 0
  | m :: ms => m ||| unionMasks ms

def disjointMasks : List Nat → Bool
  | [] => true
  | m :: ms => (m &&& unionMasks ms == 0) && disjointMasks ms

theorem certify_blocks (blocks : List (List (List (Fin n)))) (ms : List Nat)
    (hc : List.Forall₂ (fun cs m => Certificate cs.flatten m) blocks ms)
    (hd : disjointMasks ms = true) :
    Certificate blocks.flatten.flatten (unionMasks ms) := by
  induction hc with
  | nil => exact ⟨by simp, by simp [unionMasks]⟩
  | @cons cs m blocks ms hcs hrest ih =>
    have h : m &&& unionMasks ms = 0 ∧ disjointMasks ms = true := by
      simpa only [disjointMasks, Bool.and_eq_true, beq_iff_eq] using hd
    simpa only [List.flatten_cons, List.flatten_append, unionMasks] using
      hcs.append (ih h.2) h.1

theorem cyclesInv_on_cycle {α : Type*} [DecidableEq α]
    (cs : List (List α)) (hd : cs.flatten.Nodup) (c : List α) (hc : c ∈ cs)
    (x : α) (hx : x ∈ c) : cyclesInv cs x = cycleInv c x := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    obtain ⟨_, hcs, hdisj⟩ := List.nodup_append'.mp
      (show (a ++ cs.flatten).Nodup from hd)
    rcases List.mem_cons.mp hc with rfl | hc
    · have hy : cycleInv c x ∈ c := by
        rw [cycleInv_eq]
        apply List.mem_of_formPerm_apply_mem
        simpa using hx
      exact cyclesInv_of_notMem cs (cycleInv c x)
        (fun h => List.disjoint_left.mp hdisj hy h)
    · have hxa : x ∉ a := fun h => List.disjoint_left.mp hdisj h
        (List.mem_flatten.mpr ⟨c, hc, hx⟩)
      simpa only [cyclesInv, List.foldl_cons, cycleInv_of_notMem hxa] using
        ih hcs hc

theorem cyclesInv_edge {cs : List (List (Fin n))} {m : Nat}
    (h : Certificate cs.flatten m) (c : List (Fin n)) (hc : c ∈ cs)
    (x y : Fin n) (hx : x ∈ c) (he : cycleInv c x = y) : cyclesInv cs x = y :=
  (cyclesInv_on_cycle cs h.nodup c hc x hx).trans he

theorem cyclesInv_fixed {cs : List (List (Fin n))} {m : Nat}
    (h : Certificate cs.flatten m) (x : Fin n) (hx : m.testBit x.val = false) :
    cyclesInv cs x = x := by
  apply cyclesInv_of_notMem
  intro hmem
  have := (h.mem_iff x).mp hmem
  simp [hx] at this
end Sporadic.Fischer.Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck
