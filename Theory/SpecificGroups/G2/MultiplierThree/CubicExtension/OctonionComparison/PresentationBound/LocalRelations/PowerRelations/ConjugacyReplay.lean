module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.WordCalculus

/-!
# Replaying conjugations and source-word substitutions

A source-word equality preserves every power identity. Conjugation does too.
This checker combines the two operations, so a recorded path to the original
involution certifies that its starting word has square one. The concrete power
certificates use only the six ATLAS G23G1-P1 source relators.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.PowerReplay
open Subgroup.CosetWordCertificate Replay

inductive Command where
  | rewrite (step : Nat × Nat)
  | conjugate (letter : Letter Bool)

def step (db : Database) (w : Word Bool) : Command → Option (Word Bool)
  | .rewrite s => rewriteAt db w s
  | .conjugate a => some ([(a.1, !a.2)] ++ w ++ [a])

def run (db : Database) : Word Bool → List Command → Option (Word Bool)
  | w, [] => some w
  | w, c :: cs => (step db w c).bind fun v => run db v cs

def Command.Valid {G : Type*} [Group G] (g : Bool → G) (db : Database) : Command → Prop
  | .rewrite s => eval g (db s.1).1 = eval g (db s.1).2
  | .conjugate _ => True

theorem step_power {G : Type*} [Group G] (g : Bool → G) (db : Database)
    (w v : Word Bool) (c : Command) (n : Nat)
    (hc : c.Valid g db) (hs : step db w c = some v)
    (hv : eval g v ^ n = 1) : eval g w ^ n = 1 := by
  cases c with
  | rewrite s =>
      rw [rewriteAt_sound g db w s hc hs]
      exact hv
  | conjugate a =>
      cases hs
      have he : eval g ([(a.1, !a.2)] ++ w ++ [a]) =
          (eval g [a])⁻¹ * eval g w * eval g [a] := by
        cases a with
        | mk a sign => cases sign <;> simp [eval_cons, eval_append, mul_assoc]
      rw [he] at hv
      have hp : ((eval g [a])⁻¹ * eval g w * eval g [a]) ^ n =
          (eval g [a])⁻¹ * eval g w ^ n * eval g [a] := by
        simpa only [inv_inv] using
          (conj_pow (a := (eval g [a])⁻¹) (b := eval g w) (i := n))
      rw [hp] at hv
      have hh := congrArg (fun z => eval g [a] * z * (eval g [a])⁻¹) hv
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one, one_mul] using hh

theorem run_power {G : Type*} [Group G] (g : Bool → G) (db : Database)
    (w v : Word Bool) (cs : List Command) (n : Nat)
    (hs : ∀ c ∈ cs, c.Valid g db) (hc : run db w cs = some v)
    (hv : eval g v ^ n = 1) : eval g w ^ n = 1 := by
  induction cs generalizing w with
  | nil => cases hc; exact hv
  | cons c cs ih =>
      simp only [run, Option.bind_eq_some_iff] at hc
      obtain ⟨u, hu, hv'⟩ := hc
      exact step_power g db w u c n (hs _ (List.mem_cons_self ..)) hu
        (ih u (fun d hd => hs d (List.mem_cons_of_mem _ hd)) hv')

def Command.before (bound : Nat) : Command → Bool
  | .rewrite s => decide (s.1 < bound)
  | .conjugate _ => true

theorem run_prefix_power {G : Type*} [Group G] (g : Bool → G) (db : Database)
    (bound : Nat) (w v : Word Bool) (cs : List Command) (n : Nat)
    (hs : ValidBefore g db bound)
    (hb : cs.all (Command.before bound) = true)
    (hc : run db w cs = some v) (hv : eval g v ^ n = 1) : eval g w ^ n = 1 := by
  apply run_power g db w v cs n _ hc hv
  intro c hmem
  have hh := List.all_eq_true.mp hb c hmem
  cases c with
  | rewrite s => exact hs s.1 (of_decide_eq_true hh)
  | conjugate _ => trivial

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.PowerReplay
