module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.ShortWords
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.ConjugacyReplay

/-!
# Remaining branches of the max8 local identities

The quartic relation and the six mixed words are independent source obligations.
The replay consumer below connects a checked conjugacy to the exact quartic
word, including its original signed subgroup expansion. No concrete trace or
remaining relation is asserted here. Source: ATLAS M24G1-P1 and M24G1-max8W1;
see `../source/README.md` and the local `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations
open Subgroup.CosetWordCertificate

/-- The one remaining power word, at the fixed local index two. -/
def QuarticRelation : Prop := eval boundGenerator (localRelatorLetters 2) = 1

/-- All six non-power words, retaining their fixed local indices three through eight. -/
def MixedRelations : Prop :=
  ∀ i : Fin 6, eval boundGenerator (localRelatorLetters ⟨i.val + 3, by omega⟩) = 1

/-- Half of the fixed quartic word expanded in the original signed source alphabet. -/
def quarticHalfLetters : Word (Fin 2) :=
  Replay.expand boundLetters ((localRelatorLetters 2).take 8)

/-- A checked source conjugacy with a proved square-one endpoint establishes
precisely the missing quartic relation on the literal subgroup generators. -/
theorem quartic_relation_of_checked_conjugacy (db : Replay.Database) (n : Nat)
    (cs : List PowerReplay.Command) (v : Word (Fin 2))
    (hdb : Replay.ValidBefore generator db n)
    (hb : cs.all (PowerReplay.Command.before n) = true)
    (hc : PowerReplay.run db quarticHalfLetters cs = some v)
    (hv : eval generator v ^ 2 = 1) : QuarticRelation := by
  have hp : eval generator quarticHalfLetters ^ 2 = 1 :=
    PowerReplay.run_prefix_power generator db n quarticHalfLetters v cs 2 hdb hb hc hv
  have hg : (fun s => eval generator (boundLetters s)) = boundGenerator :=
    funext (eval_boundLetters generator)
  rw [quarticHalfLetters, Replay.eval_expand, hg] at hp
  have hw : localRelatorLetters 2 =
      (localRelatorLetters 2).take 8 ++ (localRelatorLetters 2).take 8 := by decide +kernel
  unfold QuarticRelation
  rw [hw, eval_append, ← pow_two]
  exact hp

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations
