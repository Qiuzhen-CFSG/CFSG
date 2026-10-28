module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Frattini
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup

/-!
# Literal core pullback in the symplectic Frattini branch

The native Frattini theorem applies both before and after characteristic
replacement. Pulling its conclusion back through the specified free-amalgam
embedding identifies precisely the original intrinsic component core.
The central-layer identity is supplied by the native (3.2) producer; the
Frattini inclusion selects the first branch of MS93 (3.6), printed p.870.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- The Frattini branch identifies the original component core, through the
literal free-amalgam embedding, with the moving Z-layer. -/
theorem original_core_eq_moving_of_frattini
    (hX : ⁅X R (alpha R),Ltilde R (alpha R)⁆ = U R (alpha R))
    (hsmall : core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    (blockU L).map L.subtype = (U R (alpha R)).comap (embedM R) := by
  rw [←s.original_core_pullback,
    s.core_eq_U_of_le_frattini_sup (alpha R) rfl hX hsmall]

/-- The same branch on the characteristic replacement identifies exactly the
original intrinsic component core, with neither coordinate map changed. -/
theorem reduced_core_eq_moving_of_frattini (c : CharacteristicReduction L R)
    (hX : ⁅X c.radical (alpha c.radical),Ltilde c.radical (alpha c.radical)⁆ =
      U c.radical (alpha c.radical))
    (hsmall : core c.radical (alpha c.radical) ≤
      (frattini (Q c.radical (alpha c.radical))).map
        (Q c.radical (alpha c.radical)).subtype ⊔ X c.radical (alpha c.radical)) :
    (blockU L).map L.subtype =
      ((U c.radical (alpha c.radical)).comap (embedM c.radical)).map c.overgroup.subtype := by
  change (⁅pCore 2 L,(⊤ : Subgroup L)⁆).map L.subtype = _
  rw [←s.reduced_core_pullback_internal c,
    (s.reduce c).core_eq_U_of_le_frattini_sup (alpha c.radical) rfl hX hsmall]

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
