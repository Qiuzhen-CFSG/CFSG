module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Tits

/-!
# Rigidity of the Tits and full binary Ree inclusion amalgams

For the actual Tits inclusion amalgam, each endpoint has at least 4096
restrictions to the Sylow overlap. Its automorphism group has order at most
8192, and the restriction intersection has order 2048. The resulting product
is the whole automorphism group, so every overlap twist can be removed.

For the full binary Ree model, the first restriction group has index at most
two and a proved second restriction lies outside it. This likewise removes
every twist, independently of the Tits calculation. Sylow normalization then
upgrades arbitrary parabolic equivalences to compatible amalgam isomorphisms.
Neither recognition result needs faithfulness or an extra finite-model premise.
The final application uses the actual full automorphism-group identification,
retaining both inclusion squares.

Source: Aschbacher--Smith F.1.11--12, printed pp.262--263; Fan, *Amalgams
of prime index*, J. Algebra 98 (1986), 375--421. The Tits and full Ree models
belong to F.1.12(I)(9) and (I)(5) at q = 2, respectively. These are direct
finite-model proofs; no unverified statement from Fan's paper is invoked.
Alignment of the original weak-BN-pair hypotheses remains with the F.1.12
assembly. The first Tits core is the corrected order-512 core with quotient
Sz(2), not the printed 1024/D10 package.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.ExceptionalRigidity
open Theory.GroupTheory RankTwoAmalgam

/-- The two concrete local counts imply recognition of arbitrary Sylow inputs.
No faithfulness premise is needed for this stronger, conditional route. -/
theorem tits_of_restriction_counts
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hα : SylowEmbedded 2 α)
    (e : ParabolicEquiv α Tits.ExceptionalParabolics.amalgam)
    (hleft : 4096 ≤ Nat.card Tits.AmalgamRigidity.firstRestrictions)
    (hright : 4096 ≤ Nat.card Tits.AmalgamRigidity.secondRestrictions) :
    IsAtlasTitsAmalgam α := by
  apply iso_of_twist_factorization hα
    (sylowEmbedded_ofSubgroups Tits.atlas1600SylowTwo _ _ _ _ _
      (Tits.ExceptionalParabolics.overlap_eq_sylow.trans
        Tits.atlas1600SylowTwo_coe.symm)) e
  exact Tits.AmalgamRigidity.factorsThrough_of_counts hleft hright

/-- The exact faithful-twist contract, with both endpoint extension premises
discharged by the concrete Tits restriction calculation. -/
theorem tits_faithful_twist_factorization
    (d : MulAut Tits.ExceptionalParabolics.overlap)
    (_hf : Faithful (twistRight Tits.ExceptionalParabolics.amalgam d)) :
    FactorsThrough Tits.ExceptionalParabolics.amalgam d :=
  Tits.AmalgamRigidity.factorsThrough d

/-- The full binary Ree calculation discharges the same contract for its
literal overlap. No Tits factorization premise remains. -/
theorem reeFull_faithful_twist_factorization
    (d : MulAut Tits.ExceptionalParabolics.FullRee.B)
    (_hf : Faithful (twistRight Tits.ExceptionalParabolics.FullRee.amalgam d)) :
    FactorsThrough Tits.ExceptionalParabolics.FullRee.amalgam d :=
  Tits.AmalgamRigidity.FullRee.factorsThrough d

/-- The Tits parabolic equivalence upgrades to an isomorphism of both squares.
The endpoint counts are proved, and faithfulness is unnecessary. -/
theorem tits_of_parabolicEquiv
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hα : SylowEmbedded 2 α)
    (e : ParabolicEquiv α Tits.ExceptionalParabolics.amalgam) :
    IsAtlasTitsAmalgam α :=
  tits_of_restriction_counts hα e Tits.AmalgamRigidity.firstRestrictions_card_ge
    Tits.AmalgamRigidity.secondRestrictions_card_ge

/-- The full binary Ree parabolic equivalence upgrades to an isomorphism of
both squares, with all finite-model premises discharged. -/
theorem reeFull_of_parabolicEquiv
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hα : SylowEmbedded 2 α)
    (e : ParabolicEquiv α Tits.ExceptionalParabolics.FullRee.amalgam) :
    IsBinaryReeAmalgam α :=
  Tits.AmalgamRigidity.FullRee.iso_of_parabolicEquiv hα e

/-- Recognition in the actual full automorphism group of the Atlas Tits group,
using its proved marked identification with the full binary Ree model. -/
theorem titsAutomorphism_of_parabolicEquiv
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hα : SylowEmbedded 2 α)
    (e : ParabolicEquiv α
      Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgam) :
    Nonempty (Iso α Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgam) :=
  (reeFull_of_parabolicEquiv hα
    (e.trans Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgamIso.symm.toParabolicEquiv)).automorphism_model

end CFSG.Quasithin.ChapterF.GreenBook.ExceptionalRigidity
