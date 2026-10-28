module

public import Theory.GroupTheory.Amalgam.RestrictionProduct
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Automorphisms
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Verified

/-!
# Coordinates retaining both full binary Ree overlap inclusions

The verified root map identifies the coordinate Sylow group with the entire
Borel. Its first inclusion is the existing semidirect-product embedding. The
second inclusion is the actual full Ree inclusion composed with that same root
map. Thus the comparison below is an isomorphism of marked amalgams, including
both commuting squares; it makes no assumption about uniqueness of amalgams.

These definitions support a restriction-group calculation for the full Ree
alternative in Aschbacher--Smith F.1.11--12, printed pp.262--263. The coordinate
comparison follows Shinoda (1975), pp.81--83, and Parrott (1972), p.683. In
particular it does not presume that the mixed-character Tits subgroup is
characteristic in the full Sylow group.
-/

@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee
open Theory.GroupTheory RankTwoAmalgam

/-- The verified Sylow map, with codomain the literal whole overlap. -/
def borelEquiv : ReeTwo.SylowModel ≃* ExceptionalParabolics.FullRee.B :=
  ReeTwo.ParabolicMarkedComparison.Verified.sylowEquiv.trans
    (MulEquiv.subgroupCongr ExceptionalParabolics.FullRee.borel_eq_sylow.symm)

/-- Coordinate marking on the left, with the actual second endpoint on the right. -/
def coordinateAmalgam : RankTwoAmalgam ReeTwo.Centralizer ReeTwo.SylowModel
    ExceptionalParabolics.FullRee.second where
  left := ReeTwo.SylowModel.embedding
  right := ExceptionalParabolics.FullRee.amalgam.right.comp borelEquiv.toMonoidHom

/-- Both inclusion squares use the same verified ambient root map. -/
def coordinateAmalgamIso : Iso coordinateAmalgam ExceptionalParabolics.FullRee.amalgam where
  left := ReeTwo.ParabolicMarkedComparison.Verified.firstEquiv
  middle := borelEquiv
  right := MulEquiv.refl _
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := rfl

/-- Restrictions of automorphisms of the first coordinate endpoint. -/
abbrev firstRestrictions : Subgroup (MulAut ReeTwo.SylowModel) :=
  extensionSubgroup ReeTwo.SylowModel.embedding

/-- Restrictions along the marked inclusion into the actual second endpoint. -/
abbrev secondRestrictions : Subgroup (MulAut ReeTwo.SylowModel) :=
  extensionSubgroup coordinateAmalgam.right

/-- The whole model overlap is a Sylow subgroup at both endpoints. -/
theorem sylowEmbedded : SylowEmbedded 2 ExceptionalParabolics.FullRee.amalgam :=
  sylowEmbedded_ofSubgroups ExceptionalParabolics.FullRee.sylow _ _ _ _ _
    (ExceptionalParabolics.FullRee.borel_eq_sylow.trans
      ExceptionalParabolics.FullRee.sylow_coe.symm)

end Tits.AmalgamRigidity.FullRee
