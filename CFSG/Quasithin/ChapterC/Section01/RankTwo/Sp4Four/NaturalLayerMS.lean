module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.ThompsonOffender

/-!
# The MS characteristic condition recognizes the initial Sp4(4) layer

The initial central omega orbit has centralizer O2(H). Its containing layer
X=Omega1(Z(O2(H))) therefore has exactly that centralizer. MS3 constructs an
FF offender on the literal conjugation representation of H/O2(H) on X.
When its simple normal component has the supplied Sp4(4) order, the complete
classification identifies [X,L]/C_[X,L](L) as the natural Sp4 module over a
field of order four. This application discharges the offender premise of
natural recognition from the actual MS condition and the initial orbit.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2)(vi) and (3.2)(vi).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- Initial natural-module recognition on the original central omega layer.
The quotient map and the canonical moved/fixed section remain literal. -/
theorem centralOmega_moved_natural
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    (C : Subgroup J) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hc : Nat.card C = 979200) (hC : centralizer (C : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C) :
    let X := omegaCenterIn (pCore 2 H)
    let hker := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
    let ρ := NormalElementaryQuotient.representation X q hq hker
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) ∧
      ∃ F : BinaryField, F.degree = 2 ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ C).action.comp C.subtype)
          (binarySymplectic F)) := by
  dsimp only
  apply ff_card_sp4_four_moved_natural _ C hc hC hsq
  · exact NormalElementaryQuotient.representation_injective _ _ _ _
  · exact centralOmega_isFFModule R hms hp hne hQR hself hfaith q hq hcore

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
