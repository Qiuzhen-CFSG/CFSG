module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerMS
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator

/-!
# The actual initial Sp4(4) commutator core

The normal Sylow-center omega orbit W and the full layer
X=Omega1(Z(O2(H))) have the same centralizer O2(H). The previous MS
recognition puts the moved space of X in Irr-plus for the actual quotient
component. Faithfulness makes W a noncentral submodule, so Irr-plus forces
its moved space to coincide with that of X. Literal quotient-action
coordinates turn this into [W,K]=[X,K] as subgroup equality in H.

Source: Meierfrankenfeld--Stellmacher (1993), (3.2)(vi), the initial
identification [X,L]=U. Reconstruction of the entire later commutator core
is separate.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H J : Type*} [Group H] [Group J]

variable [Finite H] [Finite J]

/-- The MS initial central orbit and the full central omega layer have the
same literal commutator with the component. No fully moved premise is used. -/
theorem initialCore_eq
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    (K : Subgroup H) (C : Subgroup J)
    [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hKC : K.map q = C)
    (hc : Nat.card C = 979200) (hC : centralizer (C : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C) :
    ⁅omegaOrbit R,K⁆ = ⁅omegaCenterIn (pCore 2 H),K⁆ := by
  let : IsElementaryAbelian 2 (omegaOrbit R) := omegaOrbit_elementary R hQR hself
  have hneC : C ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hc
    omega
  have hi := (centralOmega_moved_natural R hms hp hne hQR hself hfaith
    q hq hcore C hc hC hsq).1
  exact NormalElementaryQuotient.commutator_eq_of_irrPlus (omegaOrbit R)
    (omegaCenterIn (pCore 2 H)) (omegaOrbit_le_centralOmega R hQR hself) q hq
    (hcore.trans hfaith.symm)
    (hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm)
    K C hKC hneC hi


end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
