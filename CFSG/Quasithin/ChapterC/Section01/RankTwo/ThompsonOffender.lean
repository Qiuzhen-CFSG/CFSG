module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CentralOrbit
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# The actual FF module supplied by the MS characteristic condition

If R contains O₂(H), MS3 forces its elementary Thompson subgroup outside
O₂(H): otherwise it agrees with the elementary Thompson subgroup of O₂(H)
and is normal in H. Thus every normal elementary layer X contained in R
with C_H(X)=O₂(H) has a genuine offender on its actual quotient action.
In particular the initial omega orbit makes X=Ω₁(Z(O₂(H))) faithful,
providing the input to the nonbinary Sp₄(4) natural-module recognition.

Source: MS93 (2.2)(vi), (3.2)(vi), pp.856--857 and863--864;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public section
open Subgroup Stellmacher
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {H : Type*} [Group H] [Finite H]

/-- MS3 prevents the elementary Thompson subgroup from lying in the two-core. -/
theorem MSCharacteristicCondition.thompson_not_le_core {R : Subgroup H}
    (hms : MSCharacteristicCondition R) (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hQR : pCore 2 H ≤ R) : ¬ elementaryAbelianMaxJ R ≤ pCore 2 H := by
  intro hle
  have heqOrder : elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder (pCore 2 H) :=
    le_antisymm (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ hle).1
      (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hQR).1
  have heqJ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (pCore 2 H) :=
    le_antisymm ((elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ hle).2 heqOrder)
      ((elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hQR).2 heqOrder.symm)
  have hmap (T : Subgroup H) :
      (elementaryAbelianMaxJ (⊤ : Subgroup T)).map T.subtype = elementaryAbelianMaxJ T := by
    rw [← elementaryAbelianMaxJ_map_injective _ T.subtype_injective,
      ← MonoidHom.range_eq_map, T.range_subtype]
  let C : Subgroup R := elementaryAbelianMaxJ ⊤
  let : C.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hn : (C.map R.subtype).Normal := by
    change ((elementaryAbelianMaxJ (⊤ : Subgroup R)).map R.subtype).Normal
    rw [hmap, heqJ, ← hmap (pCore 2 H)]
    let : (elementaryAbelianMaxJ (⊤ : Subgroup (pCore 2 H))).Characteristic :=
      elementaryAbelianMaxJ_top_characteristic
    infer_instance
  have hC : C = ⊥ := hms.eq_bot_of_normal C hn
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hne
  let D : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  have hD : D ≠ ⊥ := omega_center_ne_bot hp
  have hDe : IsElementaryAbelian 2 D := by
    let : IsElementaryAbelian 2 (omega₁ (center R) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative (center R)
    exact IsElementaryAbelian.map (center R).subtype
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup R)
  have hAC : A ≤ C := le_sSup hA
  have hAbot : A = ⊥ := le_bot_iff.mp (hC ▸ hAC)
  have hcard := hA.2.2 D le_top hDe
  rw [hAbot, card_bot] at hcard
  exact hD (eq_bot_of_card_le D hcard)

/-- The source condition supplies an FF offender on the literal quotient
representation, without a natural-module recognition premise. -/
theorem MSCharacteristicCondition.isFFModule {R X : Subgroup H}
    [X.Normal] [IsElementaryAbelian 2 X]
    (hms : MSCharacteristicCondition R) (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hQR : pCore 2 H ≤ R) (hXR : X ≤ R)
    {J : Type*} [Group J] (q : H →* J) (hq : Function.Surjective q)
    (hcore : q.ker = pCore 2 H) (hker : q.ker = centralizer (X : Set H)) :
    IsFFModule (NormalElementaryQuotient.representation X q hq hker) := by
  let : Finite J := Finite.of_surjective q hq
  apply NormalElementaryQuotient.isFFModule_of_thompson_not_le X q hq hker R hXR
  rw [hcore]
  exact hms.thompson_not_le_core hp hne hQR

namespace MSCentralOrbit

omit [Finite H] in
/-- The full central omega layer has the same centralizer as its initial
omega orbit, hence remains faithful modulo the actual two-core. -/
theorem centralOmega_centralizer (R : Subgroup H)
    (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H) :
    centralizer (omegaCenterIn (pCore 2 H) : Set H) = pCore 2 H := by
  apply le_antisymm
  · exact (centralizer_le (omegaOrbit_le_centralOmega R hQR hself)).trans_eq hfaith
  · intro q hq x hx
    exact (((mem_omegaCenterIn_iff _ _).mp hx).2.1 q hq).symm

omit [Finite H] in
/-- The central omega layer is normal in the original ambient group. -/
instance centralOmega_normal : (omegaCenterIn (pCore 2 H)).Normal := by
  let : (omega₁ (center (pCore 2 H)) (p := 2)).Characteristic := omega₁_characteristic _
  infer_instance

/-- A quotient with the actual two-core kernel supports the original central
omega FF module. This is the exact initial X-layer input for MS93 (3.2). -/
theorem centralOmega_isFFModule (R : Subgroup H)
    (hms : MSCharacteristicCondition R) (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    {J : Type*} [Group J] (q : H →* J) (hq : Function.Surjective q)
    (hcore : q.ker = pCore 2 H) :
    IsFFModule (NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) q hq
      (hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm)) := by
  apply hms.isFFModule hp hne hQR ?_ q hq hcore
  intro x hx
  exact hQR ((mem_omegaCenterIn_iff _ _).mp hx).1

end MSCentralOrbit
end CFSG.Quasithin.ChapterC
