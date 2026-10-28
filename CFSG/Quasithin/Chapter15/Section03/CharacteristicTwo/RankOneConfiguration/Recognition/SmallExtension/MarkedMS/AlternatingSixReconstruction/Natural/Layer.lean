module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Cases
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovingSection
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The faithful initial layer in the center-free alternating-six case

For M = LR, put Q = O₂(M), X = Ω₁Z(Q), and K = L inside M.
The center-free marking makes K/O₂(K) simple. The initial omega orbit
therefore has centralizer Q, and so does X. Its actual quotient action is
an FF module. We retain the canonical moved/fixed section for this action;
in particular we do not replace a possible five-dimensional moved space
by a four-dimensional subgroup.

Source: Aschbacher--Smith C.1.31--32, printed pp.135--136; MS93 (2.2)
and (3.2)(vi), printed pp.856--857 and 863--864.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC ChapterB.QuasisimpleSource
namespace AlternatingSixReconstruction.Natural
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- The actual central omega subgroup of the MS ambient two-core. -/
abbrev centralOmega (L R : Subgroup G) : Subgroup (L ⊔ R : Subgroup G) :=
  omegaCenterIn (pCore 2 (L ⊔ R : Subgroup G))

instance centralOmega_normal (L R : Subgroup G) : (centralOmega L R).Normal := by
  let : (omega₁ (center (pCore 2 (L ⊔ R : Subgroup G))) (p := 2)).Characteristic :=
    omega₁_characteristic _
  infer_instance

/-- Keep the central-core marking separate from the action recognition. -/
abbrev CentralMarking (L : Subgroup G) :=
  (L ⧸ centralPreimage (pCore 2 L)) ≃*
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))

variable (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M
local notation "X" => centralOmega L R

include e hz in
omit [Finite G] in
/-- The full relative component quotient is simple, not merely quasisimple. -/
theorem relative_quotient_simple : IsSimpleGroup (K ⧸ pCore 2 K) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  exact ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans
    (SmallMSPair.alternatingQuotientEquivOfCenterEqBot e hz)).isSimpleGroup

include h e hz in
/-- In the center-free case the initial orbit has no extra odd kernel. -/
theorem orbit_centralizer :
    centralizer (MSCentralOrbit.omegaOrbit (R.subgroupOf (L ⊔ R)) : Set M) = Q := by
  let := h.relative_normal
  let := relative_quotient_simple (R := R) e hz
  exact MSCentralOrbit.omegaOrbit_centralizer K (R.subgroupOf (L ⊔ R))
    h.relative_radical.isPGroup h.relative_radical_ne_bot h.relative_radical.twoCore_le
    h.relative_self_centralizing h.relative_product h.relative_characteristic

include h e hz in
/-- The literal action of M on X has kernel Q. -/
theorem centralOmega_centralizer : centralizer (X : Set M) = Q := by
  apply le_antisymm
  · rw [← orbit_centralizer h e hz]
    exact centralizer_le (MSCentralOrbit.omegaOrbit_le_centralOmega _
      h.relative_radical.twoCore_le h.relative_self_centralizing)
  · intro q hq x hx
    exact (((mem_omegaCenterIn_iff Q x).mp hx).2.1 q hq).symm

/-- The action uses the original projection M → M/O₂(M). -/
def initialAction : Representation (ZMod 2) (M ⧸ Q) (Additive X) :=
  NormalElementaryQuotient.representation X (QuotientGroup.mk' Q)
    (QuotientGroup.mk'_surjective Q)
    ((QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h e hz).symm)

theorem initialAction_faithful : Function.Injective (initialAction h e hz) :=
  NormalElementaryQuotient.representation_injective _ _ _ _

/-- MS3 supplies the FF property on the entire central omega layer. -/
theorem initialAction_isFFModule : IsFFModule (initialAction h e hz) := by
  unfold initialAction
  apply NormalElementaryQuotient.isFFModule_of_thompson_not_le
    X (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
    ((QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h e hz).symm)
    (R.subgroupOf (L ⊔ R))
  · intro x hx
    exact h.relative_radical.twoCore_le ((mem_omegaCenterIn_iff Q x).mp hx).1
  · simpa only [QuotientGroup.ker_mk'] using
      h.relative_characteristic.thompson_not_le_core h.relative_radical.isPGroup
        h.relative_radical_ne_bot h.relative_radical.twoCore_le

/-- The literal component image in the ambient two-core quotient. -/
abbrev componentImage (L R : Subgroup G) :
    Subgroup ((L ⊔ R : Subgroup G) ⧸ pCore 2 (L ⊔ R : Subgroup G)) :=
  (L.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (pCore 2 (L ⊔ R : Subgroup G)))

/-- The section is [X,K]/C_[X,K](K), with the original conjugation action. -/
def initialSection : MovedSection (initialAction h e hz) (componentImage L R) := by
  let := h.relative_normal
  exact MovedSection.ofNormal _ _

/-- A literal natural action on the initial central quotient. This does not
assert that the whole commutator core lies in X. -/
def InitialNatural : Prop :=
  IsAlternatingNatural ((initialSection h e hz).action.comp (componentImage L R).subtype) 6

include h in
/-- The two-perfect component fully moves its initial moved subgroup. -/
theorem initial_moved_idempotent : ⁅⁅X, K⁆, K⁆ = ⁅X, K⁆ :=
  commutator_isPPerfect_idempotent K X h.relative_twoPerfect
    (IsElementaryAbelian.isPGroup 2 X) le_normalizer_of_normal

include h in
/-- The initial moved subgroup is nonzero, without a naturality assumption. -/
theorem initial_moved_ne_bot : ⁅X, K⁆ ≠ ⊥ := by
  intro hh
  apply MSCentralOrbit.component_not_centralizes_omegaOrbit K (R.subgroupOf (L ⊔ R))
    h.relative_radical.isPGroup h.relative_radical_ne_bot h.relative_product
    h.relative_characteristic
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
  exact hc.trans (centralizer_le (MSCentralOrbit.omegaOrbit_le_centralOmega _
    h.relative_radical.twoCore_le h.relative_self_centralizing))

end AlternatingSixReconstruction.Natural
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
