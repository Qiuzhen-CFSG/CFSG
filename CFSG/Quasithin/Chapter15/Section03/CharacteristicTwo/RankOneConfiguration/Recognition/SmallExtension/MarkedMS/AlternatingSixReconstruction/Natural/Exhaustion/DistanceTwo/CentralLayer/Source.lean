module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Inputs
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSixMoved
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator
public import Theory.GroupTheory.NormalSectionResidualMonolith
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import Theory.Quasithin.Rank

/-!
# The whole alternating-six moving layer on a characteristic replacement

The replacement retains the original moved elementary subgroup W. Its
centralizer is exactly the replacement two-core: otherwise normal generation
by the simple residual quotient would force the component to centralize W,
contrary to its nonzero, fully moved action. This uses no complement to the
possible central fixed line of the five-dimensional augmentation cover.

The replacement central omega layer X has a faithful FF action supplied by
MS3. The order-360 B.5.1 theorem identifies [X,K] with W. Applying the same
Irr-plus calculation to the faithful omega orbit identifies [Z,K] with W.
The literal free-amalgam embedding then gives [X_alpha,Ltilde_alpha] = U_alpha
and identifies U_alpha with the mapped original W. The final application
removes the moving-layer premise from the original Frattini branch.

Source: Meierfrankenfeld--Stellmacher, "Pushing up weak BN-pairs of rank two"
(1993), (3.2)(vi), printed pp.863--864, and Section 7, pp.932--933;
Aschbacher--Smith B.5.1. Whole-core exhaustion beyond the Frattini branch
remains with the distance-two assembly owner.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC ChapterB.QuasisimpleSource
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (d : Replacement L R)

local notation "K" => Subgroup.subgroupOf (L.subgroupOf (L ⊔ R)) d.overgroup

include h in
private theorem moved_normal : (replacementMoved d).Normal := by
  let := h.relative_normal
  infer_instance

include h in
private theorem moved_le_omega : replacementMoved d ≤ omegaCenterIn (pCore 2 d.overgroup) := by
  let := h.relative_normal
  intro x hx
  have hxX := (commutator_le_left (centralOmega L R) (L.subgroupOf (L ⊔ R))) hx
  obtain ⟨hq, hc, hs⟩ := (mem_omegaCenterIn_iff _ _).mp hxX
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨?_, ?_, Subtype.ext hs⟩
  · rw [replacement_core h d]
    exact hq
  · intro y hy
    apply Subtype.ext
    apply hc y
    rwa [replacement_core h d] at hy

include h in
private theorem moved_idempotent : ⁅replacementMoved d, K⁆ = replacementMoved d := by
  apply map_injective d.overgroup.subtype_injective
  rw [map_commutator, replacementMoved_map h d,
    map_subgroupOf_eq_of_le (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)]
  exact initial_moved_idempotent h

include h in
private theorem moved_ne_bot : replacementMoved d ≠ ⊥ := by
  intro he
  have hh := replacementMoved_map h d
  rw [he, Subgroup.map_bot] at hh
  exact initial_moved_ne_bot h hh.symm

variable (e : CentralMarking L) (hz : center (L ⧸ pCore 2 L) = ⊥)

include e hz in
omit [Finite G] in
private theorem component_quotient_simple : IsSimpleGroup (K ⧸ pCore 2 K) := by
  let := relative_quotient_simple (R := R) e hz
  let f := subgroupOfEquivOfLe
    (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
  exact (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).isSimpleGroup

include e hz in
/-- Both elementary moving layers equal the entire original moved subgroup,
including any central fixed line. No initial naturality premise is needed. -/
theorem replacement_centralLayer (h : SmallMSPair KnownSimple.IsKnownSimple L R) :
    CentralLayer d := by
  let W := replacementMoved d
  let X₀ := omegaCenterIn (pCore 2 d.overgroup)
  let Z₀ := MSCentralOrbit.omegaOrbit d.radical
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K).map q
  let := h.relative_normal
  let := component_quotient_simple d e hz
  have hK : (K).IsCComponent := h.component.subgroupOf
    (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
  obtain ⟨_, hn, hs, hqs, hc⟩ := MSCentralOrbit.component_image_structure K d.radical hK
    (replacement_radical_isPGroup h d) (replacement_product h d)
  let : C.Normal := hn
  let : IsSimpleGroup C := hs
  let : IsQuasisimple C := hqs
  let : W.Normal := moved_normal h d
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (moved_le_omega h d)
  let : IsElementaryAbelian 2 Z₀ := MSCentralOrbit.omegaOrbit_elementary d.radical
    (replacement_core_le_radical h d) (replacement_self_centralizing h d)
  let f := (subgroupOfEquivOfLe
    (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)).trans
    (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left))
  let a : C ≃* alternatingGroup (Fin 6) :=
    (cComponentTwoCoreQuotientEquiv hK).symm.trans
      ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans
        (SmallMSPair.alternatingQuotientEquivOfCenterEqBot e hz))
  have hcard : Nat.card C = 360 := by
    rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hsq : IsSQTK KnownSimple.IsKnownSimple (d.overgroup ⧸ pCore 2 d.overgroup) := by
    have hd := h.sqtk.subgroup d.overgroup
    refine ⟨?_, hd.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 d.overgroup)
      pCore_isPGroup).trans (hd.stronglyQuasithin p hp ho)
  have hZ : centralizer (Z₀ : Set d.overgroup) = pCore 2 d.overgroup :=
    MSCentralOrbit.omegaOrbit_centralizer K d.radical
      (replacement_radical_isPGroup h d) (replacement_radical_ne_bot h d)
      (replacement_core_le_radical h d) (replacement_self_centralizing h d)
      (replacement_product h d) (replacement_characteristic h d)
  have hX : q.ker = centralizer (X₀ : Set d.overgroup) :=
    (QuotientGroup.ker_mk' _).trans
      (MSCentralOrbit.centralOmega_centralizer d.radical
        (replacement_core_le_radical h d) (replacement_self_centralizing h d) hZ).symm
  have hW : q.ker = centralizer (W : Set d.overgroup) := by
    rw [QuotientGroup.ker_mk']
    apply le_antisymm
    · intro x hx w hw
      exact (((mem_omegaCenterIn_iff _ _).mp (moved_le_omega h d hw)).2.1 x hx).symm
    · by_contra hnW
      let : IsSimpleGroup ((pResidual 2 d.overgroup).map q) := by
        rw [replacement_residual h d]
        exact hs
      have hr := pResidual_le_normal_of_not_le_monolithic_kernel 2 q
        (QuotientGroup.mk'_surjective _) (by
          rw [show q.ker = pCore 2 d.overgroup from QuotientGroup.ker_mk' _]
          exact pCore_isPGroup) (by
            simpa only [replacement_residual h d] using hc)
        (centralizer (W : Set d.overgroup)) (by
          simpa only [q, QuotientGroup.ker_mk'] using hnW)
      rw [replacement_residual h d] at hr
      have he : ⁅W, K⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hr)
      rw [moved_idempotent h d] at he
      exact moved_ne_bot h d he
  have hff : IsFFModule (NormalElementaryQuotient.representation X₀ q
      (QuotientGroup.mk'_surjective _) hX) :=
    MSCentralOrbit.centralOmega_isFFModule d.radical (replacement_characteristic h d)
      (replacement_radical_isPGroup h d) (replacement_radical_ne_bot h d)
      (replacement_core_le_radical h d) (replacement_self_centralizing h d) hZ
      q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hXW : ⁅X₀, K⁆ = W :=
    normalElementary_card360_commutator_eq W X₀ (moved_le_omega h d)
      q (QuotientGroup.mk'_surjective _) hW hX K C rfl hcard hc (hsq.subgroup C)
      hff (moved_idempotent h d)
  have hZW : ⁅Z₀, K⁆ = W := by
    apply Eq.trans ?_ hXW
    apply NormalElementaryQuotient.commutator_eq_of_irrPlus Z₀ X₀
      (MSCentralOrbit.omegaOrbit_le_centralOmega d.radical
        (replacement_core_le_radical h d) (replacement_self_centralizing h d))
      q (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans hZ.symm)
      hX K C rfl
    · intro he
      rw [he, card_bot] at hcard
      omega
    · exact SourceCompletion.ff_card360_moved_irrPlus _ C hcard hc (hsq.subgroup C)
        (NormalElementaryQuotient.representation_injective X₀ q _ hX) hff
  have hgraphX : ⁅X d.radical (alpha d.radical), Ltilde d.radical (alpha d.radical)⁆ =
      W.map (embedM d.radical) := by
    rw [X, Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d), omegaCenter_map _ _ (embedM_injective _),
      Ltilde_alpha, replacement_residual h d, ← map_commutator]
    exact congrArg (Subgroup.map (embedM d.radical)) hXW
  have hgraphU : U d.radical (alpha d.radical) = W.map (embedM d.radical) := by
    rw [U, NaturalSixControl.SymplecticSeed.Z_eq_seedHull, Ltilde_alpha,
      replacement_residual h d, ← map_commutator]
    exact congrArg (Subgroup.map (embedM d.radical)) hZW
  exact ⟨hgraphX.trans hgraphU.symm, hgraphU⟩

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer

namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
universe u

/-- MS93 (3.2)(vi) on every characteristic replacement, retaining the whole
moved subgroup and any central fixed line. -/
theorem centralLayer_knownSimple : CentralLayerInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz _ d
  exact CentralLayer.replacement_centralLayer d e hz h

/-- The original Frattini branch now has no additional moving-layer premise. -/
theorem exhaustion_of_frattini_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (d : Replacement L R)
    (hsmall : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    ⁅pCore 2 (L ⊔ R : Subgroup G), L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_frattini h d (CentralLayer.replacement_centralLayer d e hz h) hsmall

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
