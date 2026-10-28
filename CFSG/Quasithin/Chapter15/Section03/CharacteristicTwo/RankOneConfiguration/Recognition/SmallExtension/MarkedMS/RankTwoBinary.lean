module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover

/-!
# The binary linear branch of the small MS classification

In the binary linear row of MS1, cyclic-Sylow transfer removes the center
of L/O₂(L). Thus the specified central-core identification supplies the
full SL₃(2) quotient and case (5) of C.1.32. This argument only needs the
perfectness supplied by the actual relative C-component.

The final theorem applies this branch to the original marked component,
retaining its star quotient map and the specified Sylow subgroup.

Source: Aschbacher--Smith C.1.31--32, printed pp.135--136, and 15.3.31,
printed p.1132. The alternating and G₂ rows require their separate block
reconstruction arguments.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

omit [Finite G] in
/-- Perfectness belongs to the original component, as well as its relative
copy inside the component--radical join. -/
theorem SmallMSPair.component_perfect (h : SmallMSPair κ L R) : Group.IsPerfect L := by
  let _ := h.component.perfect
  let e := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

/-- The linear row of the central-core quotient gives the full binary core
quotient. No C.1.32 or C.1.34 classification premise is used. -/
def SmallMSPair.binaryCoreQuotientEquiv (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := by
  let _ := h.component_perfect
  let _ := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  let eSL := e.trans
    ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv)
  let eZ := (centralPreimageQuotientEquiv (pCore 2 L)).symm.trans eSL
  let f : PerfectCentralCovering.Cover (L ⧸ pCore 2 L)
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := {
    toMonoidHom := eZ.toMonoidHom.comp (QuotientGroup.mk' (center (L ⧸ pCore 2 L)))
    surjective := eZ.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      change eZ (QuotientGroup.mk' (center (L ⧸ pCore 2 L)) x) = 1 at hx
      exact (QuotientGroup.eq_one_iff x).mp (eZ.map_eq_one_iff.mp hx) }
  exact Matrix.PSL3Two.centralCoverEquiv f (pCore_quotient_pCore_eq_bot 2)

/-- C.1.32(5), with the actual field F₂ and degree one, is established for
this complete row of the small MS-pair input. -/
theorem SmallMSPair.rankTwo_of_binary (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    RankTwoAlternatives L R := by
  exact Or.inr (Or.inr (Or.inr (Or.inr
    ⟨1, by decide, ZMod 2, inferInstance, inferInstance, by simp,
      ⟨h.binaryCoreQuotientEquiv e⟩⟩)))

/-- Apply the proved binary branch to the literal local star marking.
The quotient comparison is the one constructed from that marking. -/
theorem rankTwo_of_linearThree_marking (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) Parabolics.linearThreeParabolic)
    (hms : SmallMSPair κ c.L d.S) : RankTwoAlternatives c.L d.S := by
  let _ := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  apply hms.rankTwo_of_binary
  exact ((centralCoreQuotientEquivStar d c hnormal P hP (.linearThree m)).trans
    m.equiv).trans (topEquiv.symm.trans
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
