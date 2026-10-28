module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Conditions
public import Theory.SpecificGroups.G2.BinaryCentralCore

/-!
# The full component quotient in the small G₂ MS branch

The C-component is perfect on its original carrier. The binary derived G₂
cover theorem therefore removes the central kernel above its two-core.
Both the arbitrary MS-pair and the original local parabolic marking retain
their literal projection. This supplies the quotient input to C.1.32(1);
the whole commutator-module reconstruction and shortness remain separate.

Source: Aschbacher--Smith C.1.31--32, printed pp.135--136, and 15.3.31,
printed p.1132. No MS93 classification alternative is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

omit [Finite G] in
private theorem component_perfect (h : SmallMSPair κ L R) : Group.IsPerfect L := by
  let _ := h.component.perfect
  let e := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

/-- The derived G₂ central-core marking gives the full intrinsic core quotient. -/
def SmallMSPair.g2CoreQuotientEquiv (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) :
    (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)) := by
  let _ := component_perfect h
  exact Atlas.G2.BinaryCentralCore.coreQuotientEquiv e

/-- The original component projection is retained by the recovered marking. -/
theorem SmallMSPair.g2CoreQuotientEquiv_apply (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) (l : L) :
    h.g2CoreQuotientEquiv e (QuotientGroup.mk' (pCore 2 L) l) =
      e (QuotientGroup.mk' (centralPreimage (pCore 2 L)) l) := by
  let _ := component_perfect h
  exact Atlas.G2.BinaryCentralCore.coreQuotientEquiv_apply e l

/-- The source central preimage is exactly the two-core in this branch. -/
theorem SmallMSPair.g2_centralPreimage_eq (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) :
    centralPreimage (pCore 2 L) = pCore 2 L := by
  let _ := component_perfect h
  exact Atlas.G2.BinaryCentralCore.centralPreimage_eq e

/-- Apply the quotient recovery to the original star marking and its actual
component map. This discharges the covering input without a block premise. -/
theorem g2_core_quotient_of_marking (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Atlas.G2.Model (ZMod 2))) Parabolics.g2DerivedParabolic)
    (hms : SmallMSPair κ c.L d.S) :
    ∃ e : (c.L ⧸ pCore 2 c.L) ≃* commutator (Atlas.G2.Model (ZMod 2)),
      ∀ l : c.L, e (QuotientGroup.mk' (pCore 2 c.L) l) =
        m.equiv (componentMap d c l) := by
  let e := (centralCoreQuotientEquivStar d c hnormal P hP (.g2Derived m)).trans m.equiv
  refine ⟨hms.g2CoreQuotientEquiv e, ?_⟩
  intro l
  rw [SmallMSPair.g2CoreQuotientEquiv_apply]
  exact congrArg m.equiv (centralCoreQuotientEquivStar_apply d c hnormal P hP (.g2Derived m) l)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
