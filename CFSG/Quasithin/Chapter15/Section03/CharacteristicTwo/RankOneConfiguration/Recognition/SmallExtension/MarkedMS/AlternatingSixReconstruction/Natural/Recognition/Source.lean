module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Inputs
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedModel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Quasithin.Rank

/-!
# Natural recognition of the initial alternating-six moved quotient

The actual image of the relative component in M/O₂(M) is simple and
self-centralizing. Its SQTK hypothesis descends from the original MS pair
through the two-core quotient. The faithful central-omega FF action therefore
satisfies the complete B.5.1 classifier. Comparison with the marked A₆ actor
leaves the natural action, including the derived binary symplectic row.

The classifier first works inside the offender-generated subgroup. The identity
map on the original vector space and the literal component inclusion transport
its moved/fixed quotient to the canonical initialSection. Checking this transport
on an abstract representation avoids unfolding the concrete conjugation action.

This proves initial recognition; whole-core exhaustion is a separate source step.
Source: Aschbacher--Smith C.1.31--32, printed pp.135--136, and B.5.1;
Meierfrankenfeld--Stellmacher (1993), (3.2)(vi), printed pp.863--864.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC ChapterB.QuasisimpleSource
namespace AlternatingSixReconstruction.Natural
universe u

private theorem natural_of_ff
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D)
    [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hc : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ)
    (a : C ≃* alternatingGroup (Fin 6)) (s : MovedSection ρ C) :
    IsAlternatingNatural (s.action.comp C.subtype) 6 := by
  obtain ⟨hCJ, ⟨c⟩⟩ := SourceCompletion.ff_socle_source_conclusion ρ C hc hsq hf hff
  obtain ⟨_, ⟨E⟩⟩ := C27Source.AlternatingSixMovedModel.source_natural _ c
    ((subgroupOfEquivOfLe hCJ).trans a)
  let B := C.subgroupOf (offenderSubgroup ρ)
  let φ : C ≃* B := (subgroupOfEquivOfLe hCJ).symm
  have hm : (moved ρ C).map (LinearMap.id : V →ₗ[ZMod 2] V) =
      moved (ρ.comp (offenderSubgroup ρ).subtype) B := by
    rw [Submodule.map_id, moved_comp_map, map_subgroupOf_eq_of_le hCJ]
  let T := c.sectionData.componentEmbeddingEquiv s φ
    (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ hh => hh) (fun _ _ => rfl) hm
  exact ⟨{
    groupEquiv := T.groupEquiv.trans E.groupEquiv
    linearEquiv := T.linearEquiv.trans E.linearEquiv
    intertwines := fun g v => by
      change E.linearEquiv (T.linearEquiv (_)) = _
      rw [T.intertwines, E.intertwines]
      rfl }⟩

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- The canonical initial moved/fixed quotient has the actual binary natural A₆ action. -/
theorem initialNatural_knownSimple
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) : InitialNatural h e hz := by
  let M := (L ⊔ R : Subgroup G)
  let K := L.subgroupOf (L ⊔ R)
  let C := componentImage L R
  let ρ := initialAction h e hz
  let := relative_quotient_simple (R := R) e hz
  obtain ⟨_, hn, hs, hq, hc⟩ := MSCentralOrbit.component_image_structure
    K (R.subgroupOf (L ⊔ R)) h.component h.relative_radical.isPGroup h.relative_product
  let : C.Normal := hn
  let : IsSimpleGroup C := hs
  let : IsQuasisimple C := hq
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let a : C ≃* alternatingGroup (Fin 6) :=
    (cComponentTwoCoreQuotientEquiv h.component).symm.trans
      ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans
        (SmallMSPair.alternatingQuotientEquivOfCenterEqBot e hz))
  have hsq : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_, h.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 M) pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin p hp ho)
  exact natural_of_ff ρ C hc (hsq.subgroup C)
    (initialAction_faithful h e hz) (initialAction_isFFModule h e hz) a
    (initialSection h e hz)

/-- Initial recognition for the full known-simple catalogue, with no additional module input. -/
theorem initialRecognition_knownSimple :
    InitialRecognitionInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz
  exact initialNatural_knownSimple h e hz

end AlternatingSixReconstruction.Natural
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
