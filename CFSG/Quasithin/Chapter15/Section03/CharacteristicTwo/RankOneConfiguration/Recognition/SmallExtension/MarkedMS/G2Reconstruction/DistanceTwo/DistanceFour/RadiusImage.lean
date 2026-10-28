module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.Radius
public import Theory.Representation.G2BinaryOffenderGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Comparison.CriticalImage.Source

/-!
# The derived radius in a distance-two G₂ quotient

At critical distance four, every nontrivial generator of a radius image is a
natural G₂ offender. The radius is a two-group, so a common Sylow conjugator
places all these generators in the five-root radical. Its derived group has
order at most two. Applying the literal endpoint actor gives the same bound
for the relative index of the midpoint kernel in the actual derived radius.

This is the first derived-radius bound in MS93 (3.8), printed p.878. It does
not assume the residual fixation still required by `FixedRadiusInput`; the
subsequent midpoint-containment and nonfixed-derived arguments remain with
qt-e-ms-small-g2-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NaturalStructure.Exclusion
open Representation Representation.BinaryOffender Comparison Comparison.CriticalImage
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
include h e

/-- In one midpoint actor, all nontrivial radius-generator images are
natural offenders. A single Sylow conjugator puts the entire radius image
in the five-root subgroup. No fixation of the derived radius is assumed. -/
theorem radius_image_le_conjugate_radical
    (hb : (geometry h).b T = 4)
    (a c : Vertex T) (ha : color T a = false) (_hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (d : EndpointModel T c) :
    ∃ g : Atlas.G2.Model (ZMod 2),
      (image d (V T a)).map (MulAut.conj g).toMonoidHom ≤
        Atlas.G2.LieParabolicSetup.radical₁ := by
  let I := {v : Vertex T // color T v = false ∧ (cosetGraph T).dist v a ≤ 2}
  have hV : V T a = ⨆ v : I, Z T v.val := by
    apply le_antisymm
    · apply radius_le_of_m_ball ha
      intro v hv hdist
      exact le_iSup_of_le (⟨v,hv,hdist⟩ : I) le_rfl
    · apply iSup_le
      intro v
      exact le_iSup_of_le v.val (le_iSup_of_le v.property.2 le_rfl)
  have hSc (v : I) : Z T v.val ≤ stabilizer T c :=
    (geometry h).ball_Z_le_stabilizer (by omega) a v.val c v.property.1
      v.property.2 (by rw [SimpleGraph.dist_comm,hac])
  have hVS : V T a ≤ stabilizer T c :=
    ((geometry h).V_le_Q (by omega) a ha).trans
      (Q_le_stabilizer_of_dist_two T a c ha hac)
  have hpre : (V T a).subgroupOf (stabilizer T c) =
      ⨆ v : I, (Z T v.val).subgroupOf (stabilizer T c) := by
    apply map_injective (stabilizer T c).subtype_injective
    rw [map_subgroupOf_eq_of_le hVS,Subgroup.map_iSup,hV]
    apply iSup_congr
    intro v
    exact (map_subgroupOf_eq_of_le (hSc v)).symm
  let E : I → Subgroup (Atlas.G2.Model (ZMod 2)) := fun v => image d (Z T v.val)
  have heq : image d (V T a) = ⨆ v : I, E v := by
    change ((V T a).subgroupOf (stabilizer T c)).map d.actor = _
    rw [hpre,Subgroup.map_iSup]
    rfl
  have hE (v : I) : E v = ⊥ ∨ IsOffender rho (E v) := by
    by_cases hq : Z T v.val ≤ Q T c
    · left
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro x hx
      have hxQ := hq hx
      have hk : d.actor.ker = (Q T c).subgroupOf (stabilizer T c) := by
        apply map_injective (stabilizer T c).subtype_injective
        rw [d.actor_kernel,map_subgroupOf_eq_of_le (show Q T c ≤ stabilizer T c from fun _ hx => hx.1)]
      rw [hk]
      exact hxQ
    · right
      have hmin := criticalDistance_le T v.val ((geometry h).exists_critical v.val v.property.1) hq
      have hd : criticalDistance T v.val ((geometry h).exists_critical v.val v.property.1) = 4 :=
        ((geometry h).distance_constant v.val v.property.1).trans hb
      have ht := (cosetGraph_connected T).dist_triangle (u := v.val) (v := a) (w := c)
      have hcrit : CriticalPair T v.val c ((geometry h).exists_critical v.val v.property.1) := by
        refine ⟨?_,hq⟩
        have hv := v.property.2
        omega
      obtain ⟨dv⟩ := endpointModel_knownSimple h e v.property.1
      exact critical_image_offender (geometry h) (edgeCentralizer h e) v.val c v.property.1
        (by omega) hcrit dv d
  have hp : IsPGroup 2 (image d (V T a)) :=
    ((radius_isPGroup h (by omega) a ha).comap_subtype).map d.actor
  rw [heq] at hp ⊢
  exact Atlas.G2.Natural.BinaryOffenderGeneration.generated_offenders_le_conjugate_radical E hp hE

/-- The image of the full derived radius at a distance-two vertex has order
at most two, the first nonfixed-derived bound in MS93 (3.8). -/
theorem radius_derived_image_card_le_two
    (hb : (geometry h).b T = 4)
    (a c : Vertex T) (ha : color T a = false) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (d : EndpointModel T c) :
    Nat.card (image d (⁅V T a,V T a⁆)) ≤ 2 := by
  obtain ⟨g,hg⟩ := radius_image_le_conjugate_radical h e hb a c ha hcColor hac d
  have hc := Atlas.G2.Natural.BinaryOffenderGeneration.derived_card_le_two_of_le_radical _ hg
  rw [←map_commutator,card_map_of_injective (MulAut.conj g).injective] at hc
  have hVS : V T a ≤ stabilizer T c :=
    ((geometry h).V_le_Q (by omega) a ha).trans
      (Q_le_stabilizer_of_dist_two T a c ha hac)
  have hdS : ⁅V T a,V T a⁆ ≤ stabilizer T c :=
    (le_normalizer_iff_commutator_le_left.mp (V T a).le_normalizer).trans hVS
  have heq : (⁅V T a,V T a⁆).subgroupOf (stabilizer T c) =
      ⁅(V T a).subgroupOf (stabilizer T c),(V T a).subgroupOf (stabilizer T c)⁆ := by
    apply map_injective (stabilizer T c).subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hdS,map_subgroupOf_eq_of_le hVS]
  simpa only [image,heq,map_commutator] using hc

/-- The order-two bound is expressed with the original kernel and relative
index, preserving the exact quotient map for the subsequent displacement proof. -/
theorem radius_derived_index_le_two
    (hb : (geometry h).b T = 4)
    (a c : Vertex T) (ha : color T a = false) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) :
    (Q T c).relIndex (⁅V T a,V T a⁆ : Subgroup (FreeAmalgam T)) ≤ 2 := by
  obtain ⟨d⟩ := endpointModel_knownSimple h e hcColor
  have hVS : V T a ≤ stabilizer T c :=
    ((geometry h).V_le_Q (by omega) a ha).trans
      (Q_le_stabilizer_of_dist_two T a c ha hac)
  have hdS : ⁅V T a,V T a⁆ ≤ stabilizer T c :=
    (le_normalizer_iff_commutator_le_left.mp (V T a).le_normalizer).trans hVS
  rw [←image_card d _ hdS]
  exact radius_derived_image_card_le_two h e hb a c ha hcColor hac d

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour
