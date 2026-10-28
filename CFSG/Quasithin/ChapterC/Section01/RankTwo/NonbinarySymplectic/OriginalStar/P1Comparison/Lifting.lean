module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.StrictMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFixedTrivial
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison.Lifting

/-!
# Lifting the original point-core movement

For the literal original star, point-core movement and the critical
commutator lie in the opposite moving group. If this group misses the
complete fixed attachment, containment after the tilde projection lifts
to containment before projection. The original critical commutator has
order q, while the point-core intersection has strictly greater movement.

The opposite fixed-core disjointness remains explicit here; the order and
strict movement are proved from the original source hypotheses.
Source: MS93 (3.7), printed p.877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour
variable {H F E : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable [Field E] [Finite E] [CharP E 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

omit [Finite F] [CharP F 2] [Finite E] [CharP E 2] in
/-- Lift a containment modulo the whole fixed core, on the original graph. -/
theorem original_movement_le_critical_commutator
    (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z t : Vertex R} (path : CriticalPath R g a z)
    (hb : g.b R=2) (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (κ : stabilizer R a →* Sp E) (u : Sp E)
    (hdis : Disjoint (fixedCore R a) (U R z))
    (hcentral : layerImage R a (Z R z) ≤ relativeCentralizer R κ z u) :
    ⁅Z R z,markedPointCore R κ u⊓Q R t⁆ ≤ ⁅Z R a,Z R z⁆ := by
  let S := stabilizer R a
  let J := markedPointCore R κ u⊓Q R t
  have hZaT : Z R a≤Q R t := by
    apply Z_le_Q_of_dist_lt R a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1<g.b R
    omega
  have hZzT : Z R z≤Q R t := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1<g.b R
    omega
  have hZaS : Z R a≤S := hZaT.trans (original_edge_le_stabilizer R hat)
  have hZzS : Z R z≤S := hZzT.trans (original_edge_le_stabilizer R hat)
  have hJS : J≤S := inf_le_right.trans (original_edge_le_stabilizer R hat)
  have hmove := original_full_radical_Z_displacement_le_moving h hinner path.end_color hzt
  have hRW : ⁅Z R a,Z R z⁆≤U R z := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZaT).trans hmove
  have hMW : ⁅Z R z,J⁆≤U R z := (commutator_mono le_rfl inf_le_right).trans hmove
  have hk : Disjoint ((U R z).subgroupOf S) (fixedProjection R a).ker := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxd : x∈fixedAttachment R a := (QuotientGroup.eq_one_iff _).mp hx.2
    exact (disjoint_iff.mp hdis).le ⟨hxd,hx.1⟩
  have hm := SaturatedDistanceTwo.P1Comparison.movement_le (fixedProjection R a)
    ((Z R z).subgroupOf S) (J.subgroupOf S)
    ((markedPointCore R κ u).subgroupOf S) ((U R z).subgroupOf S)
    ((⁅Z R a,Z R z⁆).subgroupOf S)
    (layerImage R a (Z R a)⊔layerImage R a (Z R z)) hk
    (subgroupOf_mono S hRW) (by
      rw [←SubgroupTransport.subgroupOf_commutator _ _ hZzS hJS]
      exact subgroupOf_mono S hMW)
    (subgroupOf_mono S inf_le_left) (by
      change _≤normalizer (layerImage R a ⁅Z R a,Z R z⁆ : Set (FixedQuotient R a))
      rw [layerImage_commutator R _ _ hZaS hZzS]
      exact sup_le (normalizer_commutator_ge_left _ _) (normalizer_commutator_ge_right _ _)) hcentral
  rw [←SubgroupTransport.subgroupOf_commutator _ _ hZzS hJS] at hm
  intro x hx
  exact hm (show (⟨x,((Subgroup.commutator_le_sup _ _).trans (sup_le hZzS hJS)) hx⟩ : S) ∈
    (⁅Z R z,J⁆).subgroupOf S from hx)

/-- The actual field-critical pair and marked point core rule out the
opposite section as the relative centralizer, once opposite disjointness
allows the complete fixed attachment to be removed. -/
theorem original_relativeCentralizer_not_opposite
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {g : Geometry R} {a z t : Vertex R} (path : CriticalPath R g a z)
    (hb : g.b R=2) (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n)
    (κ : stabilizer R a →* Sp E)
    (hκ : κ.ker=(Q R a).subgroupOf (stabilizer R a)) (u : Sp E)
    (hE : Nat.card E=2^n)
    (hroot : ((Z R z).subgroupOf (stabilizer R a)).map
      ((MulAut.conj u).toMonoidHom.comp κ)=RootSubgroup.group 0)
    (hdis : Disjoint (fixedCore R a) (U R z)) :
    ¬ layerImage R a (Z R z) ≤ relativeCentralizer R κ z u := by
  intro hcentral
  have hle := original_movement_le_critical_commutator h hinner path hb hat hzt κ u hdis hcentral
  have hRcard := original_source_field_critical_commutator_order h hshort hinner hnsyl
    g hb path hat hzt hcritical
  have hstrict := original_point_core_strict_movement h hinner hnsyl path hb hat hzt κ hκ u hE hroot
  let : Finite (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hRcard]; exact pow_ne_zero _ (by decide))
  exact (not_lt_of_ge ((Nat.card_le_card_of_injective (inclusion hle)
    (inclusion_injective hle)).trans_eq hRcard)) hstrict

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
