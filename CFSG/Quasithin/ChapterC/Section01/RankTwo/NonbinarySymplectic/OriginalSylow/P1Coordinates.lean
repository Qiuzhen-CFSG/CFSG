module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.RootSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.PointGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.QuotientOverlap

/-!
# The actual opposite-section marking on the original full Sylow star

At an original field-sized critical pair, the whole-core theorem supplies
the natural kernel after the complete fixed attachment is divided out.
Choose its ambient natural cover once. Its own action selects the opposite
long root, and the same inner conjugation marks both sections. The overlap
index survives the fixed quotient. Elementary-pair geometry then proves
that the original point-parabolic preimage normalizes the opposite image.

Thus all fields of the two-section marking are constructed from the
original source hypotheses, with no assumed module inequivalence or
point-parabolic normalization. The subsequent relative-centralizer and
movement argument is separate.

Source: MS93 (3.7), printed pp.876--877.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Representation.OneCohomology.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour OriginalStar OriginalStar.P1Comparison
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hshort hsyl

/-- Construct the natural/opposite section marking at the actual original
critical pair. Both coordinate axes use a single chosen cover quotient. -/
theorem exists_original_marked_pair
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ∃ cv : AmbientVertexCover R (originalMovedSection h) n a,
      ∃ u : Sp cv.field.Carrier,
        Nonempty (ParabolicOppositeSections.MarkedPair
          (markedQuotient R (coverQuotient h hinner cv)
            (coverQuotient_kernel h hinner cv) u)
          (layerImage R a (Z R a)) (layerImage R a (Z R z))) := by
  have hcritical := (original_critical_indices_eq_field_of_full_sylow
    h hshort hinner hsyl path hb hat hzt).1
  let : Finite (stabilizer R a) := finite_stabilizer R a
  let : Finite (FixedQuotient R a) :=
    inferInstanceAs (Finite (stabilizer R a ⧸ fixedAttachment R a))
  let : IsElementaryAbelian 2 (Z R z) := g.Z_elementary (by omega) z path.end_color
  let : IsElementaryAbelian 2 ((Z R z).subgroupOf (stabilizer R a)) :=
    IsElementaryAbelian.subgroupOf (by
      apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
      rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
        g.distance_constant z path.end_color])
  let : IsElementaryAbelian 2 (layerImage R a (Z R z)) :=
    IsElementaryAbelian.map _
  obtain ⟨cv⟩ := exists_ambient_cover h path.start_color
  obtain ⟨u,hroot⟩ := exists_critical_root_image h hinner path (by omega) hcritical cv
  have hwhole := (original_source_three_of_full_sylow h hshort hinner hsyl
    g hb path hat hzt).2.1
  have he := whole_layer_eq_core R hb path.start_color hwhole
  obtain ⟨natural,hconj⟩ := natural_coordinates h hinner cv hwhole u
  let κ := markedQuotient R (coverQuotient h hinner cv)
    (coverQuotient_kernel h hinner cv) u
  have hk : κ.ker = layerImage R a (Q R a) := markedQuotient_kernel R _ _ u
  have hi : (layerImage R a (Z R z)).relIndex (layerImage R a (Q R a)) =
      Nat.card cv.field.Carrier := by
    rw [←he,cv.field.card_eq,cv.degree]
    exact original_source_critical_quotient_overlap h hshort hinner hsyl
      g hb path hat hzt (fixedProjection R a) (QuotientGroup.ker_mk' _)
  have hn := point_parabolic_normalizes_opposite κ (layerImage R a (Q R a))
    (layerImage R a (Z R z)) hk natural hconj hroot hi
  refine ⟨cv,u,?_⟩
  rw [he]
  exact ⟨{
    onto := markedQuotient_onto R _ _ (coverQuotient_onto h hinner cv) u
    kernel := hk
    natural := natural
    natural_conjugation := hconj
    root_image := hroot
    opposite_commutative := inferInstance
    opposite_normalized := hn
    intersection_index := hi }⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
