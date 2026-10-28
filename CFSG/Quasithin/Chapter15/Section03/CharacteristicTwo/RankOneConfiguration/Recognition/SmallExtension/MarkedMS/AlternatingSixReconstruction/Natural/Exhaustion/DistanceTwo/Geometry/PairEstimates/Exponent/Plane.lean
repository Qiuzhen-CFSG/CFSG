module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Exponent.Model
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.CriticalTransposition.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Source

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.PlaneContainment

/-!
# The actual critical-plane commutator misses the opposite fixed attachment

Use the original opposite-edge coordinates and recognize its central critical
image as a transposition. The plane lies in the original kernel and hence
centralizes that image. The whole-cover fixed-hyperplane calculation then
makes its commutator disjoint from the opposite component-fixed attachment.
Every map is the literal source projection or edge embedding; both whole-cover
orders sixteen and thirty-two remain possible.

Source: MS93 (3.6), printed p.871. Exponent.Source applies this separation to
the paired commutator squares. No local-image or plane-intersection input is
used by this plane-commutator statement.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
open LocalImages LargeDistance PlaneMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz hn in
/-- The actual critical-plane commutator misses the opposite component's
fixed attachment, even when the moved cover has order thirty-two. -/
theorem plane_commutator_inf_opposite_fixed_eq_bot
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b) :
    ⁅Q d.radical (alpha d.radical),criticalPlane d.radical c b⁆ ⊓
      centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) = ⊥ := by
  obtain ⟨A,T,hAT,hTR,hAc,hTA,hne,_,_,hfix,hindex,
      b',i,hi,hAm,hab',hcb',hTm,hiW,hiS,hiL⟩ :=
    critical_image_data_coordinates_full h e hz hn d hb hlarge hc
  let q := Recognition.sourceProjection h e hz hn d
  let := hAc
  have hp : IsPGroup 2 (T.map q) :=
    ((replacement_radical_isPGroup h d).of_injective (inclusion hTR) (inclusion_injective _)).map q
  have hcent : T.map q ≤ centralizer (A.map q : Set (Equiv.Perm (Fin 6))) := by
    rintro _ ⟨y,hy,rfl⟩ _ ⟨a,ha,rfl⟩
    exact (map_mul q a y).symm.trans ((congrArg q (hTA hy a ha)).trans (map_mul q y a))
  have hnq := critical_image_nonquadratic h e hz hn d hb hlarge hc hab' hcb' T i hi hTm hiW hiS
  have hnon : A.map q ≠ ⊥ := by
    intro he
    exact hne ((Recognition.sourceProjection_kernel h e hz hn d) ▸
      (Subgroup.map_eq_bot_iff A).mp he)
  obtain ⟨t,ht,ht1⟩ := (A.map q).bot_or_exists_ne_one.resolve_left hnon
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map _
  have hswap := isSwap_of_nonquadratic_fixer (A.map q) (T.map q) hp
    (map_mono hAT) hcent hfix hnq ht ht1
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht)
  have hcard : Nat.card (A.map q) = 2 := hindex.symm.trans
    (critical_image_two h e hz hn d hb hlarge hc)
  have he : A.map q = zpowers t := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr ht) ?_).symm
    rw [hcard,Nat.card_zpowers,hswap.orderOf]
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let W := replacementMoved d
  let S := omegaCenter d.radical
  let V := (criticalPlane d.radical c b).comap i
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hZc : Z d.radical c = (W ⊔ S).map i := by
    rw [Subgroup.map_sup,hiW,hiS]
    exact CentralLayer.Z_eq_moving_sup_edge_at h e hz d hc0 hcb'
  have hV : V ≤ W ⊔ S := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [←hZc]
    exact (map_comap_le _ _).trans (criticalPlane_le_opposite c b)
  have hVm : V.map i = criticalPlane d.radical c b := by
    apply map_comap_eq_self
    exact (criticalPlane_le_opposite c b).trans (hZc ▸ map_le_range _ _)
  have hVA : V ≤ centralizer (A : Set d.overgroup) := by
    intro v hv a ha
    apply hi
    rw [map_mul,map_mul]
    have hvQ := replacement_plane_le_intersection h e hz d hb hlarge hc hab hcb hv
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical (alpha d.radical) rfl) (hAm ▸ mem_map_of_mem i ha) _ hvQ.2).symm
  have hSA : S ≤ centralizer (A : Set d.overgroup) := by
    intro s hs a ha
    exact (mem_omegaCenter_iff.mp hs).2.2 a (hTR (hAT ha))
  have hST : S ≤ centralizer (T : Set d.overgroup) := by
    intro s hs a ha
    exact (mem_omegaCenter_iff.mp hs).2.2 a (hTR ha)
  have hq := sourceProjection_surjective_of_nonfrattini h e hz hn d hb hlarge
  have hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
    (moved_centralizer h e hz hn d).symm
  have hnzero := commutator_inf_fixed_of_transposition W q hq hk (pResidual 2 d.overgroup)
    (Recognition.sourceProjection_component h e hz hn d)
    (moved_cover_model h e hz hn d hq) A T S V t hswap he hTA hSA hST hV hVA
  have hD : (⁅T,V⁆ : Subgroup d.overgroup).map i =
      ⁅Q d.radical (alpha d.radical),criticalPlane d.radical c b⁆ := by
    rw [map_commutator,hTm,hVm]
  apply _root_.eq_bot_iff.mpr
  rintro x ⟨hx,hxC⟩
  rw [←hD] at hx
  obtain ⟨z,hzmem,rfl⟩ := hx
  have hzC : z ∈ centralizer (pResidual 2 d.overgroup : Set d.overgroup) := by
    intro k hkK
    apply hi
    rw [map_mul,map_mul]
    exact hxC (i k) (hiL ▸ mem_map_of_mem i hkK)
  have hz1 : z = 1 := mem_bot.mp (hnzero ▸ ⟨hzmem,hzC⟩)
  rw [hz1,map_one]
  exact one_mem _

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
