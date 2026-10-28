module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TriangleCoreIntersection
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TrianglePairCoreIntersection
public import Theory.SpecificGroups.MinusExtraspecial.AlternatingAction
public import Theory.GroupTheory.GaschutzCentralPreimage
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Splitting the actual involution-centralizer quotient

The original point centralizer meets the full involution core in the central
involution line. Modulo that line, their images have orders twelve and sixteen
and intersect trivially. Their join has index five, so Gaschütz supplies an
actual complement to the full core image. Its literal inverse image retains
both product identities and the original full-kernel quotient map.

The subgroup produced here has order 120. Containing both original marked
parabolic intersections is a further alignment duty; it is not a premise or
conclusion of this splitting step.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem image_card_mul_center (B : Subgroup H) (hB : center H ≤ B) :
    Nat.card (B.map (QuotientGroup.mk' (center H))) * Nat.card (center H) = Nat.card B := by
  have hh := relIndex_ker B (QuotientGroup.mk' (center H))
  have hc := ((center H).subgroupOf B).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv] at hc
  change (center H).relIndex B * Nat.card (center H) = Nat.card B at hc
  rw [QuotientGroup.ker_mk'] at hh
  rwa [hh] at hc

set_option maxHeartbeats 800000 in
private theorem central_quotient_split
    (Q X : Subgroup H) [Q.Normal]
    (eQ : Q ≃* MinusExtraspecial.Model)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (hself : centralizer (Q : Set H) ≤ Q)
    (hX : Nat.card X = 24) (hZX : center H ≤ X)
    (hinf : Q ⊓ X = center H) :
    let q := QuotientGroup.mk' (center H)
    Nat.card (center H) = 2 ∧ Nat.card (Q.map q) = 16 ∧
      Nat.card (X.map q) = 12 ∧ Disjoint (Q.map q) (X.map q) ∧
      (Q.map q ⊔ X.map q).index = 5 ∧
      ∃ K : Subgroup (H ⧸ center H), (Q.map q).IsComplement' K := by
  let q := QuotientGroup.mk' (center H)
  let V := Q.map q
  let U := X.map q
  have hZeq : center H = (center Q).map Q.subtype :=
    MinusExtraspecial.AlternatingAction.center_eq_center_image Q eQ hself
  have hZQ : center H ≤ Q := hZeq ▸ map_subtype_le _
  have hZ : Nat.card (center H) = 2 := by
    rw [hZeq, card_map_of_injective Q.subtype_injective,
      Nat.card_congr (Subgroup.centerCongr eQ).toEquiv]
    exact MinusExtraspecial.card_center
  have hQ : Nat.card Q = 32 := (Nat.card_congr eQ.toEquiv).trans MinusExtraspecial.card_model
  have hH : Nat.card H = 1920 := by
    rw [card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr eA.toEquiv,
      nat_card_alternatingGroup, hQ]
    norm_num
  have hW : Nat.card (H ⧸ center H) = 960 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (center H)
    rw [hZ,hH] at hh
    omega
  have hV : Nat.card V = 16 := by
    have hh := image_card_mul_center Q hZQ
    rw [hZ,hQ] at hh
    change Nat.card V * 2 = 32 at hh
    omega
  have hU : Nat.card U = 12 := by
    have hh := image_card_mul_center X hZX
    rw [hZ,hX] at hh
    change Nat.card U * 2 = 24 at hh
    omega
  let : V.Normal := QuotientGroup.map_normal (center H) Q
  have hd : Disjoint V U := by
    rw [disjoint_iff]
    change Q.map q ⊓ X.map q = ⊥
    rw [← map_inf_of_ker_le q Q X (by simpa only [q,QuotientGroup.ker_mk'] using hZX), hinf]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  let : IsExtraspecial 2 Q := IsExtraspecial.of_mulEquiv eQ.symm inferInstance
  have hder : ⁅Q,Q⁆ = center H := by
    rw [← map_subtype_commutator, IsExtraspecial.commutator_eq_center (p := 2), ←hZeq]
  let : IsMulCommutative V := commutator_self_eq_bot_iff.mp (by
    change ⁅Q.map q,Q.map q⁆ = ⊥
    rw [←map_commutator,hder]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  let J := V ⊔ U
  have hJ : Nat.card J = 192 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint V U le_normalizer_of_normal hd,hV,hU]
  have hi : J.index = 5 := by
    have hh := J.index_mul_card
    rw [hJ,hW] at hh
    omega
  have hs : (V.subgroupOf J).IsComplement' (U.subgroupOf J) := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [Nat.card_congr (subgroupOfEquivOfLe (show V ≤ J from le_sup_left)).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe (show U ≤ J from le_sup_right)).toEquiv,
        hV,hU,hJ]
    · apply disjoint_def.mpr
      intro x hxV hxU
      exact Subtype.ext (disjoint_def.mp hd hxV hxU)
  exact ⟨hZ,hV,hU,hd,hi,exists_complement_of_coprime_overgroup V J le_sup_left
    (by rw [hV,hi]; decide) ⟨U.subgroupOf J,hs⟩⟩


open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 800000 in
/-- The actual index-five point image supplies a complement to the full
central core quotient, with its original central preimage and quotient map. -/
theorem literal_triangle_quotient_splitting
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    let f := j SingerField.fieldElement
    let H := Janko23.involutionCentralizer f
    let Q := Janko23.localCore f
    let X := (j.range ⊓ H).subgroupOf H
    let q := QuotientGroup.mk' (center H)
    (center H).map H.subtype = zpowers f ∧
      Nat.card (center H) = 2 ∧ Nat.card (Q.map q) = 16 ∧
      Nat.card (X.map q) = 12 ∧ Disjoint (Q.map q) (X.map q) ∧
      (Q.map q ⊔ X.map q).index = 5 ∧
      ∃ K : Subgroup (H ⧸ center H), (Q.map q).IsComplement' K ∧
        ∃ R : Subgroup H, R = K.comap q ∧ center H ≤ R ∧
          Q ⊓ R = center H ∧ Q ⊔ R = ⊤ ∧ Nat.card R = 120 ∧
          ∃ r : R →* H ⧸ Q, Function.Surjective r ∧
            r.ker = (center H).subgroupOf R ∧
            ∀ x : R, r x = QuotientGroup.mk' Q (x : H) := by
  let f := j SingerField.fieldElement
  let H := Janko23.involutionCentralizer f
  let Q := Janko23.localCore f
  let X := (j.range ⊓ H).subgroupOf H
  let q := QuotientGroup.mk' (center H)
  have hf : orderOf f = 2 := image_involution_order j hj.1
  obtain ⟨⟨eQ⟩,_,⟨eA⟩⟩ := literal_involution_core_and_quotient (D := D) hc f hf
  have hself : centralizer (Q : Set H) ≤ Q := centralizer_generalizedFitting_le H
  have hZeq : center H = (center Q).map Q.subtype :=
    MinusExtraspecial.AlternatingAction.center_eq_center_image Q eQ hself
  have hZcard : Nat.card (center H) = 2 := by
    rw [hZeq,card_map_of_injective Q.subtype_injective,
      Nat.card_congr (Subgroup.centerCongr eQ).toEquiv]
    exact MinusExtraspecial.card_center
  let fH : H := ⟨f,mem_centralizer_singleton_iff.mpr rfl⟩
  have hfZ : fH ∈ center H := mem_center_iff.mpr fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have hZline : center H = zpowers fH := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hfZ) ?_).symm
    rw [Nat.card_zpowers, ←orderOf_coe, hf,hZcard]
  have hZmap : (center H).map H.subtype = zpowers f := by
    rw [hZline,MonoidHom.map_zpowers]
    rfl
  have hXmap : X.map H.subtype = j.range ⊓ H := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hXQ : Q ⊓ X = center H := by
    apply map_injective H.subtype_injective
    rw [map_inf _ _ _ H.subtype_injective,hXmap,hZmap]
    change Janko23.ambientCore f ⊓ (j.range ⊓ H) = zpowers f
    rw [inf_comm]
    exact literal_triangle_point_core_intersection P hc A C a j hj
  have hZX : center H ≤ X := by rw [←hXQ]; exact inf_le_right
  have hXcard : Nat.card X = 24 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show j.range ⊓ H ≤ H from inf_le_right)).toEquiv,
      Nat.card_congr (PointCentralizer.imagePointCentralizerEquiv j hj.1).toEquiv,
      Nat.card_prod,alternatingGroup.card_of_card_eq_four (by simp)]
    norm_num [Nat.card_eq_fintype_card]
  obtain ⟨hZ,hV,hU,hd,hi,K,hK⟩ := central_quotient_split Q X eQ eA hself hXcard hZX hXQ
  obtain ⟨R,hR,hZR,hQR,hgen,r,hr,hker,hrep⟩ :=
    exists_preimage_of_quotient_complement Q (center H)
      (hZeq ▸ map_subtype_le _) K hK
  have hRcard : Nat.card R = 120 := by
    have hk : Nat.card r.ker = 2 := by
      rw [hker,Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv,hZ]
    have hh := r.ker.index_mul_card
    rw [index_ker,MonoidHom.range_eq_top.mpr hr,
      Nat.card_congr (topEquiv (G := H ⧸ Q)).toEquiv,
      Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,hk] at hh
    norm_num at hh
    exact hh.symm
  exact ⟨hZmap,hZ,hV,hU,hd,hi,K,hK,R,hR,hZR,hQR,hgen,hRcard,r,hr,hker,hrep⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
