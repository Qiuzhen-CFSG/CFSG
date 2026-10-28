module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.ParabolicImage
public import Theory.GroupTheory.SylowNormalIntersectionIndex
public import Theory.SpecificGroups.SL3.BinaryPointStabilizer

/-!
# The actual point-parabolic intersection in the larger component

Inside the original G₁/O₂(G₁), restrict M₁* to the normal component K₁*.
The factorization M₁ = YL₁T, with Y and L₁ in K₁, makes this intersection
contain a Sylow subgroup of K₁* of relative index 63. This is computed
from the original two-block quotient M₁*/O₂(M₁*) of order 1008;
no larger-component embedding is assumed. If V is not in O₂(G₁), its
literal image restricts to a normal elementary eight-group in the same
intersection. Both statements retain the original quotient projection.

The linear consumer is in `PointCore/LinearComponent`. The remaining
sporadic embeddings belong to qt-d-1251-local; the final exterior assembly
belongs to qt-d-1251-source.

Source: Aschbacher--Smith, 12.5.3 and 12.5.8(1), printed pp.818, 820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The original point normalizer, intersected with the actual component image. -/
@[expose] def pointComponentParabolic (K : Subgroup G) : Subgroup (s.pointCoreImage K) :=
  (s.pointCoreImage (s.marking.Mi 1)).subgroupOf (s.pointCoreImage K)

omit [Finite G] in
private theorem point_image_sup {A B : Subgroup G}
    (hA : A ≤ s.marking.Gi 1) (hB : B ≤ s.marking.Gi 1) :
    s.pointCoreImage (A ⊔ B) = s.pointCoreImage A ⊔ s.pointCoreImage B := by
  rw [pointCoreImage, subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

private theorem point_image_supplement {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hLK : s.marking.Li 1 ≤ K) (hY : s.Y ≤ K) :
    s.pointCoreImage (s.marking.Mi 1) ≤ s.pointCoreImage K ⊔ s.pointCoreImage (T : Subgroup G) := by
  have hm : s.marking.Mi 1 ≤ K ⊔ (T : Subgroup G) := by
    rw [s.M₁_eq_Y_sup_point_residual_sup_sylow]
    exact sup_le_sup (sup_le hY hLK) le_rfl
  exact (s.pointCoreImage_mono hm).trans_eq (s.point_image_sup hK s.sylow_le_G₁)

/-- The original two-block quotient has order 1008 in the star group. -/
theorem pointCoreImage_M₁_core_card :
    Nat.card (s.pointCoreImage (s.marking.Mi 1) ⧸ pCore 2 (s.pointCoreImage (s.marking.Mi 1))) = 1008 := by
  rw [Nat.card_congr s.pointCoreImage_M₁CoreEquiv.toEquiv, Nat.card_prod,
    Nat.card_congr (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).toEquiv,
    Nat.card_perm, Nat.card_fin, BinaryLinear.NaturalThreePoint.group_card]
  rfl

/-- The same literal Sylow intersection has index 63 inside the component parabolic. -/
theorem pointComponentParabolic_sylow_index {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hLK : s.marking.Li 1 ≤ K) (hY : s.Y ≤ K) :
    ∃ S : Sylow 2 (s.pointCoreImage K), (S : Subgroup _) ≤ s.pointComponentParabolic K ∧
      (S : Subgroup _).relIndex (s.pointComponentParabolic K) = 63 := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := (T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let C := s.pointCoreImage K
  let A := s.pointCoreImage (s.marking.Mi 1)
  have hR : (R : Subgroup _) = s.pointCoreImage (T : Subgroup G) := rfl
  have hRA : (R : Subgroup _) ≤ A :=
    s.pointCoreImage_mono (le_inf le_sup_right s.sylow_le_G₁)
  let : (K.subgroupOf H).Normal := hn
  let : C.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨S,hS⟩ := R.exists_subgroupOf_eq_of_normal C
  refine ⟨S, ?_, ?_⟩
  · rw [hS]
    exact comap_mono hRA
  · change (S : Subgroup C).relIndex (A.subgroupOf C) = 63
    have hsupp := s.point_image_supplement (K := K) hK hLK hY
    rw [hS, hR]
    rw [normal_intersection_relIndex (s.pointCoreImage (T : Subgroup G)) A C hRA hsupp]
    exact (R.subtype hRA).index_eq_sixtyThree_of_core_card s.pointCoreImage_M₁_core_card

/-- Failure of point-core containment supplies the normal eight-group inside the
actual component intersection, not merely inside an abstract model of M₁. -/
theorem pointComponentParabolic_seed_normal_eight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {K : Subgroup G} (hLK : s.marking.Li 1 ≤ K)
    (hf : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    ∃ B : Subgroup (s.pointComponentParabolic K),
      B.Normal ∧ IsElementaryAbelian 2 B ∧ Nat.card B = 8 := by
  let C := s.pointCoreImage K
  let A := s.pointComponentParabolic K
  let B := (s.pointCoreImage V).subgroupOf C
  have hvK : s.pointCoreImage V ≤ C :=
    s.pointCoreImage_mono (s.seed_le_point_residual.trans hLK)
  have hvA : B ≤ A := comap_mono (s.pointCoreImage_mono s.seed_le_M₁)
  have hn : (B.subgroupOf A).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hvA).mpr
    intro m hm b
    exact s.pointCoreImage_M₁_normalizes_seed hm (b : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1))
  let := s.pointCoreImage_seed_elementary
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hvK
  refine ⟨B.subgroupOf A, hn, IsElementaryAbelian.subgroupOf hvA, ?_⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe hvA).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hvK).toEquiv]
  exact s.pointCoreImage_seed_card h hf
end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
