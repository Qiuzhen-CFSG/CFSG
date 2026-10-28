module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalSpecialLinearFour
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointSylowOuter
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
/-!
# The original supplement of the full SL₃(4) component

The original equality H=KT makes H-star/K-star a two-group. Its being
cyclic would put the kernel of a cyclic image of the original T inside
O₂(L₁T), contradicting the marked four-block Sylow quotient. The normal
quasisimple component is therefore the full generalized Fitting subgroup.
The odd scalar center and both original quotient maps are retained.

Source: Aschbacher–Smith 12.6.31(1), printed pp.836–837. Identifying the
outer quotient as E₄ and the graph-module analysis remain source duties.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)



include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The unchanged component quotient has a noncyclic two-group supplement;
the full special-linear component, including its center, is F*(H-star). -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_quotient
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H)
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    letI : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
    IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ actorImage H K) ∧
      ¬ IsCyclic ((H ⧸ pCore 2 H) ⧸ actorImage H K) ∧
      generalizedFitting (H ⧸ pCore 2 H) = actorImage H K := by
  let E := D.fullSetup hZ T z
  let B := actorImage H K
  let π := QuotientGroup.mk' (pCore 2 H)
  let : B.Normal := hn.map π (QuotientGroup.mk'_surjective _)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  obtain ⟨_,hg⟩ := S.original_abelian_normal_specialLinearFour_reduction
    D hZ z hz hTV hTz hbound hTI hns hH hKH hgen hn hm
  have hsup : B ⊔ actorImage H T = ⊤ := by
    unfold B actorImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hKH hTH,hg,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (actorImage H T)
      (T.isPGroup'.comap_subtype.map π) hsup
  have hq : IsQuasisimple B :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  let _ := hq
  refine ⟨hquot,?_,generalizedFitting_eq_of_quasisimple_two_quotient B hquot
    (pCore_quotient_pCore_eq_bot 2)⟩
  intro hcyc
  let _ := hcyc
  let f : T →* ((H ⧸ pCore 2 H) ⧸ B) :=
    (QuotientGroup.mk' B).comp (π.comp (inclusion hTH))
  have hcore := S.original_abelian_normal_specialLinearFour_sylow_le_edge_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm
  apply S.original_point_sylow_cyclic_kernel_impossible D hZ z hz hTz f
  intro t ht
  have hb : π (inclusion hTH t) ∈ B := (QuotientGroup.eq_one_iff _).mp ht
  obtain ⟨k,hk,he⟩ := hb
  have hdiff : inclusion hTH t * k⁻¹ ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (inclusion hTH t * k⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hdiffR : (t : G) * (k : G)⁻¹ ∈ E.R₁ :=
    S.original_core_le_point_core D hZ z hH (mem_map_of_mem H.subtype hdiff)
  have hRT : E.R₁ ≤ (T : Subgroup G) := (S.original_point_core_eq D hZ z hz hTz).2.2
  have hkT : (k : G) ∈ (T : Subgroup G) := by
    have hh := (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hRT hdiffR)) t.property
    simpa only [mul_inv_rev,inv_inv,inv_mul_cancel_right] using hh
  have hh := E.R₁.mul_mem hdiffR (hcore ⟨hkT,hk⟩)
  change (t : G) ∈ E.R₁
  simpa only [inv_mul_cancel_right] using hh

end CFSG.Quasithin.Chapter12.Section06
