module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalRankTwo
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointSylowOuter
public import Theory.GroupTheory.OuterKernelPSupplement
/-!
# Excluding the original normal symplectic and G₂ components

In either row L₁-star lies in K-star, so H-star is K-star times T-star.
The centerless component has trivial centralizer: that centralizer embeds
in the binary quotient by K-star and O₂(H-star)=1. Thus the literal outer
action has kernel K-star. Lifting its restriction to the original T
through the full O₂(H) kernel puts the kernel in R₁, using the already
proved T intersect K <= R₁. A cyclic outer group now contradicts the
noncyclic original point-Sylow quotient.

The model automorphism theorems discharge cyclicity separately for Sp₄
and G₂. Both quotient maps and the original normal component are retained.
No even-field or degree-two assumption is added to these exclusions.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
AbelianClassicalSieve applies the exclusions to the original reduced actor.
The signed degree-three and later module/terminal branches remain with
the universal NaturalReduction assembly.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTz hH hKH hgen in
/-- The literal outer action contradicts the original noncyclic point-Sylow image. -/
theorem SourceHypothesis.original_normal_cyclic_outer_impossible
    (hn : (K.subgroupOf H).Normal)
    [IsCyclic (MulAut.Outer (actorImage H K))]
    (hzK : center (actorImage H K) = ⊥)
    (hpoint : actorImage H (D.fullSetup hZ T z).L₁ ≤ actorImage H K)
    (hcore : (T : Subgroup G) ⊓ K ≤ (D.fullSetup hZ T z).R₁) : False := by
  let E := D.fullSetup hZ T z
  let B := actorImage H K
  let π := QuotientGroup.mk' (pCore 2 H)
  let : B.Normal := hn.map π (QuotientGroup.mk'_surjective _)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hgenstar : B ⊔ actorImage H T = ⊤ := by
    have hg := hgen
    rw [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hg
    have hh : B ⊔ actorImage H E.L₁ ⊔ actorImage H T = ⊤ := by
      unfold B actorImage
      rw [←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hKH hLH,
        ←subgroupOf_sup (sup_le hKH hLH) hTH,hg,subgroupOf_self,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rwa [sup_eq_left.mpr hpoint] at hh
  let a : (H ⧸ pCore 2 H) →* MulAut.Outer B :=
    (QuotientGroup.mk' (MulAut.innerSubgroup B)).comp MulAut.conjNormal
  have hak : a.ker = B := outer_action_kernel_of_centerless_p_supplement B
    (actorImage H T) (T.isPGroup'.comap_subtype.map π) hgenstar hzK
    (pCore_quotient_pCore_eq_bot 2)
  let f : T →* MulAut.Outer B := a.comp (π.comp (inclusion hTH))
  apply S.original_point_sylow_cyclic_kernel_impossible D hZ z hz hTz f
  intro t ht
  have hb : π (inclusion hTH t) ∈ B := hak ▸ ht
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

private theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : center Y = ⊥) : center X = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x = 1 := mem_bot.mp (h ▸ ((centerCongr e) ⟨x,hx⟩).property)
  exact mem_bot.mpr (e.map_eq_one_iff.mp he)

include hz hTV hTz hH hKH hK hgen in
/-- The original normal symplectic component is impossible. -/
theorem SourceHypothesis.original_abelian_normal_symplectic_impossible
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) : False := by
  have hpoint := S.original_abelian_normal_symplectic_point_le D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  have hcore := S.original_abelian_normal_rankTwo_sylow_le_edge_core D hZ z hz hTV hTz hH hKH hK hgen hn hn2 (Or.inl hm)
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))
  let e := (componentStarEquiv H K hKH hK).symm.trans
    (eK.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hq))
  let : IsCyclic (MulAut.Outer (Theory.SpecificGroups.SymplecticFour.Sp F)) :=
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card
      hcard (by omega)
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  let : IsCyclic (MulAut.Outer (actorImage H K)) := (MulAut.outerCongr e).isCyclic.mpr inferInstance
  exact S.original_normal_cyclic_outer_impossible D hZ z hz hTz hH hKH hgen hn
    (center_eq_bot_of_equiv e Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot) hpoint hcore

include hz hTV hTz hH hKH hK hgen in
/-- The original normal G₂ component is impossible. -/
theorem SourceHypothesis.original_abelian_normal_g2_impossible
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : Models.IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ n)) : False := by
  have hpoint := S.original_abelian_normal_g2_point_le D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  have hcore := S.original_abelian_normal_rankTwo_sylow_le_edge_core D hZ z hz hTV hTz hH hKH hK hgen hn hn2 (Or.inr hm)
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) (by omega))
  let e := (componentStarEquiv H K hKH hK).symm.trans
    (eK.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard))
  let : IsCyclic (MulAut.Outer (Atlas.G2.Model F)) :=
    Atlas.G2.LieAutomorphismExtensions.outer_isCyclic hq
  let : IsCyclic (MulAut.Outer (actorImage H K)) := (MulAut.outerCongr e).isCyclic.mpr inferInstance
  exact S.original_normal_cyclic_outer_impossible D hZ z hz hTz hH hKH hgen hn
    (center_eq_bot_of_equiv e (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq)) hpoint hcore
end CFSG.Quasithin.Chapter12.Section06
