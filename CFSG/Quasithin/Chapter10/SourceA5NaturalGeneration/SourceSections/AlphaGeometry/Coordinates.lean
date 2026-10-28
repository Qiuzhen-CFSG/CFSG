module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaGeometry.Field
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaPlacement
public import CFSG.Quasithin.Chapter10.SourceA5LocalCentralQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.SourceGeometry
/-!
# Natural coordinates with the original product quotient diagram

The same selected paired source gives a coordinate map on the original
module. Its residual-fixed kernel vanishes when the original Sylow center
has trivial orbit centralizer. The original A5-pair embedding lands in the
selected layer; the actual field-order-four theorem makes its order equal
to that layer, so it is an isomorphism. The resulting group marking and
module coordinates retain the literal original quotient diagram.

Source: Aschbacher--Smith 10.2.3(4), printed p.746, using E.2.3(2).
-/
public section
open Matrix Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem source_original_module_marking_of_selected_source
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)))
    (hpair : SourceOriginalPairedLinear D) :
    ∃ F : BinaryField, Nat.card F.Carrier = 4 ∧
      ∃ (a : (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ≃*
        (SL(2,F.Carrier) × SL(2,F.Carrier)))
        (m : D.moduleSubgroup →* Multiplicative ((Fin 2 → F.Carrier) × (Fin 2 → F.Carrier))),
        Function.Bijective m ∧ ∀ (r : localOrbit T L) (v : D.moduleSubgroup),
          (m ⟨(r:G)*v*(r:G)⁻¹,
            (mem_normalizer_iff.mp (D.orbit_normalizes_module r.property) v).mp v.property⟩).toAdd =
          (((a (originalA5ProductProjection D e hn ht htn r)).1).val *ᵥ (m v).toAdd.1,
            ((a (originalA5ProductProjection D e hn ht htn r)).2).val *ᵥ (m v).toAdd.2) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set X) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  obtain ⟨d,F,⟨c⟩,hexchange⟩ := hpair
  have hF := source_original_paired_field_card D e hn hJ d F c hexchange
  let V := Fin 2 → F.Carrier
  have hP := source_a5_minimal_parabolic D e hn
  have hcore : pCore 2 (X ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [←hk,he]
    exact le_top
  have hp := (minimalParabolic_reduced_image S hP q hq hcore hne).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk S
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
    · exact hf
  have hc : c.quotientMap.ker = fixedSpace α ((pResidual 2 X).map q) := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact source_offender_pair_linear_kernel α (S.mapSurjective hq) hp hff hcore F c
  have hJY : (elementaryAbelianMaxJ (S : Subgroup X)).map q ≤ Y :=
    RankOneBaumann.thompson_image_le_offender_layer S U q hq hk
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) Y le_rfl
  have hRY := RankOneBaumann.residual_image_le_normal_thompson_layer S hP U hU hJ q hq hk Y hJY
  let R := localOrbit T L
  have hRX : R ≤ X := le_sup_left
  have hUX : D.moduleSubgroup ≤ X := D.module_le_core.trans (pCoreIn_le 2 X)
  have hrx : pResidual 2 X = R.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [source_join_residual D,map_subgroupOf_eq_of_le hRX]
  obtain ⟨i,hi,_,hdiag⟩ := source_a5_local_product_embedding D e hn ht htn
  let j : (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) →* Y :=
    i.codRestrict Y (by
      intro a
      obtain ⟨r,rfl⟩ := originalA5ProductProjection_surjective D e hn ht htn a
      rw [hdiag]
      apply hRY
      apply mem_map_of_mem
      rw [hrx]
      exact r.property)
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  have hcard : Nat.card (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = Nat.card Y := by
    rw [Nat.card_congr c.action.groupEquiv.toEquiv,Nat.card_prod,Nat.card_prod,
      nat_card_alternatingGroup,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    norm_num [Nat.factorial]
  let a := (MulEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨hj,hcard⟩)).trans
    c.action.groupEquiv
  let ue : U ≃* D.moduleSubgroup := subgroupOfEquivOfLe hUX
  let m : D.moduleSubgroup →* Multiplicative (V × V) := {
    toFun v := Multiplicative.ofAdd (c.quotientMap (Additive.ofMul (ue.symm v)))
    map_one' := by rw [map_one]; exact c.quotientMap.map_zero
    map_mul' := by
      intro x y
      rw [map_mul]
      exact c.quotientMap.map_add _ _ }
  have hinj : Function.Injective c.quotientMap := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hvc := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk (pResidual 2 X) v).mp
      (hc ▸ hv)
    have hvT : (v.toMul.val:G) ∈ (T : Subgroup G) :=
      hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S) v.toMul.property
    have hvR : (v.toMul.val:G) ∈ centralizer (R : Set G) := by
      intro r hr
      have hr' : r ∈ (pResidual 2 X).map X.subtype := by
        rw [source_join_residual D]
        exact hr
      obtain ⟨x,hx,rfl⟩ := hr'
      exact congrArg X.subtype (hvc x hx)
    have he : (v.toMul.val:G) = 1 :=
      mem_bot.mp ((source_sylow_orbit_centralizer_eq_bot hz).le ⟨hvT,hvR⟩)
    change v = 0
    exact Additive.toMul.injective (Subtype.ext (Subtype.ext he))
  have hm : Function.Bijective m := by
    constructor
    · intro v w h
      have hh := hinj (congrArg Multiplicative.toAdd h)
      exact ue.symm.injective (Additive.toMul.injective hh)
    · intro v
      obtain ⟨x,hx⟩ := c.quotientMap_surjective v.toAdd
      refine ⟨ue x.toMul,?_⟩
      change Multiplicative.ofAdd (c.quotientMap (Additive.ofMul (ue.symm (ue x.toMul)))) = v
      rw [ue.symm_apply_apply]
      exact hx
  refine ⟨F,hF,a,m,hm,?_⟩
  intro r v
  have hh := c.quotientMap_action (j (originalA5ProductProjection D e hn ht htn r))
    (Additive.ofMul (ue.symm v))
  have hconj : α (q (inclusion hRX r)) (Additive.ofMul (ue.symm v)) =
      Additive.ofMul (ue.symm ⟨(r:G)*v*(r:G)⁻¹,
        (mem_normalizer_iff.mp (D.orbit_normalizes_module r.property) v).mp v.property⟩) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply U q hq hk (inclusion hRX r) (ue.symm v)
  change c.quotientMap (α (i (originalA5ProductProjection D e hn ht htn r)) _) = _ at hh
  rw [hdiag,hconj] at hh
  exact hh
end CFSG.Quasithin.Chapter10
