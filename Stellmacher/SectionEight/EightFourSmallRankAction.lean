module
public import Stellmacher.SectionEight.EightFourFaithfulSylowMaximal
public import Stellmacher.SectionEight.GeneratedEightFiveCenterFour
public import Stellmacher.SectionOne.SmallFixedIndexRank

/-!
# The action-theoretic rank step of Stellmacher (8.4)

For the original quotient witness, all hypotheses of the Section One
small-fixed-index theorem follow from the initial residual join, the actual
maximal Sylow image, and the trivial residual centralizer. The only geometric
input of this reduction is the exact doubling of the J-fixed cardinal over
the Sylow-fixed cardinal. Faithfulness and the nonzero offender join make the
J-fixed subgroup proper. Two-group fixed-point parity then gives the strict
module bound greater than four, without any assumed rank or order bound.

A generating canonical factor bounds the Sylow-fixed cardinal by two; hence
the exact doubling also gives the original ambient fixed subgroup order four.
The first public theorem is an entirely action-theoretic kernel, independent
of any Section Eight context. The second retains the original supplied action.
Source: Stellmacher, Journal of Algebra 190 (1997), printed p.40, (8.4).
The final graph adapter uses only the actual local context, and its original
canonical signature is retained through the graph-preserving local adapter.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem one_seven_sylow_fixed_card_le_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : SectionOne.Hypotheses G V) (sylow : Sylow 2 G)
    (hgen : SectionOne.oneE (V := V) (sylow : Subgroup G) ⊔
      (sylow : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup G) (⊤ : Subgroup G))
    (hfix : FixedPoints.subgroup
      (SectionOne.oneE (V := V) (sylow : Subgroup G)) V = ⊥) :
    Nat.card (FixedPoints.subgroup sylow V) ≤ 2 := by
  obtain ⟨factor, hfactor, hfactorGen⟩ :=
    SectionOne.oneSeven_exists_factor_sup_sylow_eq_top h sylow hgen hunique
  have hfactorData := (SectionOne.mem_oneSevenFactors_iff factor).mp hfactor
  obtain ⟨hnormal, hproduct, _⟩ := SectionOne.oneSeven_global_product h sylow
  have hcoordinates := SectionOne.sl2_product_sylow_coordinates sylow
    (SectionOne.oneSevenGenerated (G := G) (V := V)) hnormal
    (SectionOne.oneSevenFactors (G := G) (V := V)) hproduct
    (fun other hother => ((SectionOne.mem_oneSevenFactors_iff other).mp hother).1)
  let factorFixed := FixedPoints.subgroup factor V
  let sylowFixed := FixedPoints.subgroup sylow V
  let coordinateFixed := FixedPoints.subgroup (↥((sylow : Subgroup G) ⊓ factor)) V
  have hle : sylowFixed ≤ coordinateFixed :=
    fun _ hpoint actor => hpoint ⟨actor, actor.property.1⟩
  have htopFixed : FixedPoints.subgroup (⊤ : Subgroup G) V = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfix]
    exact fun _ hpoint actor => hpoint ⟨actor, trivial⟩
  have hintersection : factorFixed ⊓ sylowFixed = ⊥ := by
    apply SetLike.coe_injective
    change (MulAction.fixedPoints factor V ∩ MulAction.fixedPoints sylow V) =
      (⊥ : Subgroup V)
    rw [← fixedPoints_subgroup_sup, hfactorGen]
    exact congrArg SetLike.coe htopFixed
  have hindex : factorFixed.relIndex coordinateFixed = 2 :=
    SectionOne.oneSevenFactor_involution_fixed_relIndex h.action_faithful factor
      ((sylow : Subgroup G) ⊓ factor) hfactorData inf_le_right
      (hcoordinates.2.2.2 factor hfactor)
  have hcard : Nat.card sylowFixed = factorFixed.relIndex sylowFixed := by
    rw [← Subgroup.inf_relIndex_right, hintersection, Subgroup.relIndex_bot_left]
  rw [show Nat.card (FixedPoints.subgroup sylow V) = Nat.card sylowFixed from rfl,
    hcard, ← hindex]
  exact Subgroup.relIndex_le_of_le_right hle (by rw [hindex]; decide)

public theorem one_seven_small_rank_of_fixed_card_double
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : SectionOne.Hypotheses G V) (sylow : Sylow 2 G)
    (hJ : SectionOne.oneJ (V := V) (sylow : Subgroup G) ≠ ⊥)
    (hgen : SectionOne.oneE (V := V) (sylow : Subgroup G) ⊔
      (sylow : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup G) (⊤ : Subgroup G))
    (hfix : FixedPoints.subgroup
      (SectionOne.oneE (V := V) (sylow : Subgroup G)) V = ⊥)
    (hratio : Nat.card (FixedPoints.subgroup
      (SectionOne.oneJ (V := V) (sylow : Subgroup G)) V) =
      2 * Nat.card (FixedPoints.subgroup sylow V)) :
    Nat.card V = 16 ∧ (SectionOne.oneSevenFactors (G := G) (V := V)).card = 2 ∧
      Nat.card (FixedPoints.subgroup
        (SectionOne.oneJ (V := V) (sylow : Subgroup G)) V) = 4 := by
  let fixed := FixedPoints.subgroup
    (SectionOne.oneJ (V := V) (sylow : Subgroup G)) V
  have hproper : fixed ≠ ⊤ := by
    intro htop
    apply hJ
    apply bot_unique
    intro actor hactor
    rw [← h.action_faithful, mem_fixingSubgroup_iff]
    intro point _
    have hpoint : point ∈ fixed := htop ▸ Subgroup.mem_top point
    exact hpoint ⟨actor, hactor⟩
  have hless : Nat.card fixed < Nat.card V := by
    have hle := Subgroup.card_le_card_group fixed
    by_contra hnot
    exact hproper (Subgroup.eq_top_of_card_eq fixed (by omega))
  have hpositive : 0 < Nat.card fixed := Nat.card_pos
  obtain ⟨exponent, hcard⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hexponent : exponent ≠ 0 := by
    intro hzero
    simp only [hzero, pow_zero] at hcard
    omega
  have heven : Nat.card V % 2 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    rw [hcard]
    exact dvd_pow_self 2 hexponent
  have hparity := sylow.isPGroup'.card_modEq_card_fixedPoints V
  change Nat.card V % 2 = Nat.card (FixedPoints.subgroup sylow V) % 2 at hparity
  have hspositive : 0 < Nat.card (FixedPoints.subgroup sylow V) := Nat.card_pos
  have hslarge : 2 ≤ Nat.card (FixedPoints.subgroup sylow V) := by omega
  have hlarge : 4 < Nat.card V := by
    change Nat.card fixed = _ at hratio
    omega
  have hrank := SectionOne.oneSeven_card_sixteen_of_small_fixed_index h sylow hJ hgen
    hunique hfix hlarge (by omega)
  have hsbound := one_seven_sylow_fixed_card_le_two h sylow hgen hunique hfix
  exact ⟨hrank.1, hrank.2, by omega⟩

public theorem eight_four_small_rank_of_fixed_card_double_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let sylow := (S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    Nat.card (FixedPoints.subgroup
      (SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a) sylow)
      (ZAt ctx.Γ ctx.criticalPath.a)) =
        2 * Nat.card (FixedPoints.subgroup sylow (ZAt ctx.Γ ctx.criticalPath.a)) →
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 16 ∧
      (SectionOne.oneSevenFactors (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)).card = 2 ∧
        Nat.card (w.oneJFixedPoints S) = 4 := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let Sb := (S.subgroupOf P).map w.projection
  let E := SectionOne.oneE (V := Za) Sb
  change Nat.card (FixedPoints.subgroup (SectionOne.oneJ (V := Za) Sb) Za) =
    2 * Nat.card (FixedPoints.subgroup Sb Za) →
    Nat.card Za = 16 ∧ (SectionOne.oneSevenFactors (G := w.X) (V := Za)).card = 2 ∧
      Nat.card (w.oneJFixedPoints S) = 4
  intro hratio
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hlocal := (local_quotient_sylow_action_setup h Γ cp w).1
  obtain ⟨hSP, sylow, hsylow⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hnative : (sylow : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hsylow
  let imageSylow := sylow.mapSurjective w.surjective
  have himage : (imageSylow : Subgroup w.X) = Sb := by
    change (sylow : Subgroup P).map w.projection = _
    rw [hnative]
  have hres := lemma_eight_one_residual_join_local ctx w
  have hEaP : EAt Γ cp.a ≤ P := by
    rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
    exact Subgroup.map_subtype_le _
  have hEres : ((EAt Γ cp.a).subgroupOf P).map w.projection ≤ E := by
    rw [show E = _ from hres]
    exact le_sup_left
  have hgen : E ⊔ Sb = ⊤ := by
    have hRS : (EAt Γ cp.a).subgroupOf P ⊔ S.subgroupOf P = ⊤ := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEaP,
        Subgroup.map_subgroupOf_eq_of_le hSP, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
      exact SectionThree.twoResidual_sup_sylowImage ⟨sylow, hsylow⟩
    have hmap := congrArg (Subgroup.map w.projection) hRS
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ w.surjective] at hmap
    exact top_unique (hmap.ge.trans (sup_le_sup_right hEres Sb))
  have hfix : FixedPoints.subgroup E Za = ⊥ := by
    apply le_bot_iff.mp
    intro point hpoint
    have hfixed : point ∈ FixedPoints.subgroup
        (((EAt Γ cp.a).subgroupOf P).map w.projection) Za :=
      fun actor => hpoint ⟨actor, hEres actor.property⟩
    have hmap := Subgroup.mem_map_of_mem Za.subtype hfixed
    have hzero : Za ⊓ Subgroup.centralizer (EAt Γ cp.a : Set H) = ⊥ :=
      eight_four_initial_residual_center_trivial_local ctx hcenter
    rw [w.fixedPoints_map_subtype (EAt Γ cp.a) hEaP, hzero] at hmap
    exact Subtype.ext hmap
  have hcoatom : IsCoatom Sb := eight_four_faithful_sylow_isCoatom_local ctx w
  have hunique : IsUniqueMaximalContaining Sb (⊤ : Subgroup w.X) := by
    apply (uniqueMaximalContaining_top_iff Sb).mpr
    refine ⟨Sb, hcoatom, le_rfl, ?_⟩
    intro maximal hmaximal hle
    exact (hcoatom.le_iff_eq hmaximal.ne_top).mp hle
  have hdata : Nat.card Za = 16 ∧
      (SectionOne.oneSevenFactors (G := w.X) (V := Za)).card = 2 ∧
      Nat.card (FixedPoints.subgroup (SectionOne.oneJ (V := Za) Sb) Za) = 4 := by
    rw [← himage]
    apply one_seven_small_rank_of_fixed_card_double hlocal imageSylow
    · rw [himage]
      exact (eight_five_offender_local ctx w).2
    · rw [himage]
      exact hgen
    · rw [himage]
      exact hunique
    · rw [himage]
      exact hfix
    · change Nat.card (FixedPoints.subgroup
        (SectionOne.oneJ (V := Za) (imageSylow : Subgroup w.X)) Za) =
          2 * Nat.card (FixedPoints.subgroup (imageSylow : Subgroup w.X) Za)
      rw [himage]
      exact hratio
  refine ⟨hdata.1, hdata.2.1, ?_⟩
  change Nat.card ((FixedPoints.subgroup (SectionOne.oneJ (V := Za) Sb) Za).map
    Za.subtype) = 4
  rw [Subgroup.card_map_of_injective Za.subtype_injective]
  exact hdata.2.2


public theorem eight_four_small_rank_of_fixed_card_double
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let sylow := (S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    Nat.card (FixedPoints.subgroup
      (SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a) sylow)
      (ZAt ctx.Γ ctx.criticalPath.a)) =
        2 * Nat.card (FixedPoints.subgroup sylow (ZAt ctx.Γ ctx.criticalPath.a)) →
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 16 ∧
      (SectionOne.oneSevenFactors (G := w.X) (V := ZAt ctx.Γ ctx.criticalPath.a)).card = 2 ∧
        Nat.card (w.oneJFixedPoints S) = 4 := by
  exact eight_four_small_rank_of_fixed_card_double_local ctx.toLocalContext hcenter w

end Stellmacher.SectionEight
