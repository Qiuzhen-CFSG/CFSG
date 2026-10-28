module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.CentralCover
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ChiefActionUnique
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureActor
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.MarkedOdd

/-!
# The actual faithful chief action of the original A₅ overcomponent

A quasisimple head maps centrally onto the literal actor I/C_I(W); a
centerless head identifies both quotients. Independently, once that actor
is quasisimple, the actual fixed quotient W/C_W(I) satisfies the source
rank-one hypotheses. The original involution still moves at most two
binary dimensions, since displacement cannot increase under quotient.
The original involution-centralizer supplies SQTK via the semisimple
section theorem. This is the exact action consumed by the marked B.4
exclusions, retaining the original D, e, hn and hout throughout.

Source: Aschbacher–Smith, 10.2.1, p.743, with B.4.5 and K.2.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_overcomponent_quasisimple_head_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I)
    (hhead : IsQuasisimple (I ⧸ pCore 2 I)) :
    let K := L.subgroupOf I
    let W := normalClosure ((blockU K).map K.subtype : Set I)
    let C := centralizer (W : Set I)
    IsQuasisimple (I ⧸ C) ∧
      ∃ f : (I ⧸ pCore 2 I) →* (I ⧸ C), Function.Surjective f ∧
        (∀ i, f (QuotientGroup.mk' (pCore 2 I) i) = QuotientGroup.mk' C i) ∧
        f.ker ≤ center (I ⧸ pCore 2 I) ∧
        Nonempty (((I ⧸ pCore 2 I) ⧸ center (I ⧸ pCore 2 I)) ≃*
          ((I ⧸ C) ⧸ center (I ⧸ C))) := by
  let K := L.subgroupOf I
  let W := normalClosure ((blockU K).map K.subtype : Set I)
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
  have hs := hK.normalClosure_layer_split K S hSK hU
  let := hhead
  exact hK.quasisimple_layer_actor K W le_normalClosure hs.2.2.2.1 hs.2.1

theorem source_a5_overcomponent_centerless_head_equiv
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I)
    (hhead : IsQuasisimple (I ⧸ pCore 2 I))
    (hz : center (I ⧸ pCore 2 I) = ⊥) :
    let W := normalClosure ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype : Set I)
    centralizer (W:Set I) = pCore 2 I ∧
    ∃ a : (I ⧸ pCore 2 I) ≃* (I ⧸ centralizer (W:Set I)),
      ∀ i, a (QuotientGroup.mk' (pCore 2 I) i) =
        QuotientGroup.mk' (centralizer (W:Set I)) i := by
  let W := normalClosure ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype : Set I)
  obtain ⟨_,f,hf,hfmk,hker,_⟩ := source_a5_overcomponent_quasisimple_head_action
    D e hn hout hLI hIX hI hS hU hhead
  have hfi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
    (bot_unique (hker.trans hz.le))
  refine ⟨?_,MulEquiv.ofBijective f ⟨hfi,hf⟩,hfmk⟩
  ext i
  constructor
  · intro hi
    apply (QuotientGroup.eq_one_iff (N := pCore 2 I) i).mp
    apply hfi
    change f (QuotientGroup.mk' (pCore 2 I) i) = f 1
    rw [hfmk,map_one]
    exact (QuotientGroup.eq_one_iff (N := centralizer (W:Set I)) i).mpr hi
  · intro hi
    apply (QuotientGroup.eq_one_iff (N := centralizer (W:Set I)) i).mp
    change QuotientGroup.mk' (centralizer (W:Set I)) i = 1
    rw [←hfmk]
    change f (i : I ⧸ pCore 2 I) = 1
    rw [(QuotientGroup.eq_one_iff (N := pCore 2 I) i).mpr hi,map_one]

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
theorem source_a5_overcomponent_quasisimple_unique_chief
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I)
    (hhead : IsQuasisimple (I ⧸ pCore 2 I)) :
    let K := L.subgroupOf I
    let W := normalClosure ((blockU K).map K.subtype : Set I)
    let q := QuotientGroup.mk' (centralizer (W:Set I))
    IsQuasisimple (I ⧸ centralizer (W:Set I)) ∧
    ∃ he : IsElementaryAbelian 2 W, letI := he
      let ρ := NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      ∃ t, HasUniqueCentralChief ρ ∧ HasMarkedChiefSection ρ t := by
  exact ⟨(source_a5_overcomponent_quasisimple_head_action
      D e hn hout hLI hIX hI hS hU hhead).1,
    source_a5_overcomponent_contained_layer_unique_chief D e hn hout hLI hIX hI hS hU⟩

theorem source_a5_involution_overcomponent_chief_action_of_actor_quasisimple
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {v : G} (hv : orderOf v = 2) {I : Subgroup G} (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v}:Set G))
    (hI : (I.subgroupOf (centralizer ({v}:Set G))).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G))
      (centralizer ({v}:Set G)))
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I)
    (hquasi : IsQuasisimple (I ⧸ centralizer
      (normalClosure ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype : Set I) : Set I))) :
    let K := L.subgroupOf I
    let W := normalClosure ((blockU K).map K.subtype : Set I)
    let A := I ⧸ centralizer (W:Set I)
    let q := QuotientGroup.mk' (centralizer (W:Set I))
    ∃ he : IsElementaryAbelian 2 W, letI := he
      let ρ := NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      let σ := fixedQuotient ρ ⊤
      ∃ t : A, ChapterK.RankOne.SourceHypotheses σ (generalizedFitting A) ∧
        orderOf t = 2 ∧
        Module.finrank (ZMod 2) (LinearMap.range (σ t -
          (LinearMap.id : (Additive W ⧸ (fixedSubrepresentation ρ ⊤).toSubmodule) →ₗ[ZMod 2]
            (Additive W ⧸ (fixedSubrepresentation ρ ⊤).toSubmodule)))) ≤ 2 ∧
        quadraticRatio σ ≤ 2 := by
  let K := L.subgroupOf I
  let W := normalClosure ((blockU K).map K.subtype : Set I)
  let A := I ⧸ centralizer (W:Set I)
  let q := QuotientGroup.mk' (centralizer (W:Set I))
  let : IsQuasisimple A := hquasi
  obtain ⟨he,_,t,_,ht,hr,_⟩ := source_a5_overcomponent_contained_layer_small_involution
    D e hn hout hLI hIX hI hS hU
  let := he
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let σ := fixedQuotient ρ ⊤
  obtain ⟨he',_,hchief,_⟩ := source_a5_overcomponent_contained_layer_unique_chief
    D e hn hout hLI hIX hI hS hU
  have hfaith : Function.Injective σ := hchief.2.2.1
  have hirr : IsIrreducible σ := hchief.2.1
  have hrq : Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) ≤ 2 := by
    have hh := fixedCodim_quotient_add_subrepresentation_le ρ
      (fixedSubrepresentation ρ ⊤) (zpowers t)
    simp only [fixedCodim_zpowers_eq_displacement_rank] at hh
    change Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2 at hr
    change Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) + _ ≤
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) at hh
    exact (Nat.le_add_right _ _).trans (hh.trans hr)
  have hratio : quadraticRatio σ ≤ 2 := by
    obtain ⟨hA,hAr,hquad,_⟩ := involution_actor_rank_and_fixedCodim σ t ht
    apply (quadraticRatio_le_two_iff σ).mpr
    refine ⟨zpowers t,hA,hquad,?_⟩
    rw [hAr,Nat.mul_one,fixedCodim_zpowers_eq_displacement_rank]
    exact hrq
  have hsqI : IsSQTK KnownSimple.IsKnownSimple I :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hIX)).mp
      ((D.simpleQTKE.involution_centralizer_sqtk hv).subgroup _)
  have hsec : ChapterA.Section02.IsSectionOf A I :=
    ChapterA.Section02.IsSectionOf.of_surjective q (QuotientGroup.mk'_surjective _)
  have hsem : ChapterA.Section02.IsSemisimple A := by
    apply top_unique
    exact le_sSup (show IsComponent A ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hsq : IsSQTK KnownSimple.IsKnownSimple A :=
    ⟨ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
      hsqI.stronglyQuasithin hsqI.isKGroup hsec hsem,hsec.isKGroup hsqI.isKGroup⟩
  have hirrF : IsIrreducible (σ.comp (generalizedFitting A).subtype) := by
    rw [generalizedFitting_eq_top_of_quasisimple]
    exact (irreducible_comp_surjective_iff (⊤ : Subgroup A).subtype
      topEquiv.surjective σ).mpr hirr
  exact ⟨he,t,⟨hsq,rfl,generalizedFitting_isQuasisimple_of_quasisimple,hfaith,hirrF,
    (cubicRatio_le_quadraticRatio σ).trans hratio⟩,ht,hrq,hratio⟩
end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
