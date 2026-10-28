module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.Ratio
public import Theory.Representation.BinaryOffender.MarkedChiefDetection

/-!
# A marked chief section of the original contained A₅ layer closure

The reduced faithful action on the actual normal closure W has trivial
two-core. Its already constructed A₅ involution therefore survives on an
irreducible chief section. We retain that literal involution, its image,
and the displacement and quadratic-ratio bounds required by B.4.

This proves chief-section existence without assuming uniqueness or an
identification of the chief image with I/O₂(I). Those stronger source
steps remain separate.
Source: Aschbacher--Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original involution survives on a genuine chief section with the same bounds. -/
theorem source_a5_overcomponent_contained_layer_marked_chief_section
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I) :
    let K := L.subgroupOf I
    let W := normalClosure ((blockU K).map K.subtype : Set I)
    let q := QuotientGroup.mk' (centralizer (W:Set I))
    ∃ he : IsElementaryAbelian 2 W, letI := he
      let ρ := NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      IsPReduced 2 W ∧ ∃ t : I ⧸ centralizer (W:Set I),
        t ∈ K.map q ∧ orderOf t = 2 ∧
        Module.finrank (ZMod 2) (LinearMap.range
          (ρ t - (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W))) ≤ 2 ∧
        HasMarkedChiefSection ρ t := by
  obtain ⟨he,hred,t,htK,ht,hr,_hq⟩ :=
    source_a5_overcomponent_contained_layer_small_involution D e hn hout hLI hIX hI hS hU
  let := he
  refine ⟨he,hred,t,htK,ht,hr,?_⟩
  exact exists_marked_chief_section_of_twoCore_eq_bot _
    (NormalElementaryQuotient.representation_injective _ _ _ _)
    hred.quotient_pCore_eq_bot t ht hr

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
