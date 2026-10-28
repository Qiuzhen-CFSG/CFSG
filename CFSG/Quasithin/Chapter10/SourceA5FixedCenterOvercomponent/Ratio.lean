module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.Recognition
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureRatio

/-!
# The original contained A₅ layer has small quadratic ratio

For the actual element-centralizer component I, restrict the prescribed
Sylow and take W to be the normal closure of the original U(L). When the
layer lies in O₂(I), its established split over C_W(L) gives a genuine
involution of displacement rank at most two in I/C_I(W), and hence q ≤ 2
for that literal faithful action. Reducedness of W is retained.

Source: Aschbacher–Smith 10.2.1, printed p.743. This discharges the
numerical B.4 input; A.3.14 recognition of the overcomponent remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original contained-layer branch has a reduced module and the concrete
involution and ratio required by the source B.4 recognition step. -/
theorem source_a5_overcomponent_contained_layer_small_involution
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
      IsPReduced 2 W ∧
      ∃ t : I ⧸ centralizer (W:Set I), t ∈ K.map q ∧ orderOf t = 2 ∧
        Module.finrank (ZMod 2) (LinearMap.range
          (NormalElementaryQuotient.representation W q
            (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) t -
              (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W))) ≤ 2 ∧
        quadraticRatio (NormalElementaryQuotient.representation W q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let K := L.subgroupOf I
  let W := normalClosure ((blockU K).map K.subtype : Set I)
  let q := QuotientGroup.mk' (centralizer (W:Set I))
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
  have hs := hK.normalClosure_layer_split K S hSK hU
  let he := hs.2.2.1
  let := he
  refine ⟨he,hK.normalClosure_layer_reduced K S hSK hU,?_⟩
  exact hK.layer_split_quotient_small_involution K W le_normalClosure hs.2.2.2.1 q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
