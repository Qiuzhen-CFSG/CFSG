module
public import CFSG.Quasithin.Chapter10.SourceA5LayerElementComponent
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.TwoQuotient
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.ReducedClosure
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The two original layer cases in the A₅ overcomponent

Restrict the prescribed centralizer Sylow to the actual containing
C-component I. It still normalizes the original embedded L. If U(L) lies
in O₂(I), its normal closure W lies in and centralizes O₂(I), belongs to
R₂(I), and is the direct product of U(L) and C_W(L). If U(L) survives,
the original image of L in I/O₂(I) remains a natural A₅ block.

All block and Sylow data are obtained from the original FundamentalSetup
and the actual element-centralizer component. This proves the structural
case split used on printed p.743 of Aschbacher–Smith 10.2.1; the two
remaining containing-component classification arguments are separate.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original Sylow intersection normalizes the same embedded block in I. -/
theorem source_containing_component_sylow {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X) :
    ∃ S : Sylow 2 I,
      (S:Subgroup I).map I.subtype = ((T:Subgroup G)⊓normalizer (L:Set G))⊓I ∧
      (S:Subgroup I) ≤ normalizer (L.subgroupOf I : Set I) := by
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hIX hI.subnormal
  refine ⟨S,hS,?_⟩
  rw [←subgroupOf_normalizer_eq hLI]
  intro s hs
  have hh := hS ▸ mem_map_of_mem I.subtype hs
  exact hh.1.2

/-- The original overcomponent has the contained reduced-layer structure or a surviving natural A₅ block. -/
theorem source_a5_overcomponent_layer_alternative
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X) :
    let K := L.subgroupOf I
    let U := (blockU K).map K.subtype
    let W := normalClosure (U : Set I)
    let q := QuotientGroup.mk' (pCore 2 I)
    (U ≤ pCore 2 I ∧ W ≤ pCore 2 I ∧ W ≤ centralizer (pCore 2 I : Set I) ∧
      IsPReduced 2 W ∧ W = U ⊔ (W ⊓ centralizer (K:Set I)) ∧
      U ⊓ (W ⊓ centralizer (K:Set I)) = ⊥) ∨
      IsAlternatingBlock (K.map q) 5 := by
  let K := L.subgroupOf I
  let U := (blockU K).map K.subtype
  let q := QuotientGroup.mk' (pCore 2 I)
  let f := q.subgroupMap K
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
  by_cases hU : U ≤ pCore 2 I
  · have hs := hK.normalClosure_layer_split K S hSK hU
    exact Or.inl ⟨hU,hs.1,hs.2.1,hK.normalClosure_layer_reduced K S hSK hU,
      hs.2.2.2.1,hs.2.2.2.2⟩
  · apply Or.inr
    have hp : IsPGroup 2 f.ker := by
      have he : f.ker = (pCore 2 I).subgroupOf K := by
        rw [ker_subgroupMap,QuotientGroup.ker_mk']
      rw [he]
      exact pCore_isPGroup.comap_subtype
    have hnot : ¬ blockU K ≤ f.ker := by
      intro hk
      apply hU
      rintro x ⟨k,hkU,rfl⟩
      have hh : q (k:I)=1 := congrArg Subtype.val (hk hkU)
      exact (QuotientGroup.eq_one_iff (k:I)).mp hh
    have hc := ((hK.layer_le_ker_or_ker_central f hp).resolve_left hnot).2
    exact hK.of_surjective_central_two_kernel f (q.subgroupMap_surjective K) hp hc

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
