module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.NaturalPrimeRemainder
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThreeParameter
/-!
# The complete natural larger-span selector for known-simple sections

The restricted embedding catalogue gives the binary alternatives or a
signed ternary model over an odd prime. The original SL₂(5) image and its
full Sylow normalizer force that prime to be five. The model is transported
through the actual quotient-to-image isomorphism. Thus C.5.12 retains its
original natural module and span hypotheses and needs no universal A.3.12
input or additional faithful-action premise.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem natural_full_span_selection_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n)
    (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (X : Subgroup G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hLK : conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K) :
    let D := conjugateSpanBy K X
    let r := QuotientGroup.mk' (pCore 2 X)
    (K.subgroupOf X).map r = (D.subgroupOf X).map r ∨ IsL2EvenBlock K 2 ∧
      ((IsAlternating ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 7 ∨
        IsAlternatingCover ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 7 ∨
        Nonempty (((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) ≃* Janko1.Model) ∨
        ClassicalGroup.IsPSL ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 2 25 ∨
        ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 2 p) ∨
      IsSL ((K.subgroupOf X).map r) 2 5 ∧
        ∃ u, IsPSLSign ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) u 3 5 ∨
          IsSLSign ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) u 3 5) := by
  rcases natural_full_span_selection_prime_remainder hG h hn h3 hT hTK X hAX hX S hS hVC hLK
      with he | ⟨hn2,hm⟩
  · exact .inl he
  rcases hm with hm | ⟨hb,p,hp,ho,u,hm⟩
  · exact .inr ⟨hn2,.inl hm⟩
  have hK : IsChiZeroBlock K := Or.inl ⟨n,hn⟩
  let D := conjugateSpanBy K X
  let r := QuotientGroup.mk' (pCore 2 X)
  let E := (D.subgroupOf X).map r
  have hD := source_larger_span_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let f := r.subgroupMap (D.subgroupOf X)
  have hk : f.ker = pCore 2 (D.subgroupOf X) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hD.subnormal).symm
  let eD := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (r.subgroupMap_surjective _))
  have hmE : IsPSLSign E u 3 p ∨ IsSLSign E u 3 p := by
    cases u with
    | false =>
        rcases hm with hm | hm
        · exact .inl (hm.of_mulEquiv eD.symm)
        · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
          exact .inr ⟨F,inferInstance,inferInstance,hF,⟨eD.symm.trans e⟩⟩
    | true =>
        rcases hm with hm | hm
        · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
          exact .inl ⟨F,inferInstance,inferInstance,J,hF,hc,⟨eD.symm.trans e⟩⟩
        · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
          exact .inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨eD.symm.trans e⟩⟩
  have he : p=5 := source_larger_odd_three_parameter hG K T X hK h3
    (h.module_le.trans inf_le_left) hT hTK hAX hX S hS hVC hp ho u hmE
  subst p
  exact .inr ⟨hn2,.inr ⟨hb,u,hm⟩⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
