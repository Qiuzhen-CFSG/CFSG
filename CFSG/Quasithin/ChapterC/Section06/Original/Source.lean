module
public import CFSG.Quasithin.ChapterC.Section06.Original.Assembly
/-!
# C.6.1 directly from its original subgroup hypotheses

The literal source consumer supplies only (i)--(iv). The dispatcher
constructs the C.5 data and proves the structural conclusion. The simple
projections expose the universal normalizer, block-type and core-product
conclusions for consumers which do not need the entire alternative.
Source: Aschbacher--Smith C.6.1, printed pp.164--166.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section06.Original
variable {G : Type*} [Group G] [Finite G] {H Λ : Subgroup G}

theorem theorem_C_6_1
    (hf : generalizedFitting H = pCore 2 H) (hm : QuotientModels H)
    (hΛ : IsPGroup 2 Λ) (S : Sylow 2 H)
    (hS : (S : Subgroup H).map H.subtype = Λ ⊓ H) (hlt : Λ ⊓ H < Λ)
    (hc : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ Λ ⊓ H → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = Λ ⊓ H) : Conclusion H Λ :=
  (⟨hf,hm,hΛ,S,hS,hlt,hc⟩ : Input H Λ).conclusion

theorem Input.normalizer_index (d : Input H Λ) :
    (Λ ⊓ H).relIndex (Λ ⊓ normalizer (Λ ⊓ H : Set G)) = 2 := d.conclusion.1.1

theorem Input.core_product (d : Input H Λ) :
    H.pCoreIn 2 = ((pResidual 2 H).map H.subtype).pCoreIn 2 ⊔
      ((Λ ⊓ H) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G)) :=
  d.conclusion.1.2.2.1

theorem Input.residual_types (d : Input H Λ) :
    (∃ n, IsL2EvenBlock ((pResidual 2 H).map H.subtype) n) ∨
    IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5 ∨
    IsAlternatingBlock ((pResidual 2 H).map H.subtype) 3 ∨
    CubicPair ((pResidual 2 H).map H.subtype) := by
  rcases d.conclusion.2 with ⟨n,hn,_⟩ | ⟨h3,_⟩ | ⟨hβ,_⟩
  · exact Or.inl ⟨n,hn⟩
  · exact Or.inr (Or.inr (Or.inl h3))
  · rcases hβ with h5 | hp
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr (Or.inr hp))
end CFSG.Quasithin.ChapterC.Section06.Original
