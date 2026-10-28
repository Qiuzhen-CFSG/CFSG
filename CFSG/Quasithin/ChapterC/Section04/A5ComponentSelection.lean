module
public import CFSG.Quasithin.ChapterC.Section04.A5SymplecticNormality
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ContainedComponentPromotion

/-!
# Selecting the remaining component in a nonnormal A₅ configuration

The completed contained-Fitting branch contradicts original nonnormality,
so the genuine C.2.8 selection supplies an escaping C-component. It is
ordinary or constrained. In the constrained case the literal C.2.7 input
supplies its full star-model catalogue, and the symplectic row is excluded
by the original action-kernel rank argument.

This retains the selected subgroup and its actual star map for the remaining
C.3/C.4 model branches. It does not assume their unresolved local conclusions.
Source: Aschbacher–Smith C.2.13, C.3.1, C.4.1 and C.4.8, pp.148–154.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- Original nonnormality selects an escaping component outside the completed branches. -/
theorem nonnormal_a5_component_remainder
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hstrict : M < H) (eA : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ M ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧
      (IsComponent H K ∨
        (generalizedFitting K = pCore 2 K ∧
          C27Source.StarModels.Model (starImage (K.map H.subtype) R (K.map H.subtype)) ∧
          ∀ F : BinaryField, 1 < F.degree →
            ¬ Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* Sp F.Carrier))) := by
  have hf : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H :=
    fun hf => hn (h.normalizes_of_fitting_contained hstrict hf)
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := h.ordinary_or_constrained_escape hf
  refine ⟨K,hK,hq,hout,?_⟩
  rcases hcases with hc | hc
  · exact Or.inl hc
  · right
    refine ⟨hc,C27Source.star_model_from_source
      (h.constrained_source_input K hK hq hout hc),?_⟩
    rintro F hF ⟨e⟩
    apply hn (h.normalizes_of_a5_constrained_symplectic eA K hK hq hout hc e ?_)
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ F.degree)

end CFSG.Quasithin.ChapterC.HypothesisC28
