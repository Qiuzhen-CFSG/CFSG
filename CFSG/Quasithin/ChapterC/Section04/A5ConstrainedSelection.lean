module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Normality
public import CFSG.Quasithin.ChapterC.Section04.A5ComponentSelection
public import CFSG.Quasithin.ChapterC.Section04.A5FiniteNormality

/-!
# The constrained remainder of original A₅ component normality

The contained-Fitting and complete ordinary-component arguments leave an
escaping constrained C-component. Its literal star model is supplied by
C.2.7. The original pair-action argument removes the large symplectic row;
the cubic-center and finite-rank argument removes A₆–A₈, the triple cover
of A₆, SL₅(2), and G₂(2)′. Thus only the displayed rank-one, degree-three,
large G₂, and A₅ star markings remain.

This preserves the original C.2.8 subgroups and every quotient map. It is
the source input for the remaining constrained normalizer geometry and
its original Chapter 10 covering-counterexample consumer.
Source: Aschbacher–Smith C.2.7, C.3.1 and C.4.5–8, pp.145–154.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- Original nonnormality forces one of the four remaining constrained star models. -/
theorem nonnormal_a5_constrained_remainder
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hstrict : M < H) (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (hn : ¬ M ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧ generalizedFitting K = pCore 2 K ∧
      ((∃ F : BinaryField, Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) ∨
       (∃ F : BinaryField, Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃*
          Matrix.SpecialLinearGroup (Fin 3) F.Carrier)) ∨
       (∃ F : BinaryField, 1 < F.degree ∧ Nonempty
          (starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F.Carrier)) ∨
       Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃*
          alternatingGroup (Fin 5))) := by
  obtain ⟨K,hK,hq,hout,hcases⟩ := h.nonnormal_a5_component_remainder hstrict a hn
  rcases hcases with hc | ⟨hf,hm,hs⟩
  · exact (hn (h.normalizes_a5_of_ordinary_component a K hc)).elim
  refine ⟨K,hK,hq,hout,hf,?_⟩
  cases hm with
  | linearTwo F e => exact Or.inl ⟨F,⟨e⟩⟩
  | linearThree F e => exact Or.inr (Or.inl ⟨F,⟨e⟩⟩)
  | symplectic F hF e => exact (hs F hF ⟨e⟩).elim
  | g2 F hF e => exact Or.inr (Or.inr (Or.inl ⟨F,hF,⟨e⟩⟩))
  | g2DerivedTwo e =>
    exact (hn (h.normalizes_a5_of_constrained_star_g2_derived_two a K hK hq hout hf e)).elim
  | alternating n hd e =>
    rcases hd with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr ⟨e⟩))
    · exact (hn (h.normalizes_a5_of_constrained_star_alternating
        a K hK hq hout hf (by decide) (by decide) e)).elim
    · exact (hn (h.normalizes_a5_of_constrained_star_alternating
        a K hK hq hout hf (by decide) (by decide) e)).elim
    · exact (hn (h.normalizes_a5_of_constrained_star_alternating
        a K hK hq hout hf (by decide) (by decide) e)).elim
  | linearFiveTwo e =>
    exact (hn (h.normalizes_a5_of_constrained_star_linear_five_two a K hK hq hout hf e)).elim
  | tripleSix _ e =>
    exact (hn (h.normalizes_a5_of_constrained_star_triple_six a K hK hq hout hf e)).elim

end CFSG.Quasithin.ChapterC.HypothesisC28
