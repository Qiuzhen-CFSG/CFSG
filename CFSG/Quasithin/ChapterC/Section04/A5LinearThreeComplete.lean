module
public import CFSG.Quasithin.ChapterC.Section04.A5LinearThreeNormality
public import CFSG.Quasithin.ChapterC.Section04.A5FiveFreeAction

/-!
# The constrained linear-three row over every binary field

The larger fields use the actual nontrivial radical intersection and its
five-rank obstruction. Over the field of two elements, the central quotient
has order 168, contradicting the five-divisibility forced by the original
A₅ span action. Thus both cases give the original local normality conclusion.

Source: Aschbacher–Smith C.4.8, printed pp.153–154, in the A₅ covering
configuration of 4.2.12–13, pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem normalizes_a5_of_constrained_star_linear_three
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (F : BinaryField)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(3,F.Carrier)) :
    M ≤ normalizer (L : Set G) := by
  by_cases hF : 1 < F.degree
  · exact h.normalizes_a5_of_constrained_star_linear_three_large a K hK hq hout hfK F hF e
  · have hd : F.degree = 1 := by have hp := F.degree_pos; omega
    apply (h.no_a5_component_of_central_fiveFree a K hK hq hout ?_).elim
    rw [Nat.card_congr (h.constrained_linear_three_simple_equiv K hK hq hout hfK e).toEquiv,
      Matrix.PSL3.LinearThree.card_projective F.Carrier, F.card_eq, hd]
    norm_num
end CFSG.Quasithin.ChapterC.HypothesisC28

