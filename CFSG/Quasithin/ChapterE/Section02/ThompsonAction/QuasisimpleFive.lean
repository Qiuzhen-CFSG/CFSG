module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleBaumann
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleFiveMarker
public import Theory.Representation.BinaryOffender.AlternatingFiveQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.A5Source
/-!
# The genuine single symmetric-five source gives the index-two Sylow extension

The original B.5.1 moved central quotient carries the marked natural A5
module. Its literal subgroup quotient map extends to a faithful action of
the whole centralizer quotient, hence to S5 by the natural normalizer theorem.
The proper alternating subgroup forces surjectivity. Reduction and Thompson
movement transfer to the original moved subgroup, so the proved C.1.24 source
theorem gives the actual index-two Sylow extension in the required conjugate
span. The final theorem dispatches both genuine quasisimple natural rows.

Source: Aschbacher–Smith E.2.3(3), C.1.24 and3.1.7, pp.217,129 and575–576.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem quasisimple_five_source_marker
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    let W := ⁅U,pResidual 2 G⁆
    ∃ p : G →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
      ∃ hk : p.ker = centralizer (W:Set G),
      ∃ f : Additive W →ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
      Function.Surjective f ∧
      (∀ g v, f (NormalElementaryQuotient.representation W p hp hk g v) =
        BinaryPermutation.coreRepresentation (Fin 5) g (f v)) ∧
      f.ker = fixedSpace (NormalElementaryQuotient.representation W p hp hk)
        ((pResidual 2 G).map p) :=
  ChapterB.quasisimple_five_source_marker T hP U hU hJ q hq hker hqs s e

theorem quasisimple_five_source_conclusions
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    ∃ S₁ : Subgroup G,
      IsSylowSubgroupIn S₁ (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      baumann (T : Subgroup G) ≤ S₁ ∧
      ((baumann (T : Subgroup G)).subgroupOf S₁).index = 2 ∧
      S₁ ≤ conjugateSpanBy (baumann (T : Subgroup G))
        (pResidual 2 G ⊓ minimalParabolicMax T hP) := by
  obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := quasisimple_five_source_marker T hP U hU hJ q hq hker hqs s e
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer ((⁅U,pResidual 2 G⁆ : Subgroup G) : Set G) :=
    fun h => hJ (h.trans_eq (hU.centralizer_moved_eq U))
  exact (ChapterC.SymmetricFive.source_natural_quotient_conclusions T hP _ (hU.moved U)
    p hp hk f hf he hJW hfk).2.2.2

theorem quasisimple_source_sylow_or_extension
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∨
    ∃ S₁ : Subgroup G,
      IsSylowSubgroupIn S₁ (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      baumann (T : Subgroup G) ≤ S₁ ∧
      ((baumann (T : Subgroup G)).subgroupOf S₁).index = 2 ∧
      S₁ ≤ conjugateSpanBy (baumann (T : Subgroup G))
        (pResidual 2 G ⊓ minimalParabolicMax T hP) := by
  rcases quasisimple_baumann_or_symmetric_five T hP U hU hJ q hq hker hqs c with hs | he
  · exact Or.inl hs.1
  · obtain ⟨e⟩ := he
    exact Or.inr (quasisimple_five_source_conclusions T hP U hU hJ q hq hker hqs c.sectionData e)

end CFSG.Quasithin.ChapterE.ThompsonAction
