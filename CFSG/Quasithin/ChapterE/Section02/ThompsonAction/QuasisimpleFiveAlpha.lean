module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFive
/-!
# The original single symmetric-five alpha conclusion

The genuine B.5.1 moved marking constructs the same faithful whole S5
quotient as the checked C.1.24 application. Apply its sharp two-conjugate
Baumann argument on the literal W=[U,O²(H)], whose reducedness and
centralizer are inherited from U. This proves the moved-alpha identity;
no natural marking, image or fixed-codimension premise is added.
Source: Aschbacher–Smith B.6.10 and E.2.3(3), pp.117 and216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem quasisimple_five_source_alpha
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
    thompsonAlpha (T : Subgroup G) =
      ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
        centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := quasisimple_five_source_marker T hP U hU hJ q hq hker hqs s e
  let W := (⁅U,pResidual 2 G⁆ : Subgroup G)
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
    fun h => hJ (h.trans_eq (hU.centralizer_moved_eq U))
  have hfixed : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation W p hp hk g v = v := by
    intro v hv g hg
    have hh : v ∈ fixedSpace (NormalElementaryQuotient.representation W p hp hk)
        (alternatingGroup (Fin 5)) := by
      rw [← ChapterC.SymmetricFive.source_residual_image p hp,← hfk]
      exact hv
    exact hh ⟨g,hg⟩
  exact (ChapterC.SymmetricFive.source_alpha_and_saturation T hP W (hU.moved U)
    p hp hk f hf he hfixed hJW).2.1.trans (sup_comm _ _)
end CFSG.Quasithin.ChapterE.ThompsonAction
