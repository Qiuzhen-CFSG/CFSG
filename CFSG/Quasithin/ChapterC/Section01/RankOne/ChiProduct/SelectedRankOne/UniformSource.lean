module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.OriginalSection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.UniformPair
/-!
# The complete normal-SL₂ C.1.26 source branch

The full uniform C.1.18 theorem supplies the pair on the original Baumann
subgroup. Applying its alternatives to the proved selected local class gives
the actual outside χ-block and its original Thompson movement and support.
The only representation data are the genuine B.6.9 moved-section coordinates
on the original action; no characteristic-pair or block premise remains.

Source: Aschbacher–Smith C.1.26–28, printed pp.132–133.
-/
public section
universe u v
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G : Type u} {H : Type v} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem quasisimple_linear_outside_moved_chi_source
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
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2)
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G)
    (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤) :
    ¬ pResidual 2 G ≤ M ∧ IsChiBlockIn (pResidual 2 G) ∧
      pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype = ⁅U,pResidual 2 G⁆ := by
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  obtain ⟨P,hD⟩ := exists_baumann_universal_pair.{u,u} (T : Subgroup G) T.isPGroup' hTne
  exact quasisimple_linear_outside_moved_chi_of_section T hP U hU hJ q hq hker
    hqs s F hnatural hspan hfit P hD M hcpu hM
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
