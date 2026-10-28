module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.LocalLift
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
/-!
# The normal-SL₂ branch of the ambient C.1.28 source

An escaping minimal parabolic inherits characteristic two and control from
the ambient group. Its actual B.6.9 quasisimple natural section gives a
local χ-block by the complete uniform-pair source. The literal local block,
Thompson subgroup and omega-center module then enter the proved C.1.27 lift.
The conclusion is the ambient outside moved χ-block required by C.1.28.

Source: Aschbacher–Smith C.1.26–28, printed pp.132–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB SourceInduction QuasisimpleSource
universe u v
variable {G : Type u} {D : Type v} [Group G] [Finite G] [Group D] [Finite D]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem ambient_outside_of_quasisimple_linear_section
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hf : generalizedFitting G = pCore 2 G)
    (M H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hout : ¬ H ≤ M)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set H))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2)
    (hspan : U = normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H)) :
    ∃ L : Subgroup G, ¬ L ≤ M ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hfH : generalizedFitting H = pCore 2 H :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (centralizer_pCore_le_of_pCore_le H
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
        ((pCore_isPGroup.le_sylow_of_normal T).trans hTH))
  have hcontrol : (T.subtype hTH : Subgroup H).characteristicNormalizerClosure ≤ M.subgroupOf H :=
    characteristicNormalizerClosure_subgroupOf_le hTH hM
  have hproper : M.subgroupOf H ≠ ⊤ := fun he => hout (subgroupOf_eq_top.mp he)
  obtain ⟨hKo,hK,hKJ,hKU⟩ := quasisimple_linear_outside_of_control
    (T.subtype hTH) hP U q hq hker hqs s F hnatural hspan hfH (M.subgroupOf H) hcontrol hproper
  apply ambient_outside_of_local_moved_chi hA hC h4 hG T hf M H hTH hM
    (pResidual 2 H) hK hKo hKJ
  rw [hKU,←hspan]
  exact commutator_le_left _ _
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
