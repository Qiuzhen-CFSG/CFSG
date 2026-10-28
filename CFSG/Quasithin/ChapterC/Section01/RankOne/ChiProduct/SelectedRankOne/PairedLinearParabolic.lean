module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.LocalLift
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearOriginal
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
/-!
# The paired linear branch of the original ambient C.1.28 source

Restrict to the actual escaping minimal parabolic and its original Sylow.
The same marked pair yields a genuine local chi-block. Its original
Thompson movement and canonical-module support enter the proved C.1.27
lifting theorem, producing an ambient outside moved chi-block.

Source: Aschbacher–Smith C.1.26–28, printed pp.132–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB SourceInduction QuasisimpleSource
universe u
variable {G : Type u} {D : Type u} [Group G] [Finite G] [Group D] [Finite D]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem ambient_outside_of_paired_linear
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
    (hs : ¬ Group.IsSolvable H)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : (T.subtype hTH).mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:D)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:D)).toMonoidHom = d.first)
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
  obtain ⟨K,hKo,hK,hKJ,hKU,hKUle⟩ := paired_linear_outside_of_control
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC) (hG.subgroup H)
    (T.subtype hTH) hP U q hq hker hs hfH d F c hexchange hspan
    (M.subgroupOf H) hcontrol hproper
  apply ambient_outside_of_local_moved_chi hA hC h4 hG T hf M H hTH hM K hK hKo hKJ
  rw [←hspan]
  exact hKUle
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
