module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ParabolicSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Selection
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ReducedSolvability
/-!
# The solvable minimal-parabolic branch of C.1.28

The actual Sylow overgroup inherits characteristic two and proper
characteristic-normalizer control. Stellmacher's proved cubic-factor source
then constructs its escaping A₃ block, with the original Thompson marking
and canonical-module support. The C.1.27 lift supplies an ambient moved
χ-block. The same conclusion applies when solvability is known only on the
actual reduced action quotient.

Source: Aschbacher–Smith C.1.26–28, printed pp.132–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB SourceInduction QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]


theorem ambient_outside_of_solvable_parabolic
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hf : generalizedFitting G = pCore 2 G)
    (M H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hout : ¬ H ≤ M)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤) (hs : Group.IsSolvable H) :
    ∃ L : Subgroup G, ¬ L ≤ M ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let S := T.subtype hTH
  let N := M.subgroupOf H
  have hc := centralizer_pCore_le_of_pCore_le H
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
    ((pCore_isPGroup.le_sylow_of_normal T).trans hTH)
  have hcontrol : (S : Subgroup H).characteristicNormalizerClosure ≤ N :=
    characteristicNormalizerClosure_subgroupOf_le hTH hM
  have hproper : N < ⊤ := lt_top_iff_ne_top.mpr (fun he => hout (subgroupOf_eq_top.mp he))
  have hh := Solvable.sectionTwoHypotheses_of_proper_subgroup hs hc N hproper
  have hS : (S : Subgroup H) ≠ ⊥ := by
    intro he
    apply hP.2
    rw [show (T.subtype hTH : Subgroup H) = ⊥ from he]
    exact le_normalizer_of_normal
  have hSN : (S : Subgroup H) ≤ N := (S : Subgroup H).le_normalizer.trans
    ((normalizer_le_characteristicNormalizerClosure_self (S : Subgroup H) hS).trans hcontrol)
  have hchar : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup H).subtype).Normal := by
    intro K hK hne
    let : K.Characteristic := hK
    exact not_normal_of_characteristicNormalizerClosure_le (S : Subgroup H) N hproper hcontrol K hne
  have hu : IsUniqueMaximalContaining (S : Subgroup H) ⊤ := by
    obtain ⟨⟨A,hA,ha⟩,_⟩ := (isMinimalParabolicOver_top_iff S).mp hP
    exact (uniqueMaximalContaining_top_iff _).mpr ⟨A,hA.1,hA.2,fun B hB hSB => ha B ⟨hB,hSB⟩⟩
  obtain ⟨K,hKo,hK,hKa,hKJ,hKU⟩ := Solvable.exists_outside_alternatingThree_block hh S hchar hu N hSN hproper
  exact ambient_outside_of_local_moved_chi hA hC h4 hG T hf M H hTH hM K
    ⟨hK,Or.inr ⟨3,by decide,hKa⟩⟩ hKo hKJ hKU
variable {D : Type v} [Group D] [Finite D]

theorem ambient_outside_of_solvable_action
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
    (hspan : U = normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H))
    (hs : Group.IsSolvable D) :
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
  have hS : (T.subtype hTH : Subgroup H) ≠ ⊥ := by
    intro he
    apply hP.2
    rw [he]
    exact le_normalizer_of_normal
  have hU : IsPReduced 2 U := hspan ▸ omegaCenter_normalClosure_reduced (T.subtype hTH)
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfH)
  have hJ := thompson_moves_omega_closure_of_control (T.subtype hTH) hS U hspan
    (M.subgroupOf H) hcontrol hproper
  have hsol := solvable_of_reduced_minimalParabolic_action (T.subtype hTH) hP U hU hJ q hq hker hs
  exact ambient_outside_of_solvable_parabolic hA hC h4 hG T hf M H hTH hM hout hP hsol

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
