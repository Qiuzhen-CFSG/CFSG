module
public import Theory.GroupTheory.PCoreNormalizerAction.Kernel
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.OuterComparison.Action

/-!
# Five-rank of the second-normalizer action kernel

The proved commutator containment puts the actual K₂ in the kernel on
J/O₂(J). At five-rank one, the center bound from A.3.6 and the ambient SQTK
rank inequality force that kernel to have five-rank exactly one. Relative
normality then realizes this as the kernel of the action of N_G(K₂).
The kernel of its outer action is the original J times this same kernel.

Relative normality supplies the actual C.2.7 input, so its public center-card
theorem supplies the coprime-center bound. In particular the action kernel
is not prime to five. These results do not infer outer action merely from K₁ not
being contained in J; that comparison remains with
qt-e-14615-quintic-exclusion, together with the geometry and row selection.

Source: Aschbacher--Smith 14.6.15, printed p.1035.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (J : Subgroup G) (hJN : J ≤ normalizer (d.K2 : Set G))
    (hJ : (J.subgroupOf (normalizer (d.K2 : Set G))).IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hout : ¬J ≤ Mc ⊓ normalizer (d.K2 : Set G))

include hJN hJ hq hout in
/-- The original second factor acts trivially on the intrinsic component quotient. -/
theorem second_factor_le_component_quotient_kernel :
    d.K2 ≤ pCoreActionKernelIn 2 J (normalizer (d.K2 : Set G)) := by
  have hKJ : d.K2 ≤ normalizer (J : Set G) :=
    (show d.K2 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_right).trans
      (closure_normalizes_component s d J hJN hJ hq)
  exact le_pCoreActionKernelIn_of_commutator 2 J _ d.K2 d.K2.le_normalizer hKJ
    (component_second_commutator s d J hJN hJ hq hout)

variable (hf : generalizedFitting J = pCore 2 J)

include hJN hJ hq hout hf in
/-- The actual kernel has exactly the complementary five-rank. -/
theorem component_quotient_kernel_five_rank (hr : primeRank 5 J = 1) :
    primeRank 5 (pCoreActionKernelIn 2 J (normalizer (d.K2 : Set G))) = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsQuasisimple (J ⧸ pCore 2 J) := hq
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  let := component_normal_of_quintic_rank_one s d J hJN hJ hq hout hr
  have hi : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) J :=
    ⟨hs,⟨hJN,hJ⟩,hq,hf,hout,
      hs.radical_le.trans (le_normalizer_of_normal_subgroupOf hJN)⟩
  have hz : Nat.Coprime 5 (Nat.card (center (J ⧸ pCore 2 J))) := by
    rcases ChapterC.C27Source.coreQuotient_center_card_from_source hi with hz | hz <;>
      rw [hz] <;> decide
  have hsum := pCoreActionKernelIn_rank_add_le J (normalizer (d.K2 : Set G))
    (by decide : Odd 5) hJN hz
  have hN := hs.sqtk.stronglyQuasithin 5 (by decide) (by decide)
  have hlower := (second_quintic_rank_pos s d).trans
    (primeRank_mono 5 (second_factor_le_component_quotient_kernel s d J hJN hJ hq hout))
  omega

include hJN hJ hq hout hf in
/-- Realize the kernel as that of the literal action of the whole second normalizer. -/
theorem component_rank_one_normalizer_action_kernel (hr : primeRank 5 J = 1) :
    ∃ hn : normalizer (d.K2 : Set G) ≤ normalizer (J : Set G),
      primeRank 5 (((pCoreNormalizerAction 2 J).comp (inclusion hn)).ker) = 1 ∧
      d.K2 ≤ (((pCoreNormalizerAction 2 J).comp (inclusion hn)).ker).map
        (normalizer (d.K2 : Set G)).subtype := by
  let := component_normal_of_quintic_rank_one s d J hJN hJ hq hout hr
  have hn := le_normalizer_of_normal_subgroupOf hJN
  have he := pCoreActionKernelIn_eq_map_ker 2 J (normalizer (d.K2 : Set G)) hn
  refine ⟨hn,?_,?_⟩
  · have h := component_quotient_kernel_five_rank s d J hJN hJ hq hout hf hr
    rw [he,←primeRank_congr 5
      (((pCoreNormalizerAction 2 J).comp (inclusion hn)).ker.equivMapOfInjective
        (normalizer (d.K2 : Set G)).subtype (normalizer (d.K2 : Set G)).subtype_injective)] at h
    exact h
  · exact he ▸ second_factor_le_component_quotient_kernel s d J hJN hJ hq hout

include hJN hJ hq hout hf in
/-- Identify the actual outer-action kernel, retaining the order-five kernel factor. -/
theorem component_rank_one_outer_action_kernel (hr : primeRank 5 J = 1) :
    ∃ hn : normalizer (d.K2 : Set G) ≤ normalizer (J : Set G),
      ((pCoreNormalizerOuterAction 2 J).comp (inclusion hn)).ker =
        J.subgroupOf (normalizer (d.K2 : Set G)) ⊔
          ((pCoreNormalizerAction 2 J).comp (inclusion hn)).ker ∧
      primeRank 5 (((pCoreNormalizerAction 2 J).comp (inclusion hn)).ker) = 1 ∧
      d.K2 ≤ (((pCoreNormalizerAction 2 J).comp (inclusion hn)).ker).map
        (normalizer (d.K2 : Set G)).subtype := by
  obtain ⟨hn,hrk,hK⟩ := component_rank_one_normalizer_action_kernel s d J hJN hJ hq hout hf hr
  exact ⟨hn,pCoreNormalizerOuterAction_restrict_ker 2 J _ hJN hn,hrk,hK⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
