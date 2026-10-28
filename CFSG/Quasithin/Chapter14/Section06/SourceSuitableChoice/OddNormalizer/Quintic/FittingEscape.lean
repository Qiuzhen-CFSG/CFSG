module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SecondNormalizer
public import CFSG.Quasithin.ChapterA.Section04.Intersection

/-!
# Generalized-Fitting escape in the second normalizer

If the quotient generalized-Fitting preimage of N_G(K₂) lay in its
intersection with Mc, A.4.4 would identify their two-cores. The module
geometry identifies the intersection core with O₂(Mc). Since a maximal
two-local is the full normalizer of its two-core, this would put all of
N_G(K₂) in Mc, contradicting the original critical-pair element.

This proves the full generalized-Fitting escape on printed p.1034. It
does not yet prove containment of the ordinary Fitting preimage, select
the escaping component, or perform the C.2.4/C.2.7 model comparison.
Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open Chapter1.RadicalExclusions ChapterA.Section04
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

private theorem fitting_escape_of_core_intersection (Mc N : Subgroup G)
    (hmax : IsMaximalTwoLocal Mc) (hcore : (Mc ⊓ N).pCoreIn 2 = Mc.pCoreIn 2)
    (hout : ¬ N ≤ Mc) : ¬ twoGeneralizedFittingPreimage N ≤ Mc ⊓ N := by
  intro hf
  have ha : IntersectionAlternative
      (twoCoreQuotientImage N (twoGeneralizedFittingPreimage N)) := by
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl,?_,?_⟩
    · exact (inferInstance :
        ((generalizedFitting (N ⧸ pCore 2 N)).subgroupOf
          (generalizedFitting (N ⧸ pCore 2 N))).Normal).isSubnormal
    · apply (closure_le _).mpr
      intro x hx
      exact hx.1.1
  have he := lemma_A_4_4_1 N Mc (twoGeneralizedFittingPreimage N)
    (twoCore_le_fittingPreimage N) (hf.trans (le_inf inf_le_right inf_le_left)) ha
  rw [inf_comm N Mc,hcore] at he
  apply hout
  have hn : N ≤ normalizer (N.pCoreIn 2 : Set G) := N.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  rwa [he,maximalTwoLocal_normalizer_core hmax] at hn

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (H1 H2 : Subgroup G)

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (c : CriticalPair
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH)
      a Mc H1)
    (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) c.endpoint.representative)

/-- The quotient generalized-Fitting preimage of the actual second
normalizer escapes the actual intersection with Mc. -/
theorem source_secondNormalizer_fitting_escape :
    ¬ twoGeneralizedFittingPreimage (normalizer (d.K2 : Set G)) ≤
      Mc ⊓ normalizer (d.K2 : Set G) := by
  have hs := source_secondNormalizer_setup hG T hempty hM hunique hmany hcard e
    hab H hH a H1 H2 c d
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  exact fitting_escape_of_core_intersection Mc _ hmax d.intersection_core hs.2.1

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
