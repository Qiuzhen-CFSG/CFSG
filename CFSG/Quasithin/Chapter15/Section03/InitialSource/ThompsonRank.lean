module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.ThompsonAction
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.Rank

/-!
# One or two actual natural factors at the original 14.1.7 boundary

Quasithinness bounds the three-rank of the chosen maximal two-local M.
Apply the section-rank theorem to the actual localActionMap from M. The
already constructed concrete factor family has size one or two, while the
original stable offender family still selects its literal J(M) image.
Both natural supports and their equivariance data remain in the witness.

All local action, reducedness and rank premises are discharged from the
original source hypotheses. Universal Theorems A and C remain the genuine
earlier-source inputs. The fixed summand and final rank-two or orthogonal
recognition alternatives of 14.1.7 are subsequent source reductions.
Source: Aschbacher–Smith 14.1.7, printed p.977, and A.1.31(1), pp.27–28.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender

open Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Construct the original quotient factors and derive their count without a kernel restriction. -/
theorem local_thompson_factors_one_or_two_from_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    let hH : M ∈ Chapter1.HOver G (T : Set G) :=
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
    let U := (localModule T M).subgroupOf M
    letI := (localModule_reduced_from_source hG T hH).normal
    letI := (localModule_reduced_from_source hG T hH).elementary
    let q := localActionMap (centralInvolutions T) M
    let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (localActionKernel_eq_centralizer T hM.2))
    let P := ChapterB.maxOffenderImages (⊤ : Subgroup M) U q
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      (d.count = 1 ∨ d.count = 2) ∧
      Representation.BinaryOffender.IsStable (V := Additive U) ρ P ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q = generatedBy P ⊤ ∧
      (d.toSolvableFFFactors.stableFactorSet P).Nonempty ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q =
        ⨆ i ∈ d.toSolvableFFFactors.stableFactorSet P, d.factor i := by
  let hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  let := (localModule_reduced_from_source hG T hH).normal
  let := (localModule_reduced_from_source hG T hH).elementary
  obtain ⟨d, hd⟩ := local_thompson_factors_from_source hA hC hG T hempty hH hJ
  have hrank : primeRank 3 M ≤ 2 :=
    Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG.quasithin M hM.1.1 3 (by decide) (by decide)
  exact ⟨d, d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank
    (localActionMap (centralInvolutions T) M) (QuotientGroup.mk'_surjective _) hrank, hd⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource
