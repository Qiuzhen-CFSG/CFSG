module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.ReducedModule
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Actual natural factors at the initial 14.1.7 source boundary

The empty faithful-component family makes every reduced local action
solvable by the proved 14.1.3. B.2.7 and the full solvable B.1.8 theorem
therefore construct its marked factors, without assuming the local group
itself solvable. The original quotient map, stable offender family and
image of J(M) remain visible in the conclusion.

The final consumer takes the actual module and localActionMap of Section
15.3. Reducedness, faithfulness, quotient solvability and the FF hypothesis
are all derived. Its only earlier global premises are universal Theorems
A and C, besides the original QTKE, empty-family and J(T)-noncentrality
hypotheses. The factor-count and orthogonal identification needed for the
full alternatives of 14.1.7 remain subsequent source reductions.

Source: Aschbacher–Smith 14.1.3, 14.1.6(1), and the first step of 14.1.7,
printed pp.976–977, using B.2.7 and B.1.8 rather than imposing solvability
of M from the actual-solvable-group formulation of B.2.16.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original empty-family hypothesis constructs factors for every actual reduced module. -/
theorem reduced_thompson_factors_from_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : M ∈ Chapter1.HOver G (T : Set G))
    (U : Subgroup M) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (U : Set M)) :
    letI := hU.normal
    letI := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let P := ChapterB.maxOffenderImages (⊤ : Subgroup M) U q
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      Representation.BinaryOffender.IsStable (V := Additive U) ρ P ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q = generatedBy P ⊤ ∧
      (d.toSolvableFFFactors.stableFactorSet P).Nonempty ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q =
        ⨆ i ∈ d.toSolvableFFFactors.stableFactorSet P, d.factor i := by
  let := hU.normal
  let := hU.elementary
  exact ChapterB.thompson_factors_of_solvable_action U
    (QuotientGroup.mk' (centralizer (U : Set M))) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) (T.subtype hM.2) hJ
    (reduced_action_isSolvable hA hC hG T hempty hM U hU) hU.quotient_pCore_eq_bot


/-- Literal Section 15.3 module and quotient consumer, with all local action premises discharged. -/
theorem local_thompson_factors_from_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : M ∈ Chapter1.HOver G (T : Set G))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    let U := (localModule T M).subgroupOf M
    letI := (localModule_reduced_from_source hG T hM).normal
    letI := (localModule_reduced_from_source hG T hM).elementary
    let q := localActionMap (centralInvolutions T) M
    let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (localActionKernel_eq_centralizer T hM.2))
    let P := ChapterB.maxOffenderImages (⊤ : Subgroup M) U q
    ∃ d : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      Representation.BinaryOffender.IsStable (V := Additive U) ρ P ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q = generatedBy P ⊤ ∧
      (d.toSolvableFFFactors.stableFactorSet P).Nonempty ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup M)).map q =
        ⨆ i ∈ d.toSolvableFFFactors.stableFactorSet P, d.factor i := by
  have hTM : (T : Subgroup G) ≤ M := hM.2
  have hVM : localModule T M ≤ M := conjugateSpanBy_le_self
    (fun z hz => hTM ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  let U := (localModule T M).subgroupOf M
  let := (localModule_reduced_from_source hG T hM).normal
  let := (localModule_reduced_from_source hG T hM).elementary
  let S := T.subtype hTM
  have hJS : ¬ elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    intro h
    apply hJ
    have he : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
      simp only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]
    intro x hx v hv
    obtain ⟨a, ha, rfl⟩ := he.symm ▸ hx
    exact congrArg M.subtype (h ha ⟨v,hVM hv⟩ hv)
  exact ChapterB.thompson_factors_of_solvable_action U (localActionMap (centralInvolutions T) M)
    (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (localActionKernel_eq_centralizer T hTM)) S hJS
    (localActionQuotient_isSolvable hA hC hG T hempty hM)
    (localActionQuotient_twoReduced_from_source hG T hM)

end CFSG.Quasithin.Chapter15.Section03.InitialSource
