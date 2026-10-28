module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry

/-!
# The terminal intersection from the actual seed quotient action

The natural-component calculation in 14.6.23 supplies the following
precise input: an element of Mc centralizing V/Z lies in T, with the
literal V=localModule T M and Z=centralInvolutions T. In particular
C_M(V) lies in T. The already proved intersection-core decomposition
M∩Mc = C_M(V)O₂(M∩Mc) then gives M∩Mc=T. The original S₃ action
factorization M=LTC_M(V) gives M=LT, including the literal set product.

`SeedQuotientCentralizerBound` is the remaining module-theoretic input,
owned by qt-e-terminal-natural-support-decomposition. It is not asserted
here. No component-classification or residual equality is needed for this
conditional group-theoretic deduction.

Source: Aschbacher--Smith 14.1.18(2), 14.3.7 and 14.6.23(2),
printed pp.979,992,1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
open SourcePreliminaries Chapter15.Section03 Chapter15.Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The exact centralizer assertion on the original V/Z, before choosing coordinates. -/
@[expose] def SeedQuotientCentralizerBound (T : Sylow 2 G) (M Mc : Subgroup G) : Prop :=
  ∀ x ∈ Mc, (∀ v ∈ localModule T M, ⁅v,x⁆ ∈ centralInvolutions T) → x ∈ (T : Subgroup G)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))

include hG hempty hM hunique hmany hcard e

/-- The actual terminal intersection and subgroup supplement. -/
theorem terminal_intersection_of_seed_quotient_centralizer
    (hc : SeedQuotientCentralizerBound T M Mc) :
    M ⊓ Mc = (T : Subgroup G) ∧ M = sourceResidual M Mc ⊔ (T : Subgroup G) := by
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hne,_,_⟩ := plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ
  obtain ⟨_,hnoncentral,_⟩ := plane_intersection_core_inputs hG T hempty hM.1
    hunique hmany hZ hne
  obtain ⟨_,hT,hI,_⟩ := source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
  have hC : M ⊓ centralizer (localModule T M : Set G) ≤ (T : Subgroup G) := by
    intro x hx
    apply hc x (localModule_centralizer_le_partner T M hunique hx.2)
    intro v hv
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 v hv)]
    exact (centralInvolutions T).one_mem
  have hi : M ⊓ Mc = (T : Subgroup G) := by
    apply le_antisymm
    · rw [hI]
      exact sup_le hC (hT ▸ le_sup_left)
    · exact le_inf hM.1.2 (terminal_outside hG T hempty hM hunique hmany hcard e).1.2
  refine ⟨hi,?_⟩
  have hf := decomposition_of_intersectionCore_not_centralizing M Mc (localModule T M)
    T hM.1.2 ⟨e⟩ hnoncentral
  exact hf.trans (sup_eq_left.mpr (hC.trans le_sup_right))


/-- Original M=LT as a set product, with normality only inside M. -/
theorem terminal_product_of_seed_quotient_centralizer
    (hc : SeedQuotientCentralizerBound T M Mc) :
    (M : Set G) = (sourceResidual M Mc : Set G) * ((T : Subgroup G) : Set G) ∧
      M ⊓ Mc = (T : Subgroup G) := by
  obtain ⟨hi,hm⟩ := terminal_intersection_of_seed_quotient_centralizer
    hG T hempty hM hunique hmany hcard e hc
  refine ⟨?_,hi⟩
  apply (congrArg (fun X : Subgroup G => (X : Set G)) hm).trans
  exact coe_mul_of_right_le_normalizer_left _ _ (hM.1.2.trans
    ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp (residualY_normal M Mc)))

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
