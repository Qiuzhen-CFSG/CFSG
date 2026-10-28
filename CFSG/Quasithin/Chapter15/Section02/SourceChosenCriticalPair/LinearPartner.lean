module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ActionAssembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.LinearSource

/-!
# The terminal chosen-action contradiction in the linear partner branch

The faithful chief action of the actual partner quotient is recognized in
LinearSource, which constructs the moving parabolic and proves partner-core
containment. The completed involution and critical-track arguments then
discharge every terminal premise. The remaining hypotheses are the genuine
earlier-source geometry, uniqueness and marked action conclusions, together
with the linear structural alternative of 15.2.12(2).

The conjugate-component alternative remains with the same critical-pair
assembly owner; this module closes precisely the linear structural branch.
Source: Aschbacher--Smith 15.2.25--28, printed pp.1118--1120.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChapterE ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The linear partner branch of the original terminal argument, with core containment proved. -/
theorem source_chosen_contradiction_of_linear_partner
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hMH : M ⊓ H = (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hi : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G))
    (b : internalActionImage M V h.prepared.normalized)
    (hb : b ∈ (T.subtype h.maximal.1.2 : Subgroup M).map
      (actionHom M V h.prepared.normalized).rangeRestrict)
    (hb2 : orderOf b = 2)
    (hfixed : ∀ v : V, (v : G) ∈ ZS ↔ b.val v = v)
    (hc : ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),zpowers b⁆ =
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized))
    (hcases : letI := h.prepared.elementary
      (SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized) ∧
        SmallChosenActionModels (internalActionImage M V h.prepared.normalized)) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : ((partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) : False := by
  have hcore := source_chosen_partner_core_of_linear h hgeo hMc hZ hquotient hres hs hplane hn e
  exact source_chosen_contradiction_of_action_models_and_core h hgeo hu hMH hunique
    hi b hb hb2 hfixed hc hcases hcore

end CFSG.Quasithin.Chapter15.Section02
