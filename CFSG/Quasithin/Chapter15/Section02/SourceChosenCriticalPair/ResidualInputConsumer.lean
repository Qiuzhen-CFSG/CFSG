module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ActionAssembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ResidualInputAssembly

/-!
# Terminal critical-pair consumer from the complete residual input

This adapter supplies the partner two-core premise to the terminal
action-model contradiction.  The structural component rows use the existing
Held assembly, while the equality row uses the normal rank-two core lemma;
therefore no separate `partnerSpan = threePrimeResidual` premise is exposed.

Source: Aschbacher--Smith 15.2.27--28, printed pp.1119--1120.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChapterE ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The terminal contradiction after the residual split, with partner-core
containment derived from the literal `ResidualInput`. -/
theorem source_chosen_contradiction_of_action_models_and_complete_residual_input
    {T : Sylow 2 G} {M Mc V H ZS B : Subgroup G}
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
    (d : ResidualInput h H B)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) : False := by
  have hcore := source_chosen_partner_core_of_complete_residual_input
    h hgeo d hMc hZ hquotient hplane
  exact source_chosen_contradiction_of_action_models_and_core h hgeo hu hMH
    hunique hi b hb hb2 hfixed hc hcases hcore

end CFSG.Quasithin.Chapter15.Section02
