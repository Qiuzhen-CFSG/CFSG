module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenInvolutions
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalTrack
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry

/-!
# Terminal assembly after the chosen involution and critical-track proofs

The marked earlier action alternatives give the Sylow involution, commutator,
and two-rank bounds. The actual opposite-track construction and its aligned
chief actions then produce both corank-one inequalities. This connects the
completed source branches to the normal-closure and E.3.6 contradiction.

Partner-core containment remains explicit. Its proof, including faithful
chief-action recognition and the moving parabolic, belongs to the same
critical-pair assembly owner; this theorem does not assert 15.2.27(2).
The other inputs are the exact preceding 15.2.8--15 source conclusions.

Source: Aschbacher--Smith, 15.2.25--28 and the terminal argument, pp.1118--1120.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The terminal contradiction with the original earlier-source markings and
partner-core containment as its sole remaining endgame input. -/
theorem source_chosen_contradiction_of_action_models_and_core
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
    (hcore : V ≤ twoCoreIn Mc) : False := by
  let := h.prepared.elementary
  obtain ⟨_,_,hTS,hcomm,hr⟩ := source_chosen_involution_actions h hgeo hu hi b hb hb2
    hfixed hc hcases
  have hpair := source_chosen_pair_of_source_track T h hgeo hMH hunique hr
  exact source_chosen_contradiction_of_core_and_pair T h hgeo hu
    h.module_parameters.1 h.module_parameters.2 hcore hTS hcomm hpair

end CFSG.Quasithin.Chapter15.Section02
