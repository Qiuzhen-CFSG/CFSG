module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenInvolutions
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry

/-!
# Applying the chosen-action bounds to the terminal contradiction

The source involution and commutator conclusions now supply the two inputs
previously retained by the core-and-critical-pair assembly. The action parameters
are obtained from the prepared module. The partner-core containment and existence
of the critical pair remain the independent source branches.

Source: Aschbacher--Smith, 15.2.25--28 and the final argument, pp.1118--1120.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The actual terminal consumer, with the involution bounds discharged. -/
theorem source_chosen_contradiction_of_action_models_core_and_pair
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
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
    (hcore : V ≤ twoCoreIn Mc)
    (hpair : ∃ g : G,
      subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≤ 1 ∧
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1 ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  let := h.prepared.elementary
  obtain ⟨_,_,hTS,hcomm,_⟩ := source_chosen_involution_actions h hgeo hu hi b hb hb2
    hfixed hc hcases
  exact source_chosen_contradiction_of_core_and_pair T h hgeo hu
    h.module_parameters.1 h.module_parameters.2 hcore hTS hcomm hpair

end CFSG.Quasithin.Chapter15.Section02
