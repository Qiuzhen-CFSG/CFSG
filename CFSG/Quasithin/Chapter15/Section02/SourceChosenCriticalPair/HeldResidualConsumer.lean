module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ActionAssembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Assembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.HeldUniqueness
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallRankOneSelection.Omega
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.HeldResidualAssembly

/-!
# Terminal Section 15.2 consumer with the retained Held residual

This is the literal final critical-pair consumer with partner-core containment
derived from an actual `ResidualInput`. The residual reduction's Held row is
discharged by the fixed-codimension proof; its three structural rows continue
through the existing assembly.

Source: Aschbacher--Smith, 15.2.27--28, printed pp.1119--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChapterE ChosenGeometry
open ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

/-- The terminal contradiction consumes the literal residual input directly,
including its Held possibility, and proves the partner-core premise itself. -/
theorem source_chosen_contradiction_of_action_models_and_residual_input
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
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (d : ResidualInput h H B)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) : False := by
  have hcore := source_chosen_partner_core_of_residual_input
    h hgeo d hMc hZ hquotient hres hplane
  exact source_chosen_contradiction_of_action_models_and_core h hgeo hu hMH
    hunique hi b hb hb2 hfixed hc hcases hcore

/-- The Held row has its own terminal consumer.  In particular, it does not
need the all-H-star centralization premise used by the structural row:
the fixed-codimension argument already gives the partner-core containment. -/
theorem source_chosen_contradiction_of_action_models_and_held_residual
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
    (hh : HeldResidualCase T H Mc) : False := by
  have hcore := source_chosen_partner_core_of_held h hgeo hMc hZ hquotient hres hh
  exact source_chosen_contradiction_of_action_models_and_core h hgeo hu hMH
    hunique hi b hb hb2 hfixed hc hcases hcore

/-- The Held terminal consumer after reconstructing the preceding action data
from the literal residual input.  This is the source-shaped adapter used by
the Section 15 assembly: the Held row needs the residual identity, but no
all-H-star centralization premise. -/
theorem source_chosen_contradiction_of_held_residual_input
    {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hh : HeldResidualCase T H Mc) : False := by
  let := h.prepared.elementary
  let hgeo : ChosenPlaneGeometry h H ⁅V, B⁆ := d.constructed_plane.geometry
  have hMH : M ⊓ H = (T : Subgroup G) := by
    simpa only [inf_comm] using (h.wreath_intersections d.outside d.quotient).1
  have hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (⁅V, B⁆ : Subgroup G)) = {Mc} := by
    exact d.plane_uniqueness_of_residual hquotient hres
  obtain ⟨Y,hw,_⟩ := h.smallResidualWitness_of_overgroups d.two_overgroups
  have hi : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
    exact d.constructed_plane.intersection.trans d.constructed_plane.centralizer_product
  have a := h.actionPreceding_of_residual d.outside d.quotient d.two_overgroups hres
  obtain ⟨B₀,hB₀,hcard,hm,_,hplanes⟩ := a.common_plane
  let : IsCyclic B₀ := isCyclic_of_prime_card hcard
  obtain ⟨b,hb⟩ := B₀.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hfixed : ∀ v : V, (v : G) ∈ ⁅V, B⁆ ↔ b.val v = v := by
    have hfix : ⁅V, B⁆ = ambientSpace V
        (fixedSpace (imageRepresentation M V h.prepared.normalized) B₀) :=
      (hplanes B d.offender).2.2.1.trans (hplanes B d.offender).2.2.2.1
    intro v
    rw [hfix, mem_ambientSpace, ← hb, mem_fixedSpace_zpowers_iff]
    rfl
  have hcases : (SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized) ∧
      SmallChosenActionModels (internalActionImage M V h.prepared.normalized)) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized) := by
    rcases h.small with hd | ho
    · rcases d.constructed_plane.models with hm' | ho'
      · refine Or.inl ⟨hd, ?_⟩
        rcases hm' with ⟨_,hs⟩ | ⟨_,hd' | hz⟩
        · exact Or.inl hs
        · exact Or.inr (Or.inl hd')
        · exact Or.inr (Or.inr hz)
      · exact Or.inr ho'
    · exact Or.inr ho
  exact source_chosen_contradiction_of_action_models_and_held_residual h hgeo hu hMH
    hw.residual_unique hi b (hB₀ (hb ▸ mem_zpowers b))
    (by rw [← Nat.card_zpowers, hb, hcard]) hfixed
    (by rw [hb]; exact hm.symm) hcases d.constructed_plane.partner_eq
    d.constructed_plane.seed_le hquotient hres hh

/-- Split a literal residual input at its intrinsic source reduction.  The
structural branch retains the existing residual-plane premise; the Held
branch is routed through the dedicated consumer above. -/
theorem source_chosen_contradiction_of_action_models_and_residual_or_held
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
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (d : ResidualInput h H B)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) : False := by
  rcases d.structural_or_held with hs | hh
  · have hcore := source_chosen_partner_core h hgeo hMc hZ hquotient hres hs hplane
    exact source_chosen_contradiction_of_action_models_and_core h hgeo hu hMH
      hunique hi b hb hb2 hfixed hc hcases hcore
  · exact source_chosen_contradiction_of_action_models_and_held_residual h hgeo hu hMH
      hunique hi b hb hb2 hfixed hc hcases hMc hZ hquotient hres hh

end CFSG.Quasithin.Chapter15.Section02
