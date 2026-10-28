module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Assembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.HeldUniqueness
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.Complete
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Uniqueness
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallRankOneSelection.Omega

/-!
# The chosen-action contradiction from the preceding residual clauses

The unique order-two image of the original offender supplies the inverter
and its fixed plane. The equal-seed row has immediate uniqueness; the
other row satisfies the exact hypotheses of 15.2.15. The same unique image
identifies the plane arising from every H-star residual. Consequently all
those residuals centralize the distinguished plane, and the completed
critical-pair argument gives the source contradiction.

The final theorem retains exactly the original ChosenSmallSource,
15.2.5 (the two maximal overgroups), 15.2.8 (the wreath quotients), and
15.2.12(2),(4) (the residual structural alternatives and identity).
The small-parabolic and residual-geometry owners supply these preceding
clauses; qt-e-152-chosen-action-contradiction retains their final discharge.
There is no supplied plane, inverter, uniqueness or critical-pair premise.
This conditional source application does not assert all of Section 15.2
or the unconditional Theorem E.

Source: Aschbacher--Smith, 15.2.9--28 and the terminal argument,
printed pp.1110--1120, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChosenGeometry ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- The unique order-two offender image supplies the actual marked inverter. -/
theorem ChosenGeometry.DistinguishedPlane.exists_planeInverter
    (d : DistinguishedPlane h H ZS) :
    Nonempty (PlaneUniquenessPreceding.OmegaAction.PlaneInverter h ZS) := by
  let := h.prepared.elementary
  obtain ⟨B,hB,hcard,hm,_,_,hfix,_⟩ := d.common_image
  let : IsCyclic B := isCyclic_of_prime_card hcard
  obtain ⟨b,hb⟩ := B.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  refine ⟨⟨b,?_,?_,?_,?_⟩⟩
  · exact hB (hb ▸ mem_zpowers b)
  · rw [←Nat.card_zpowers,hb,hcard]
  · rw [hb]; exact hm.symm
  · intro v
    rw [hfix,mem_ambientSpace,←hb,mem_fixedSpace_zpowers_iff]
    rfl

/-- Apply original 15.2.15 to the constructed plane in both source rows. -/
theorem ChosenGeometry.DistinguishedPlane.source_uniqueness
    (d : DistinguishedPlane h H ZS)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath)) :
    maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc} := by
  obtain ⟨B,hB,hZS⟩ := d.original
  have r := h.residualInput_of_preceding d.geometry.outside d.geometry.quotient htwo hB
  rw [hZS]
  exact r.plane_uniqueness_of_residual hquotient d.residual_eq

/-- The constructed plane and its literal residual centralizers feed the
completed critical-pair contradiction. -/
theorem source_chosen_contradiction_of_distinguished_plane
    (h : ChosenSmallSource T M Mc V) (d : DistinguishedPlane h H ZS)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath))
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) : False := by
  let := h.prepared.elementary
  obtain ⟨b⟩ := d.exists_planeInverter
  have hcases : (SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized) ∧
      SmallChosenActionModels (internalActionImage M V h.prepared.normalized)) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized) := by
    rcases h.small with hd | ho
    · rcases d.models with hm | ho
      · refine Or.inl ⟨hd,?_⟩
        rcases hm with ⟨_,hs⟩ | ⟨_,hd | hz⟩
        · exact Or.inl hs
        · exact Or.inr (Or.inl hd)
        · exact Or.inr (Or.inr hz)
      · exact Or.inr ho
    · exact Or.inr ho
  have hMH : M ⊓ H = (T : Subgroup G) := by
    simpa only [inf_comm] using (h.wreath_intersections d.geometry.outside d.geometry.quotient).1
  obtain ⟨Y,hw,_⟩ := h.smallResidualWitness_of_overgroups htwo
  exact source_chosen_contradiction_of_action_models h d.geometry
    (d.source_uniqueness htwo hquotient) hMH hw.residual_unique
    (d.intersection.trans d.centralizer_product) b.involution b.in_sylow b.order_two
    b.fixed_plane b.moves_odd_core hcases d.partner_eq d.seed_le hquotient
    d.residual_eq d.structural hplane

/-- Every original H-star residual centralizes the same distinguished plane.
The unique common image identifies the separately constructed offender planes. -/
theorem ChosenGeometry.DistinguishedPlane.all_residuals_centralize
    (d : DistinguishedPlane h H ZS)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath))
    (hresidual : ∀ J B, ResidualInput h J B →
      partnerSpan J Mc = threePrimeResidual Mc) :
    ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G) := by
  let := h.prepared.elementary
  obtain ⟨A,hA,hAc,hm,hunique,hZS,_⟩ := d.common_image
  intro J hJ
  obtain ⟨B,r⟩ := h.exists_residualInput_of_preceding h.action_alternatives hJ
    (hquotient J hJ) htwo
  have a := h.actionPreceding_of_residual hJ (hquotient J hJ) htwo (hresidual J B r)
  obtain ⟨A',hA',hAc',hm',_,hplanes⟩ := a.common_plane
  have he : A' = A := hunique A' hA' hAc' hm'
  have hp : ⁅V,B⁆ = ZS := by
    rw [(hplanes B r.offender).2.2.1,he,←hZS]
  exact hp ▸ r.residual_centralizes_plane

/-- The chosen-action contradiction from the exact remaining small-parabolic
and residual source clauses, with plane selection and uniqueness discharged. -/
theorem source_chosen_contradiction_of_preceding_residuals
    (h : ChosenSmallSource T M Mc V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath))
    (hresidual : ∀ J B, ResidualInput h J B →
      partnerSpan J Mc = threePrimeResidual Mc ∧ StructuralAlternatives T J Mc) : False := by
  obtain ⟨H,ZS,d⟩ := h.distinguished_plane_of_residuals htwo hquotient hresidual
  exact source_chosen_contradiction_of_distinguished_plane h d htwo hquotient
    (d.all_residuals_centralize htwo hquotient (fun J B r => (hresidual J B r).1))

end CFSG.Quasithin.Chapter15.Section02
