module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualCommonPlane
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualInputConsumer
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.HeldUniqueness

/-!
# The terminal contradiction from one residual plane

The common-plane theorem supplies every H-star centralizer and the actual
marked inverter. The complete residual-input theorem supplies partner-core
containment, including the equality row. Thus only plane uniqueness remains
beyond the original input and preceding global wreath quotients. A literal
residual identity for this one input discharges uniqueness; no identities
for the other H-star inputs are needed.

The two-overgroup and global wreath recognition premises retain their source
producers, and the equality-row residual identity remains open.
Source: Aschbacher--Smith, 15.2.13--15 and 15.2.27--28, pp.1111--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

/-- Plane uniqueness is the only remaining geometric premise beyond an actual
residual input and the preceding global wreath quotients. -/
theorem source_chosen_contradiction_of_residual_input_and_uniqueness
    {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath))
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (⁅V,B⁆ : Subgroup G)) = {Mc}) :
    False := by
  let := h.prepared.elementary
  obtain ⟨b⟩ := d.exists_planeInverter
  have c := d.constructed_plane
  have hMH : M ⊓ H = (T : Subgroup G) := by
    simpa only [inf_comm] using (h.wreath_intersections d.outside d.quotient).1
  obtain ⟨Y,hw,_⟩ := h.smallResidualWitness_of_overgroups d.two_overgroups
  have hcases : (SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized) ∧
      SmallChosenActionModels (internalActionImage M V h.prepared.normalized)) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized) := by
    rcases h.small with hd | ho
    · rcases c.models with hm | ho
      · refine Or.inl ⟨hd,?_⟩
        rcases hm with ⟨_,hs⟩ | ⟨_,hd | hz⟩
        · exact Or.inl hs
        · exact Or.inr (Or.inl hd)
        · exact Or.inr (Or.inr hz)
      · exact Or.inr ho
    · exact Or.inr ho
  exact source_chosen_contradiction_of_action_models_and_complete_residual_input
    h c.geometry hu hMH hw.residual_unique (c.intersection.trans c.centralizer_product)
    b.involution b.in_sylow b.order_two b.fixed_plane b.moves_odd_core hcases
    c.partner_eq c.seed_le hquotient d (d.all_residuals_centralize_plane hquotient)

/-- A residual identity for one actual input suffices for the source contradiction. -/
theorem source_chosen_contradiction_of_one_residual_identity
    {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (d : ResidualInput h H B)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath))
    (hres : partnerSpan H Mc = threePrimeResidual Mc) : False :=
  source_chosen_contradiction_of_residual_input_and_uniqueness h d hquotient
    (d.plane_uniqueness_of_residual hquotient hres)

end CFSG.Quasithin.Chapter15.Section02
