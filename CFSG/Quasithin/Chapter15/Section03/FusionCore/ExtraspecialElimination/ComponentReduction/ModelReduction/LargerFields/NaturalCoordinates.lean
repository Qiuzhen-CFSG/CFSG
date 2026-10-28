module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Preparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Models
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Coordinates

/-!+# The natural component section in the larger-field case

The source setup and (k) identify the perfect offender span with L₀.
Its faithful offender-generated action satisfies all hypotheses of the
universal B.5.1 theorem. Once the rank reduction identifies L₀* with SL₂,
the complete B.5.1/B.4.2 alternatives select the natural central quotient.
The moved subspace is the literal image of [U_H,L₀] in U_H/Z, so the
coordinates are on exactly D/C_D(L₀*), not an unrelated irreducible section.

The final theorem changes the actor marking and the vector coordinates
together, placing Y₀* in the rank-one Borel under the same equivalence.
Its permitted geometric input is universal over actor markings. The
source assembly must supply the universal classification, rank reduction,
and Borel-placement results. No fixed-space containment, sum decomposition,
natural coordinates, or final contradiction is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1144; B.4.2 and B.5.1 on printed pp.86 and 99.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Representation.SL2CubicFixedSection
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates

universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : BorelInner.SourceSetup κ H M Y V Y0 L ZS Z A T)
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Natural coordinates on the literal component quotient, derived from
the offender and the full universal enumerated B.5.1 conclusion. -/
theorem exists_natural_componentSection
    (hB51 : QuasisimpleClassificationInput.{u,u} κ)
    (hY : Y0 ≤ localSpan L T)
    (e : starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hF : 2 < Nat.card F) :
    Nonempty (NaturalComponentSection (F := F) d.action.representation
      (starImage H (localSpan L T)) (componentSection Z H ZS L T)) := by
  obtain ⟨c⟩ := component_sourceConclusion d hB51 hY e hF
  obtain ⟨B, ⟨b⟩⟩ := select_movedSection _ e c.sectionData c.clause_one
  let f : B.Carrier ≃+* F :=
    fieldEquiv_of_sl2Equiv (b.groupEquiv.symm.trans (Subgroup.topEquiv.trans e))
  let a := transport_natural _ b f
  refine ⟨of_movedSection d.action.representation _ c.sectionData
    (componentSection Z H ZS L T) ?_ ?_ a⟩
  · exact componentSection_eq_moved Z H ZS L T d.action (d.replacement ▸ le_sup_left)
  · intro l v
    exact componentSection_invariant Z H ZS L Y0 T d.action d.replacement
      d.commutator_eq d.sylow_normalizes l v

/-- Select and mark the natural component section with Y₀* in the Borel.
The geometric input applies to every actor equivalence, so conjugating
the selected one also conjugates its vector coordinates compatibly. -/
theorem exists_natural_componentSection_borel
    (hB51 : QuasisimpleClassificationInput.{u,u} κ)
    (hY : Y0 ≤ localSpan L T)
    (e : starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hF : 2 < Nat.card F)
    (hB : ∀ e' : starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ y : starImage H Y0,
        g * e' ⟨y, (map_mono (comap_mono hY)) y.property⟩ * g⁻¹ ∈
          Matrix.SpecialLinearGroup.rankOneBorel F) :
    ∃ s : NaturalComponentSection (F := F) d.action.representation
        (starImage H (localSpan L T)) (componentSection Z H ZS L T),
      ∀ y : starImage H Y0,
        s.model ⟨y, (map_mono (comap_mono hY)) y.property⟩ ∈
          Matrix.SpecialLinearGroup.rankOneBorel F := by
  obtain ⟨s⟩ := exists_natural_componentSection d hB51 hY e hF
  exact exists_borel_marking (map_mono (comap_mono hY)) s hB

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
