module
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.PlaneNoncentralitySource

/-!
# Point commutator from the original local module clause

The invariant flag already supplies T-invariance of V, so the original
section-kernel theorem needs no universal structural premise. If the point
core centralizes the plane, U is a chosen module for the faithful residual K.
Apply original 13.3.2(3) at the same G,T,L. Its order sixteen conflicts with
the natural quotient of order sixteen and the nontrivial point kernel.

The earlier A₅ module theorem retains producer qt-d-1332-source; final
14.7.75 discharge belongs to qt-d-14775-source. The literal action, core
and point are unchanged. Source: AS 13.3.2(3), 13.3.14 and 14.5.21(2),
printed pp.885,891–893,1019.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Chapter12.Section08 Chapter13.Section03.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d

/-- Flag invariance discharges the literal section-kernel input. -/
theorem sectionCentralizer_from_flag : d.SectionCentralizer :=
  Chapter12.Section02.SourceAssembly.sectionCentralizer_of_sylow_invariance d
    (by simpa only [F.last] using F.invariant 3)

/-- Only the original ambient A₅ module clause is needed for plane movement. -/
theorem plane_noncentrality_of_original_modules_at
    (five : OriginalAlternatingFiveModules1332At T L) :
    ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G) := by
  intro hplane
  obtain ⟨chosen⟩ := d.U_chosen_of_plane_centralized d.sectionCentralizer_from_flag hplane
  have hmodel := five (Chapter14.Section03.FaithfulSource.hypothesis1331 d.counterexample)
    (K F) (d.K_faithful_of_plane_centralized hplane) ⟨d.K_quotient_equiv_A5⟩ F.U chosen
  have hcard := Chapter13.Section03.PlaneNoncentralitySource.alternatingFive_model_card hmodel
  have hsection := (d.KNaturalSection d.U_eq_commutator_K).card_section
  have hnatural : Nat.card SL2FourNatural.V = 16 := by
    rw [Nat.card_eq_fintype_card, SL2FourNatural.card_vector]
  rw [hnatural, hcard] at hsection
  have hpoint : 2 ≤ Nat.card d.U₀ := by
    have h := Nat.card_le_card_of_injective (Subgroup.inclusion d.point_le_U₀)
      (Subgroup.inclusion_injective d.point_le_U₀)
    rwa [show Nat.card (F.Vi 1) = 2 from by simpa using F.card 1 (by decide)] at h
  omega

/-- The point commutator needed by the fixed-component and endgame proofs. -/
theorem U_core_commutator_eq_point_of_original_modules_at
    (five : OriginalAlternatingFiveModules1332At T L) :
    ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1 :=
  d.U_core_commutator_eq_point_of_plane_moved d.sectionCentralizer_from_flag
    (d.plane_noncentrality_of_original_modules_at five)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
