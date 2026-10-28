module
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree
/-!
# The A₆ cubic degree source from the native binary catalogue

The actual component action is faithful and irreducible. The proved actor
generation bound gives degree at most twelve, and the order-five obstruction
gives degree at least four. The unconditional A₆ spectrum 1, 4, 16 therefore
forces four on the original module. No FF-module hypothesis, artificial
six-dimensional bound, or flag-filtration callback is retained.

This discharges the exact Six.Degree input used in the B.4.5 chief-action
branch. Source: Aschbacher–Smith G.5.1, pp.342–343, and K.1, p.452.
-/

public section
open Representation Subgroup
namespace CFSG.Quasithin.ChapterK.Alternating
universe u v

theorem sixDegree_native_source : RecognitionInputs.Six.Degree.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h e
  let τ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hd := BinaryAlternatingSix.alternating_degrees τ
  have hlo := four_le_finrank_of_six_component ρ h e
  have hhi := SixDegreeReduction.finrank_le_twelve ρ h e
  omega
end CFSG.Quasithin.ChapterK.Alternating
