module
public import CFSG.Quasithin.Chapter10.SourceA5NumericalSelection
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalComplete

/-!
# Complete cubic bounds for the original A₅ modules

The completed qrc theorem applies to the original action of L₀T on V.
Its uniqueness premise is supplied by the fundamental setup. The literal
image-to-centralizer-quotient transfer then gives the local cubic bound.
The actual outside-maximal guard, or the multiple-overgroup premise that
supplies it, is retained throughout.

Source: Aschbacher--Smith 3.1.6--8 and 3.2.5--6, printed pp.573--581,
using the completed E.2.7--13 and B.5.13 source arguments.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original H* supplies the completed local cubic bound on the literal
centralizer quotient of the original module. -/
theorem source_localModule_cubic_bound_of_hstar {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    SourceLocalModuleCubicBound D :=
  source_localModule_cubic_bound_of_image D
    ((D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).source_cubicRatio_le_two
      D.simpleQTKE
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1
      (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2
      D.module_ne_bot)

/-- The local cubic bound with the genuine outside-maximal guard. -/
theorem source_local_module_cubic_bound
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    SourceLocalModuleCubicBound D := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  exact source_localModule_cubic_bound_of_hstar D hH

/-- The multiple-overgroup branch discharges the original local cubic input. -/
theorem source_local_module_cubic_bound_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    SourceLocalModuleCubicBound D :=
  source_local_module_cubic_bound D (source_maximalOutside_of_many D hmany)

end CFSG.Quasithin.Chapter10
