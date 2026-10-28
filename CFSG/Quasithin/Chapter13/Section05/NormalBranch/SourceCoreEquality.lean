module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotient
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.Original

/-!
# The original normal A₆ core and its centralizer

The original normal A₆ configuration supplies its own maximal faithful
local subgroup by the earlier source maximality argument. Applying the
exceptional-component quotient obstruction with that proved maximality
gives O₂(LT) = V. The characteristic-two centralizer bound then gives
C_G(V) ≤ V on the same original module.

These applications discharge the separate Hypothesis1221 premise of the
exceptional quotient consumer. The original natural setup, F.9 hypothesis,
normality of L₁ in H and nonabelian U_H remain exactly as in the normal
branch; this is not the assembly of the whole of Theorem 13.5.12.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.5.15(7), printed pp.920–921.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreEquality
open Section08.SourceCompletion

variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

include d h e hseed hn hU

/-- Original 13.5.15(7), with the earlier maximality premise discharged. -/
theorem original_core_eq_module : D.LT.pCoreIn 2 = D.V :=
  SourceExceptionalQuotient.original_core_eq_module d
    (Section03.SourceCompletion.SixMaximality.Original.original_hypothesis1221
      d h e hseed hn hU) h e hseed hn hU

/-- The actual module inherits the ambient core-centralizer bound. -/
theorem original_module_self_centralizing : centralizer (D.V : Set G) ≤ D.V := by
  have hc := SourceExceptionalQuotient.original_core_centralizer_le d
    (Section03.SourceCompletion.SixMaximality.Original.original_hypothesis1221
      d h e hseed hn hU)
  rwa [original_core_eq_module d h e hseed hn hU] at hc

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreEquality
