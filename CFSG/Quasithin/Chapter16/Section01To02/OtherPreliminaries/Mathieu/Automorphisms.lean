module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.Mathieu.M12.Properties.SylowCentralizing
public import Theory.Mathieu.M24.Properties.OuterRestriction

/-!
# Completed Mathieu cases of Sylow-centralizing innerness

The concrete M₁₂ calculation applies to every pointwise Sylow-fixing
automorphism, and every automorphism of the concrete M₂₄ is inner. These
give the full arbitrary-two-element assertions of Aschbacher–Smith 16.1.6,
printed p.1172, for the two models. Neither result assumes an involution table.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
open Sporadic.Mathieu

/-- The M₁₂ case of 16.1.6, including the identity and all two-power orders. -/
theorem m12_sylow_centralizing_two_automorphisms :
    HasInnerSylowCentralizingTwoAutomorphisms M12 := by
  intro r _ S _ hS
  exact m12_automorphism_inner_of_fixes_sylow r S hS

/-- The M₂₄ case of 16.1.6, including the identity and all two-power orders. -/
theorem m24_sylow_centralizing_two_automorphisms :
    HasInnerSylowCentralizingTwoAutomorphisms M24 := by
  intro r _ _ _ _
  obtain ⟨g, hg⟩ := M24OuterRestriction.conj_surjective r
  exact ⟨g, hg.symm⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
