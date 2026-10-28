module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.Mathieu.M22.Properties.SylowPointwise.Innerness

/-!
# M₂₂ automorphisms centralizing a Sylow two-subgroup

The concrete degree-22 design calculation proves innerness for every
pointwise Sylow-fixing automorphism. Specializing it gives the M₂₂ case of
Aschbacher–Smith 16.1.6, printed p.1172, including the identity and all
orders dividing a power of two. This calculation is independent of the
involution-centralizer table in 16.1.5(5), printed p.1171.
-/

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
open Sporadic.Mathieu

/-- The M₂₂ case of 16.1.6 for arbitrary two-elements, including the identity. -/
public theorem m22_sylow_centralizing_two_automorphisms :
    HasInnerSylowCentralizingTwoAutomorphisms M22 := by
  intro r _ S _ hS
  exact M22SylowPointwise.automorphism_inner_of_fixes_sylow r S hS

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
