module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable

/-!
# The outer two-group of the concrete hexacode cover

Perfect central descent embeds the cover's outer automorphism group in
Out(A₆), whose actual order is four. This proves the odd-automorphism
restriction needed in the central-cover argument of A.3.18.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
A.3.18, printed pp.51–52; the concrete central quotient and the A₆ outer
order are the checked results in the imported modules.
-/

public section

open Subgroup
namespace Representation.Hexacode

theorem even_outer_two : IsPGroup 2 (MulAut.Outer Atlas.Codes.HexEvenAutomorphisms) := by
  let _ := even_isPerfect
  have htwo : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 6))) :=
    IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  exact htwo.of_injective (MulAut.centralQuotientOuter even_quotient_center_equiv)
    (MulAut.centralQuotientOuter_injective even_quotient_center_equiv)

end Representation.Hexacode
