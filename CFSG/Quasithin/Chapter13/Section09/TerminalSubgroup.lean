module

public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Basic
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Actions
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Sylow
public import Theory.SpecificGroups.Alternating.CommutingFourSixObstruction

/-!
# Terminal subgroup construction: transfer and the A₆ exclusion

These results keep H = O²(C_G(E)) literally inside G. The transfer result
removes E from H, and the A₆ exclusion uses the actual quasithin two-local
rank obstruction on O²(M₁) × H. The dihedral Sylow construction, involution
fusion, recognition and model automorphism restrictions are still needed
to construct the centralized PSL₃(2) consumed by TerminalObstruction.

Source: Aschbacher–Smith, proof of 13.9.1, printed pp.973–974.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup

open Subgroup

/-- Once the action restriction is established, the A₆ recognition branch
contradicts the actual quasithin hypothesis, without a separate rank premise. -/
theorem exclude_alternating_six {G : Type*} [Group G] [Finite G]
    (hG : IsQuasithin G) (E M₁ : Subgroup G)
    (e₁ : residual M₁ ≃* alternatingGroup (Fin 4))
    (hcomm : residual M₁ ≤ centralizer (terminal E : Set G))
    (eH : terminal E ≃* alternatingGroup (Fin 6)) : False :=
  Theory.Quasithin.not_quasithin_of_commuting_a4_a6 (residual M₁) (terminal E)
    e₁ eH hcomm hG

end CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup
