module

public import Theory.GroupTheory.CComponent.SixTheta
public import Theory.Alternating.OddCentralCovers

/-!
# The theta conclusion from the actual A₆ central quotient

The center of the two-core quotient has odd order. The alternating Schur
cover theorem therefore reduces its original A₆ central quotient to A₆
or the concrete triple cover, and the cubic generation theorem applies.
No choice of a covering model is required from the caller.

Source: Aschbacher--Smith, 12.2.8 and A.3.18, printed pp.51--52, 797.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.SixCComponentTheta
variable {H : Type*} [Group H] [Finite H]

private theorem quotient_center_odd (L : Type*) [Group L] [Finite L]
    [IsQuasisimple (L ⧸ pCore 2 L)] :
    Odd (Nat.card (center (L ⧸ pCore 2 L))) := by
  let Q := L ⧸ pCore 2 L
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ht : IsComponent Q ⊤ := ⟨IsSubnormal.top, inferInstance⟩
  have ho := GLS3.Chapter5.OddCentralCovers.component_center_odd
    (pCore_quotient_pCore_eq_bot (G := L) 2) ⊤ ht
  rwa [Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv] at ho

theorem cubic_closure_eq_of_central_quotient_six (L : Subgroup H) [L.Normal]
    (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6))
    (hrH : primeRank 3 H ≤ 2) : closure {x : H | orderOf x=3}=L := by
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) e
      (quotient_center_odd L) with hc | ⟨_,hc⟩
  · exact cubic_closure_eq_of_alternating_six L hL
      (GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6 e hc) hrH
  · obtain ⟨eH⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode e hc
    exact cubic_closure_eq_of_triple_six L hL eH hrH
end Theory.GroupTheory.SixCComponentTheta
