module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Opposition
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.OppositionCounts

/-!
# The original J.5.12 count on the binary Ree point cosets

For literal first-parabolic cosets u,v, Lambda consists of points opposite to u
and not opposite to v. The actual graph yields exact counts512,384,448 at
incidence distances2,4,6. Thus the source bound512 holds with equality exactly
at distance2, without a path-count or recurrence assumption.

Source: Aschbacher–Smith J.5.12, printed p.449.
-/

public noncomputable section
namespace ReeF4.Octagon.Binary
open Subgroup Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open SimpleGraph.OctagonShortPaths
local instance : Fintype (CosetGeometry.Vertex family) := Fintype.ofFinite _

/-- Points opposite to u and not opposite to v. -/
def lambdaSet (u v : PointCoset) : Set PointCoset :=
  {w | pointDistance u w=8 ∧ pointDistance v w≠8}

private theorem lambda_card_transfer (u v : PointCoset) :
    Nat.card (lambdaSet u v) =
      (Finset.univ.filter (fun w : orderTwoFour.Point =>
        orderTwoFour.pointDistance (cosetPointEquiv u) w=4 ∧
        orderTwoFour.pointDistance (cosetPointEquiv v) w≠4)).card := by
  classical
  let E : lambdaSet u v ≃
      {w : orderTwoFour.Point // orderTwoFour.pointDistance (cosetPointEquiv u) w=4 ∧
        orderTwoFour.pointDistance (cosetPointEquiv v) w≠4} :=
    cosetPointEquiv.subtypeEquiv (by
      intro w
      have he (q : PointCoset) : orderTwoFour.pointDistance (cosetPointEquiv q) (cosetPointEquiv w)=4 ↔
          pointDistance q w=8 := by
        rw [orderTwoFour.pointDistance_eq_iff,cosetPointEquiv_val,cosetPointEquiv_val]
        norm_num [pointDistance]
      change (pointDistance u w=8 ∧ pointDistance v w≠8) ↔ _
      exact and_congr (he u).symm (not_congr (he v)).symm)
  rw [Nat.card_congr E,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem lambda_card (u v : PointCoset) :
    Nat.card (lambdaSet u v) =
      ![0,512,384,448,416] (orderTwoFour.pointDistance (cosetPointEquiv u) (cosetPointEquiv v)) := by
  rw [lambda_card_transfer,orderTwoFour.nonopposite_opposition_card]

theorem source_J_5_12 (u v : PointCoset)
    (hd : pointDistance u v=2 ∨ pointDistance u v=4 ∨ pointDistance u v=6) :
    Nat.card (lambdaSet u v)≤512 ∧
      (Nat.card (lambdaSet u v)=512 ↔ pointDistance u v=2) := by
  have he (i : Fin 5) : orderTwoFour.pointDistance (cosetPointEquiv u) (cosetPointEquiv v)=i ↔
      pointDistance u v=2*(i:ℕ) := by
    rw [orderTwoFour.pointDistance_eq_iff,cosetPointEquiv_val,cosetPointEquiv_val]
    rfl
  have hd' : orderTwoFour.pointDistance (cosetPointEquiv u) (cosetPointEquiv v)=1 ∨
      orderTwoFour.pointDistance (cosetPointEquiv u) (cosetPointEquiv v)=2 ∨
      orderTwoFour.pointDistance (cosetPointEquiv u) (cosetPointEquiv v)=3 := by
    simpa [he] using hd
  rw [lambda_card_transfer]
  simpa [he] using orderTwoFour.source_lambda_bound (cosetPointEquiv u) (cosetPointEquiv v) hd'

end ReeF4.Octagon.Binary
