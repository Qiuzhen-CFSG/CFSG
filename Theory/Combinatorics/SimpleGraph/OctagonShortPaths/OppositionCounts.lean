module

public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.Opposition

/-!
# Exact nonopposite counts in an octagon of order (2,4)

The diagonal of the opposition square counts 1024 opposites at every point.
Subtracting its off-diagonal entries counts points opposite to one point but
not the other:512,384 and448 when their incidence distances are2,4 and6.
This proves the bound and equality characterization of Aschbacher–Smith J.5.12
by the already established distance-matrix identities.
-/

public section
namespace SimpleGraph.OctagonShortPaths.OrderTwoFourDatum
open SimpleGraph.OctagonOpposition
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (D : OrderTwoFourDatum G)
attribute [local instance] Classical.propDecidable
noncomputable section
local instance : DecidableEq D.Point := Classical.decEq _

theorem opposition_card (u : D.Point) :
    (Finset.univ.filter (fun w : D.Point=>D.pointDistance u w=4)).card=1024 := by
  have hh := (common_opposition D.pointDistance D.pointDistance_symm u u).symm.trans
    (square_value D.pointDistance D.pointDistance_zero D.recurrence u u)
  have hzero : D.pointDistance u u=0 := (D.pointDistance_zero u u).mpr rfl
  simp only [and_self,hzero] at hh
  norm_num at hh
  omega

theorem common_opposition_card (u v : D.Point) :
    (Finset.univ.filter (fun w : D.Point=>D.pointDistance u w=4 ∧D.pointDistance v w=4)).card =
      ![1024,512,640,576,608] (D.pointDistance u v) := by
  have hh := (common_opposition D.pointDistance D.pointDistance_symm u v).symm.trans
    (square_value D.pointDistance D.pointDistance_zero D.recurrence u v)
  generalize hk : D.pointDistance u v=k at hh ⊢
  fin_cases k <;> norm_num at hh ⊢ <;> omega

theorem nonopposite_opposition_card (u v : D.Point) :
    (Finset.univ.filter (fun w : D.Point=>D.pointDistance u w=4 ∧D.pointDistance v w≠4)).card =
      ![0,512,384,448,416] (D.pointDistance u v) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not
    (s:=Finset.univ.filter (fun w : D.Point=>D.pointDistance u w=4))
    (fun w=>D.pointDistance v w=4)
  rw [Finset.filter_filter,Finset.filter_filter,D.opposition_card,D.common_opposition_card] at hc
  generalize hk : D.pointDistance u v=k at hc ⊢
  fin_cases k <;> norm_num at hc ⊢ <;> omega

theorem source_lambda_bound (u v : D.Point)
    (hd : D.pointDistance u v=1 ∨D.pointDistance u v=2 ∨D.pointDistance u v=3) :
    (Finset.univ.filter (fun w : D.Point=>D.pointDistance u w=4 ∧D.pointDistance v w≠4)).card≤512 ∧
    ((Finset.univ.filter (fun w : D.Point=>D.pointDistance u w=4 ∧D.pointDistance v w≠4)).card=512 ↔
      D.pointDistance u v=1) := by
  rw [D.nonopposite_opposition_card]
  rcases hd with h|h|h <;> simp [h]

end
end SimpleGraph.OctagonShortPaths.OrderTwoFourDatum
