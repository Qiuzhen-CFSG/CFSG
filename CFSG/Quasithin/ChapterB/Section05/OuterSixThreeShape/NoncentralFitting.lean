module
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Components

/-!
# The cubic factor in the outer A₆ configuration is noncentral

The literal cubic factor is normal and lies in the Fitting subgroup. The
specified outer action on this abelian factor is nontrivial, so a central
Fitting subgroup is impossible. No order bound on the outer generator is
used. Source: Aschbacher–Smith B.5.6(4), printed p.105.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]
/-- The outer A₆–C₃ configuration has a noncentral normal cubic subgroup,
so it cannot occur when the Fitting subgroup is central. -/
theorem no_outerSixThree_of_fitting_le_center
    (hc : fittingSubgroup G ≤ center G) (c : OuterSixThreeShape G) : False := by
  let : c.second.Normal := c.second_normal
  have hp : IsPGroup 3 c.second := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    simp)
  have hf : c.second ≤ fittingSubgroup G :=
    (show c.second ≤ pCore 3 G from le_sSup ⟨inferInstance,hp⟩).trans (pCore_le_fitting G 3)
  obtain ⟨α,ha,ho⟩ := c.secondOuter
  have he : α = 1 := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [ha]
    have hh := mem_center_iff.mp (hc (hf a.property)) c.element
    change c.element * (a : G) * c.element⁻¹ = a
    rw [hh, mul_inv_cancel_right]
  apply ho
  rw [he]
  exact ⟨1,map_one _⟩

end CFSG.Quasithin.ChapterB.SourceInduction
