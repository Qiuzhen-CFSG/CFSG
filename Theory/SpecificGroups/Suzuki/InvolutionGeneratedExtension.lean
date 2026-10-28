module

public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.GroupTheory.GeneralizedFitting.InvolutionGenerated

/-!
# Involution-generated Suzuki extensions

The actual Suzuki outer automorphism group has odd order. Hence every
involution of a faithful extension belongs to the marked normal Suzuki
subgroup. If those involutions generate, the subgroup is the whole group.

Source: Aschbacher--Smith E.2.7, printed p.220, outer-extension inspection.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G]

/-- An involution-generated faithful extension of a nondegenerate Suzuki
group is the original normal Suzuki subgroup. -/
theorem suzuki_eq_top_of_involution_generated
    (L : Subgroup G) [L.Normal] (m : ℕ) (hm : 1 ≤ m)
    (e : L ≃* SuzukiMatrixGroup m) (hC : centralizer (L : Set G) = ⊥)
    (hgen : closure {g : G | g ^ 2 = 1} = ⊤) : L = ⊤ := by
  apply Theory.GroupTheory.normal_eq_top_of_odd_outer L hC hgen
  rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  exact suzuki_odd_outer_index m hm

end BenderSuzuki.MatrixGroups
