module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CommutingProductCenter

/-!
# A common exponent for component centers

Distinct components commute. When they generate the finite ambient group,
the canonical external product maps onto it. The common power identity on
the component centers consequently holds on the ambient center, including
when component centers have nontrivial intersections.

Source: Aschbacher–Smith A.2.12(I), printed p.36.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem center_pow_eq_one_of_component_centers
    (hG : componentLayer G = ⊤) (p : ℕ)
    (hp : ∀ C : Subgroup G, IsComponent G C →
      ∀ z : C, z ∈ center C → z ^ p = 1)
    (x : G) (hx : x ∈ center G) : x ^ p = 1 := by
  classical
  let I := { C : Subgroup G // IsComponent G C }
  let : Fintype I := Fintype.ofFinite I
  let H : I → Subgroup G := fun C => C.val
  have hc : Pairwise fun i j : I =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    have hn : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    exact ((commutator_eq_bot_iff_le_centralizer.mp
      (i.property.commutator_eq_bot_of_ne j.property hn)) hx y hy).symm
  have hgen : (⨆ i, H i) = ⊤ := by
    rw [← hG]
    apply le_antisymm
    · exact iSup_le (fun C => le_sSup C.property)
    · exact sSup_le (fun C hC => le_iSup_of_le (⟨C, hC⟩ : I) le_rfl)
  exact center_pow_eq_one_of_iSup_eq_top H hc hgen p
    (fun C => hp C.val C.property) x hx

end Theory.GroupTheory
