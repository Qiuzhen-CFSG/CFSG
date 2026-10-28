module

public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Outer automorphisms of perfect central covers

Descent to the central quotient detects inner automorphisms of a perfect
group. It therefore embeds the actual quotient Aut(G)/Inn(G) in the outer
group of any model isomorphic to G/Z(G). In particular commutativity passes
back to the cover. This justifies using simple-group outer calculations for
the quasisimple components on p.510 of Aschbacher–Smith (1 March 2004).
-/

public section
namespace MulAut
open Subgroup
open scoped IsMulCommutative
variable {G H : Type*} [Group G] [Group H]

/-- Descent takes inner automorphisms to inner automorphisms. -/
theorem inner_le_comap_centralQuotientAction (e : G ⧸ center G ≃* H) :
    innerSubgroup G ≤ (innerSubgroup H).comap (centralQuotientAction e) := by
  rintro a ⟨x, rfl⟩
  exact ⟨e (QuotientGroup.mk' (center G) x), (centralQuotientAction_conj e x).symm⟩

/-- Perfectness makes the preimage of the inner subgroup exactly the inner subgroup. -/
theorem comap_inner_centralQuotientAction [Group.IsPerfect G]
    (e : G ⧸ center G ≃* H) :
    (innerSubgroup H).comap (centralQuotientAction e) = innerSubgroup G := by
  apply le_antisymm _ (inner_le_comap_centralQuotientAction e)
  rintro a ⟨y, hy⟩
  obtain ⟨x, hx⟩ := (centralQuotientAction_inner_iff e a).mp ⟨y, hy.symm⟩
  exact ⟨x, hx.symm⟩

/-- The homomorphism on the actual outer quotients induced by central descent. -/
@[expose] def centralQuotientOuter (e : G ⧸ center G ≃* H) : Outer G →* Outer H :=
  QuotientGroup.map (innerSubgroup G) (innerSubgroup H) (centralQuotientAction e)
    (inner_le_comap_centralQuotientAction e)

/-- Innerness detection gives an embedding of outer automorphism groups. -/
theorem centralQuotientOuter_injective [Group.IsPerfect G]
    (e : G ⧸ center G ≃* H) : Function.Injective (centralQuotientOuter e) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.map _ _ _ _).ker = ⊥
  rw [QuotientGroup.ker_map, comap_inner_centralQuotientAction,
    QuotientGroup.map_mk'_self]

/-- Commutativity of the simple model's outer group passes to a perfect cover. -/
theorem outer_isMulCommutative_of_centralQuotient [Group.IsPerfect G]
    (e : G ⧸ center G ≃* H) [IsMulCommutative (Outer H)] :
    IsMulCommutative (Outer G) := by
  apply IsMulCommutative.of_comm
  intro x y
  apply centralQuotientOuter_injective e
  simp only [map_mul]
  exact mul_comm _ _

end MulAut
