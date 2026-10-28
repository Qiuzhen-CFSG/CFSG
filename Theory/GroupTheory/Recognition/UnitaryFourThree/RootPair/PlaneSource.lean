module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneFusion
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.CoreIntersection

/-!
# Original-source elementary sixteen and its core eight

The original IsType hypothesis supplies a plane of order sixteen in the
involution centralizer, meeting the actual core in order eight. This is the
literal input to the independent quaternion-factor swap and cubic-line
Sylow-normalizer argument. No elementary subgroup witness is left assumed.
Source: Aschbacher, Sporadic Groups (1994), 45.3–45.6, pp.243–244.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}

theorem IsType.exists_plane_with_core_eight (h:IsType z) :
    ∃ V:Subgroup G, IsElementaryAbelian 2 V ∧ Nat.card V=16 ∧
      V≤centralizer z ∧ Nat.card (V⊓core z:Subgroup G)=8 ∧
      ∀ x∈V,∀y∈V,x≠1→y≠1→∃g∈normalizer (V:Set G),g*x*g⁻¹=y := by
  obtain ⟨P⟩:=h.exists_rootPair
  obtain ⟨d⟩:=P.exists_planePair h
  have hd : d.first≤P.T ∧ IsElementaryAbelian 2 d.first ∧ Nat.card d.first=16 :=
    ⟨d.first_le.trans le_sup_left,d.first_elementary,d.first_card⟩
  exact ⟨d.first,d.first_elementary,d.first_card,hd.1.trans P.T_le_centralizer,
    P.plane_inf_core_card h d.first hd,fun x hx y hy hxne hyne=>
      P.plane_nonidentity_transitive h d.first hd x y hx hy hxne hyne⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree
