module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.LocalFamily
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.Residual
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The Sylow supplement in the fixed-plane centralizer

Relative normality makes S ∩ L Sylow in L. Since S centralizes Z_S,
this Sylow subgroup lies in C_L(Z_S), where it supplements the two-residual.
Dedekind decomposition then gives C_I(Z_S) = O²(C_L(Z_S))S.

The final theorem uses the already-proved restriction of the three-prime
residual and an explicit equality between the two residuals of C_L(Z_S).
That equality remains a geometric obligation; the definitions are distinct.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.3.32(4), printed p.1133.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The common Sylow intersection is Sylow in the component centralizer. -/
theorem fixedPlane_component_centralizer_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) :
    Chapter1.IsSylowIn 2 (d.S ⊓ c.L) (c.L ⊓ centralizer (d.ZS : Set G)) := by
  have hSL := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hS (component_le c) hnormal.isSubnormal
  exact hSL.restrict
    (le_inf inf_le_right (inf_le_left.trans (sylow_le_fixedPlane_centralizer d))) inf_le_left

/-- The two-residual of the component centralizer, together with S, is C_I(Z_S). -/
theorem twoResidual_fixedPlane_join_sylow (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hjoin : I = c.L ⊔ d.S) (hS : Chapter1.IsSylowIn 2 d.S I) :
    let K := c.L ⊓ centralizer (d.ZS : Set G)
    (pResidual 2 K).map K.subtype ⊔ d.S = I ⊓ centralizer (d.ZS : Set G) := by
  let K := c.L ⊓ centralizer (d.ZS : Set G)
  obtain ⟨P, hP⟩ := fixedPlane_component_centralizer_sylow d c hnormal hS
  have hgen := congrArg (fun H : Subgroup K => H.map K.subtype)
    (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup, hP, ← MonoidHom.range_eq_map, range_subtype] at hgen
  rw [fixedPlane_centralizer_decomposition d c hnormal hjoin]
  apply le_antisymm (sup_le_sup (map_subtype_le _) le_rfl)
  apply sup_le ?_ le_sup_right
  exact hgen.ge.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right))

/-- The source XS equality, conditional on the still separate residual comparison. -/
theorem residual_join_eq_fixedPlane_centralizer_of_residual_equality
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hnormal : (c.L.subgroupOf I).Normal) (hjoin : I = c.L ⊔ d.S)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (hL : c.L = RankOne.threeResidualIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (hres : let K := c.L ⊓ centralizer (d.ZS : Set G)
      RankOne.threeResidualIn K = (pResidual 2 K).map K.subtype) :
    RankOne.threeResidualIn (centralizer (d.ZS : Set G)) ⊔ d.S =
      I ⊓ centralizer (d.ZS : Set G) := by
  rw [threeResidual_fixedPlane_eq_component_intersection d hL, hres]
  exact twoResidual_fixedPlane_join_sylow d c hnormal hjoin hS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end
