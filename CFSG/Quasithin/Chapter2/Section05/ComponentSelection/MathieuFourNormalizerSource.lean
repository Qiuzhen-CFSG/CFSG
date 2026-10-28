module
public import Theory.Mathieu.M11.Properties.FourNormalizer

/-!
# The M₁₁ four-normalizer clause on the original component

For the literal M₁₁ alternative in 2.5.2(3), restrict the original four-group
F ≤ K to K and transport the proved model result through its actual group
identification. This supplies N_K(F) ≃ S₄ and C_K(F) = F for 2.5.8(5),
printed pp.556–557. The separate ambient automorphism containment and the
other model alternatives remain with the full small-model assembly.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup

/-- The intrinsic 2.5.8(5) conclusions in the literal M₁₁ component. -/
theorem mathieu_four_structure {G : Type*} [Group G]
    (K F : Subgroup G) (hFK : F ≤ K) [IsKleinFour F]
    (e : K ≃* Sporadic.Mathieu.M11) :
    centralizer (F.subgroupOf K : Set K) = F.subgroupOf K ∧
      Nonempty (normalizer (F.subgroupOf K : Set K) ≃* Equiv.Perm (Fin 4)) := by
  let f := subgroupOfEquivOfLe hFK
  let : IsKleinFour (F.subgroupOf K) :=
    { card_four := (Nat.card_congr f.toEquiv).trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv f).trans IsKleinFour.exponent_two }
  exact Sporadic.Mathieu.m11_four_structure_of_equiv e (F.subgroupOf K)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
