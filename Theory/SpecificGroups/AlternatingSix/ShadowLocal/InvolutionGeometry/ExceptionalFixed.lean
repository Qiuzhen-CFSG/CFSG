module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.Alternating.proposition_5_2_7_8

/-!
# Fixed subgroups of exceptional involutions of A₆

An involution of the actual automorphism group of A₆ outside its natural S₆
subgroup fixes a dihedral group of order ten. The underlying proof conjugates
the involution to a canonical exceptional automorphism and constructs a
bijective homomorphism from D₁₀ to its fixed subgroup. Here that result is
exposed using the `ShadowLocal` carriers, together with its order consequence.

Source: GLS, Volume 3, Proposition 5.2.7(a). This is the exceptional-involution
input to the local A₆ geometry used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined 1 March 2004 manuscript, printed pp.567–570,
especially the fixed-subgroup containment argument on p.569.
-/

public section

open GLS3.Chapter5

namespace AlternatingSix.ShadowLocal

/-- An involution outside the natural S₆ has fixed subgroup D₁₀. -/
theorem outside_natural_involution_fixed_equiv_dihedral
    (β : AutA6) (hβ : orderOf β = 2) (hn : β ∉ natural) :
    Nonempty (automorphismFixedSubgroup β ≃* DihedralGroup 5) :=
  a6_outsideNatural_involution_fixed_equiv_dihedral β hβ hn

/-- The exceptional involution's fixed subgroup has order ten. -/
theorem outside_natural_involution_fixed_card
    (β : AutA6) (hβ : orderOf β = 2) (hn : β ∉ natural) :
    Nat.card (automorphismFixedSubgroup β) = 10 := by
  obtain ⟨e⟩ := outside_natural_involution_fixed_equiv_dihedral β hβ hn
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

end AlternatingSix.ShadowLocal
