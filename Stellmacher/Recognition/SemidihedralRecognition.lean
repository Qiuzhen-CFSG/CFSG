module

public import ABG.Recognition.ThreeLinearRecognition
public import ABG.Recognition.ThreeMathieuRecognition
public import ABG.Recognition.ThreeCharacterTheory
public import Stellmacher.Recognition.Catalogue
public import Stellmacher.Recognition.SemidihedralSylowSixteen

/-!
# Recognition from characteristic-three semidihedral local data

A finite simple group with a supplied semidihedral Sylow two-subgroup
of order sixteen and actual `GL₂(3)` involution centralizers is `PSL₃(3)`
or `M11`. Wong's character theorem gives orders 5616 and 7920. The projective-plane and sharply
four-transitive-action recognition theorems identify the actual groups in
these two cases, giving membership in the N₂ model catalogue.

For a simple N₂ group with a supplied semidihedral Sylow two-subgroup and
trivial odd cores in all two-local subgroups, the local centralizer theorem
provides these actual `GL₂(3)` models. Their two-parts give Sylow order sixteen,
so the final two theorems derive recognition from the original local hypotheses.

Sources: Alperin--Brauer--Gorenstein, III.8 Proposition 5, article p.117;
W. J. Wong, *On finite groups whose 2-Sylow subgroups have cyclic subgroups
of index 2* (1964), Theorem 6, pp.106–111, DOI 10.1017/S1446788700022771.
The argument uses the proved characteristic-three inputs, without the
classification statements in `ABG.FinalTheorem`.
-/

namespace Stellmacher.Recognition
universe u

/-- Wong recognition from a semidihedral Sylow subgroup of order sixteen
and actual `GL₂(3)` involution centralizers. -/
public theorem isPSL3_or_mathieu_of_semidihedral_gl2_three_centralizers
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ x : G, orderOf x = 2 →
      Nonempty (Subgroup.centralizer ({x} : Set G) ≃* ABG.GL2 3 1)) :
    ABG.IsPSL3 G 3 ∨ Nonempty (G ≃* Sporadic.Mathieu.M11) := by
  classical
  let e := fun x hx => Classical.choice (hC x hx)
  rcases ABG.threeCharacterTheory_order_alternatives S hS hcard e with hM | hL
  · exact Or.inr (ABG.nonempty_mulEquiv_M11_of_card_eq_7920 S hS hcard e hM)
  · exact Or.inl (ABG.isPSL3_of_card_eq_5616 S hS hcard e hL)

/-- The semidihedral alternative with actual `GL₂(3)` involution centralizers
belongs to the N₂ model catalogue. -/
public theorem isNTwoGroupModel_of_semidihedral_gl2_three_centralizers
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ x : G, orderOf x = 2 →
      Nonempty (Subgroup.centralizer ({x} : Set G) ≃* ABG.GL2 3 1)) :
    IsNTwoGroupModel G := by
  rcases isPSL3_or_mathieu_of_semidihedral_gl2_three_centralizers S hS hcard hC with hL | hM
  · exact Or.inl (.linearThree hL)
  · obtain ⟨e⟩ := hM
    exact Or.inl (.mathieuEleven e)

/-- A simple N₂ group with semidihedral Sylow two-subgroups and trivial
two-local odd cores is actually `PSL₃(3)` or `M11`. -/
public theorem isPSL3_or_mathieu_of_simple_nTwo_semidihedral
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥) :
    ABG.IsPSL3 G 3 ∨ Nonempty (G ≃* Sporadic.Mathieu.M11) := by
  have hC := involutionCentralizer_equiv_gl2_three_of_simple_nTwo S hS hN hcore
  exact isPSL3_or_mathieu_of_semidihedral_gl2_three_centralizers S hS
    (sylow_card_sixteen_of_gl2_three_centralizers S hS hC) hC

/-- The core-free-local semidihedral branch of the simple N₂ reduction belongs
to the N₂ model catalogue. -/
public theorem isNTwoGroupModel_of_simple_nTwo_semidihedral
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥) :
    IsNTwoGroupModel G := by
  rcases isPSL3_or_mathieu_of_simple_nTwo_semidihedral S hS hN hcore with hL | hM
  · exact Or.inl (.linearThree hL)
  · obtain ⟨e⟩ := hM
    exact Or.inl (.mathieuEleven e)

end Stellmacher.Recognition
