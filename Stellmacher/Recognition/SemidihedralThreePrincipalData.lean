module

public import ABG.ChapterIII.Section2.ThreePrincipalData
public import Theory.PGroupCore

/-!
# Supplied semidihedral characteristic-three principal characters

This data interface retains the actual principal-block characters and the
geometric order identity with the odd-core intersection parameter. Evaluating
the character identities gives the two degree and order alternatives.
Construction of this package from local group hypotheses is kept in
`SemidihedralThreePrincipalCharacters`; consumers with supplied characters
can use this module independently of that existence theorem.

Source: Alperin--Brauer--Gorenstein, III.2 Proposition 6 and III.8
Proposition 1, article pp.68--69 and 111.
-/

namespace Stellmacher.Recognition
open ABG

/-- The actual odd-core intersection parameter in ABG III.8. -/
@[expose] public def threePrincipalCoreCentralizer
    {G : Type*} [Group G] (x : G) (T : Subgroup G) :=
  (Subgroup.centralizer (T : Set G)).subgroupOf
    ((pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype)

/-- The retained character data together with the geometric order identity. -/
public structure SemidihedralThreePrincipalCharacters
    (G : Type*) [Group G] [Finite G] (x : G) (T : Subgroup G)
    extends ThreePrincipalData G x where
  order_identity :
    (Nat.card G : ℤ) * ((degree 0 : ℤ) - 3)^2 =
      4608 * (Nat.card (threePrincipalCoreCentralizer x T) *
        (threePrincipalCoreCentralizer x T).index^3 : ℕ) *
          (degree 0 : ℤ) * ((degree 0 : ℤ) - 1)

namespace SemidihedralThreePrincipalCharacters
variable {G : Type*} [Group G] [Finite G] {x : G} {T : Subgroup G}
  (c : SemidihedralThreePrincipalCharacters G x T)

/-- Both ABG alternatives refer to the retained actual characters. -/
public theorem alternatives :
    let A := threePrincipalCoreCentralizer x T
    (c.degree 0 = 11 ∧ c.degree 1 = 45 ∧ c.degree 2 = 55 ∧
      c.degree 3 = 44 ∧ c.degree 4 = 10 ∧ Nat.card G = 7920 * (Nat.card A * A.index^3)) ∨
    (c.degree 0 = 27 ∧ c.degree 1 = 13 ∧ c.degree 2 = 39 ∧
      c.degree 3 = 12 ∧ c.degree 4 = 26 ∧ Nat.card G = 5616 * (Nat.card A * A.index^3)) :=
  three_principal_degree_order_alternatives _ _ _ _ _ _ _ _
    c.toThreePrincipalData.degree_identities.1 c.degree_product
    c.degree_first_congruence c.degree_second_congruence
    c.toThreePrincipalData.degree_identities.2.1
    c.toThreePrincipalData.degree_identities.2.2 c.order_identity

/-- The two involution values used in the nonprincipal-constituent argument. -/
public theorem first_two_involution_values :
    c.toThreePrincipalData.χ 1 (ConjClasses.mk x) = 3 ∧
      c.toThreePrincipalData.χ 2 (ConjClasses.mk x) = -3 :=
  ⟨c.toThreePrincipalData.involution_values 1, c.toThreePrincipalData.involution_values 2⟩

end SemidihedralThreePrincipalCharacters

end Stellmacher.Recognition
