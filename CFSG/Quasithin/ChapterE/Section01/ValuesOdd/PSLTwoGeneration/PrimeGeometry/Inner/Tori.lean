module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori.Seed
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori.Placement

/-!
# Prime dihedral tori through four-group Sylow actors in PSL₂

For a prime field of odd order greater than five, select the even split or
nonsplit torus. A Sylow subgroup of order four forces its two-part to be two;
its nontrivial odd part supplies a prime dihedral subgroup. Involution fusion
moves its central involution to the prescribed actor involution, and Sylow
conjugacy inside that involution's centralizer places the whole actor in it.

The final conditional application discharges the literal torus input of
`concreteLocalGeometryAt_of_involution_tori`. Only the independent bound on
centralizers in proper overgroups remains explicit.

Source: Aschbacher--Smith, E.1.2 and E.1.14(6), printed pp.209--210 and 214,
citing Aschbacher (1982), Lemma 4.10. The concrete tori are constructed by the
proved split and nonsplit Huppert II.8.3--4 interfaces.
-/

public section

open Subgroup GorensteinWalter

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The literal torus witnesses for the order-four Sylow branch: each specified
actor involution is centralized by a prime dihedral subgroup containing the actor. -/
theorem involution_tori_of_sylow_card_four
    {p : ℕ} (hp : p.Prime) (hpo : Odd p) (hp5 : 5 < p)
    (hF : Nat.card F = p) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (hT : Nat.card T = 4)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup G))
    (z : G) (hzA : z ∈ A) (hz : z ≠ 1) :
    ∃ (r : ℕ) (H : Subgroup G), r.Prime ∧ Odd r ∧
      A ≤ H ∧ H ≤ centralizer ({z} : Set G) ∧
      Nonempty (H ≃* DihedralGroup (2 * r)) := by
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hpo, by decide, by simpa using hF⟩
  have hfusion : ∀ x y : G, IsInvolution x → IsInvolution y →
      ∃ g : G, g * x * g⁻¹ = y := by
    intro x y hx hy
    have hex : IsInvolution (e x) :=
      ⟨fun h => hx.1 (e.injective (by simpa using h)), by
        simpa only [map_pow, map_one] using congrArg e hx.2⟩
    have hey : IsInvolution (e y) :=
      ⟨fun h => hy.1 (e.injective (by simpa using h)), by
        simpa only [map_pow, map_one] using congrArg e hy.2⟩
    obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd (e x) (e y) hex hey
    refine ⟨e.symm g, ?_⟩
    apply e.injective
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hg
  obtain ⟨r, D, t, hr, hro, _, ht, hDC, ⟨eD⟩⟩ :=
    Tori.prime_dihedral_seed hp hpo hp5 hF e T hT
  obtain ⟨H, hAH, hHC, hH⟩ :=
    Tori.place_dihedral_through_four T hT hfusion A hA hAT z hzA hz D t ht hDC eD
  exact ⟨r, H, hr, hro, hAH, hHC, hH⟩

/-- Conditional local geometry for the four-group Sylow branch. The sole extra
input is the exact small-centralizer premise supplied by the Overgroups producer. -/
theorem concreteLocalGeometryAt_of_sylow_card_four
    {p : ℕ} (hp : p.Prime) (hpo : Odd p) (hp5 : 5 < p)
    (hF : Nat.card F = p) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (hT : Nat.card T = 4)
    (hsmall : ∀ A M : Subgroup G, IsKleinFour A → A ≤ M → M ≠ ⊤ →
      ∃ z : G, z ∈ A ∧ z ≠ 1 ∧
        Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ≤ 8) :
    ConcreteLocalGeometryAt T := by
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hpo, by decide, by simpa using hF⟩
  exact concreteLocalGeometryAt_of_involution_tori hodd e T hsmall
    (involution_tori_of_sylow_card_four hp hpo hp5 hF e T hT)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
