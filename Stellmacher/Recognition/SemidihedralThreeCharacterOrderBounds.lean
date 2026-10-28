module

public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import Theory.Character.SchurSmallDegrees
public import ABG.ChapterIII.Section8.ThreeCharacterArithmetic

/-!
# Numerical assembly of semidihedral characteristic-three character bounds

For `N = C_G(x)`, write `K` for its odd core mapped into `G` and
`A = C_G(T) ∩ K`, viewed as a subgroup of `K`. The local quotient theorem
identifies `|N| = 48 |A| [K:A]`. A local degree-four Schur bound, the two
global order formulas, and the cyclic-defect congruences then imply the
numerical bounds used to eliminate a nontrivial index `[K:A]`.

The character-theoretic inputs are explicit hypotheses of the assembly
theorem below. This module is shared by the cyclic-block argument and the
unconditional assembly in `SemidihedralThreeCharacterBounds`, avoiding an
import cycle. No core-free centralizer is assumed here.

Source: Alperin--Brauer--Gorenstein, III.8 Proposition 1, Lemmas 1--4,
and Proposition 5, especially article pp.111 and 114--117.
-/

namespace Stellmacher.Recognition
open ABG
universe u

/-- The source parameters multiply to the order of the actual odd core. -/
public theorem involutionCentralizer_oddCore_card_eq_fourCentralizer_card_mul_index
    {G : Type u} [Group G] [Finite G] (x : G) (T : Subgroup G) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    Nat.card (pPrimeCore 2 N) = Nat.card A * A.index := by
  dsimp only
  rw [Subgroup.card_mul_index, Subgroup.card_map_of_injective
    (Subgroup.centralizer ({x} : Set G)).subtype_injective]

/-- The local quotient supplies the factor forty-eight in the source parameters. -/
public theorem involutionCentralizer_card_eq_fourCentralizer_parameters
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (T : Subgroup G) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    Nat.card N = 48 * (Nat.card A * A.index) := by
  dsimp only
  rw [involutionCentralizer_card_of_simple_nTwo S hS hN x hx,
    involutionCentralizer_oddCore_card_eq_fourCentralizer_card_mul_index x T]

/-- The local degree-four Sylow estimates imply the order bound `720`.
Producing those estimates from the local character is a separate input. -/
public theorem involutionCentralizer_card_dvd_of_degree_four_sylow_bounds
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ P : Sylow p (Subgroup.centralizer ({x} : Set G)),
        Nat.card P ∣ p ^ (4 / (p - 1)) * (4 / (p - 1)).factorial) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720 := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  obtain ⟨R, _, ⟨e⟩⟩ := hQD.exists_semidihedral_sylow_in_centralizer S hS x hx
  have hR : Nat.card R = 16 := (Nat.card_congr e.toEquiv).symm.trans
    (semidihedral_sylow_card_sixteen_of_simple_nTwo S hS hN)
  exact Theory.Character.card_dvd_degree_four_bound_of_sylow_bounds R hR hodd

/-- Assemble the exact bounds consumed by the odd-core elimination from
the remaining character and cyclic-defect inputs. No restrictions on `T`
are needed for this arithmetic step; they enter in proving those inputs. -/
public theorem semidihedral_three_character_bounds_of_order_data
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (T : Subgroup G)
    (hdata :
      let N := Subgroup.centralizer ({x} : Set G)
      let K := (pPrimeCore 2 N).map N.subtype
      let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
      let a := Nat.card A
      let b := A.index
      b ≠ 1 → Nat.card N ∣ 720 ∧
        ((Nat.card G = 7920 * (a * b^3) ∧
          Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11 ∧ (Nat.card G / 11) % 11 = 5) ∨
        (Nat.card G = 5616 * (a * b^3) ∧
          ¬ 81 ∣ Nat.card G ∧ (Nat.card G / 13) % 13 = 3))) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    let a := Nat.card A
    let b := A.index
    b ≠ 1 → a * b ∣ 15 ∧
      ((a * b^3 ∣ 3^4 * 5 ∧ a * b^3 % 11 = 1) ∨
        (Nat.Coprime (a * b) 3 ∧ a * b^3 % 13 = 1)) := by
  dsimp only at hdata ⊢
  intro hb
  obtain ⟨hlocal, hcases⟩ := hdata hb
  rw [involutionCentralizer_card_eq_fourCentralizer_parameters S hS hN x hx T] at hlocal
  exact threeCharacter_bounds_of_order_data hlocal hcases

end Stellmacher.Recognition
