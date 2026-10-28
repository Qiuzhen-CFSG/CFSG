module

public import Stellmacher.Recognition.SemidihedralThreePrincipalData
public import Stellmacher.MainDefs
public import ABG.ChapterII.Section1.FusionPatterns
public import Theory.Character.BrauerTuanThreePart
public import Theory.Character.CyclicThirteenBlock
public import Theory.GroupTheory.PrimeOrderSylowCentralizer

/-!
# The Case II three-part bound from the cyclic thirteen-block

The supplied semidihedral principal characters give degrees 27, 13, 39,
12, 26 and order 5616 times the odd-core parameter. In particular, 27
divides the group order. The rational degree-27 and degree-12 characters
are the two nonprincipal nonexceptional rows of the principal thirteen-block;
the cyclic degree equation gives four exceptional characters of degree 16.

A self-centralizing Sylow subgroup of order thirteen excludes elements of
order 39. Brauer--Tuan's block intersection argument then shows that 81
cannot divide the group order: the intersection sum is 27 or 15, and its
three-part divisibility excludes 15 and bounds the three-part by 27.
The Sylow geometry and the character package are explicit inputs.

Source: Alperin--Brauer--Gorenstein, III.8 Proposition 5, printed p.117,
`refs/original/n-group-global/semidihedral-source/abg-iii7-8.txt`;
Brauer--Tuan, *On simple groups of finite order I*, Bull. AMS 51 (1945),
Lemmas 2--3, DOI 10.1090/S0002-9904-1945-08441-9.
-/

namespace Stellmacher.Recognition
open ABG
namespace SemidihedralThreePrincipalCharacters
variable {G : Type*} [Group G] [Finite G] {x : G} {T : Subgroup G}
  (c : SemidihedralThreePrincipalCharacters G x T)

/-- The Case II degrees and order refer to the actual retained characters. -/
public theorem thirteen_degrees_order (hf : c.degree 1 = 13) :
    c.degree 0 = 27 ∧ c.degree 1 = 13 ∧ c.degree 2 = 39 ∧
      c.degree 3 = 12 ∧ c.degree 4 = 26 ∧
      Nat.card G = 5616 * (Nat.card (threePrincipalCoreCentralizer x T) *
        (threePrincipalCoreCentralizer x T).index ^ 3) := by
  rcases c.alternatives with h | h
  · omega
  · exact h

/-- All eight character degrees in the second alternative. -/
public theorem thirteen_row_degrees (hf : c.degree 1 = 13) (i : Fin 8) :
    c.toThreePrincipalData.χ i (ConjClasses.mk 1) =
      ((![1, 27, 13, 39, 12, 26, 26, 26] i : ℕ) : ℂ) := by
  obtain ⟨h0, h1, h2, h3, h4, _⟩ := c.thirteen_degrees_order hf
  simpa only [ThreePrincipalData.χ, h0, h1, h2, h3, h4] using c.degree_value i

/-- The lower half of the exact three-part assertion follows from the order formula. -/
public theorem twenty_seven_dvd_card (hf : c.degree 1 = 13) :
    27 ∣ Nat.card G := by
  rw [(c.thirteen_degrees_order hf).2.2.2.2.2]
  exact (by norm_num : 27 ∣ 5616).trans (dvd_mul_right _ _)

/-- The cyclic thirteen-block and Brauer--Tuan intersection theorem give the
upper half of the exact three-part assertion from the supplied Sylow geometry. -/
public theorem not_eightyOne_dvd_card [IsSimpleGroup G] (hf : c.degree 1 = 13)
    (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : automizerIndex (P : Subgroup G) = 3) :
    ¬ 81 ∣ Nat.card G := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨d⟩ := ModularBlock.PrimeBlockConstruction.exists_primeCongruenceBlockData 13 G
  obtain ⟨row, _, hrow₁, hrow₂, hdegrees, hvalues⟩ :=
    CyclicThirteenBlock.exists_rows P hP hC hindex
      (c.toThreePrincipalData.irreducible 1) (c.toThreePrincipalData.irreducible 4)
      (c.rational 1) (c.rational 4)
      (by simpa using c.thirteen_row_degrees hf 1)
      (by simpa using c.thirteen_row_degrees hf 4) d
  have hcard : Nat.card ↥P = 13 := hP
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : P)
  have horder : orderOf (u : G) = 13 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by simpa only [hcard] using pow_card_eq_one' (x := u)) hu
  apply BrauerTuan.not_eightyOne_dvd_of_thirteen_block d row hdegrees
    (c.twenty_seven_dvd_card hf) (fun g => ?_) u horder
    (by rw [hrow₁]; exact (hvalues u hu).1)
    (by rw [hrow₂]; exact (hvalues u hu).2)
  exact P.orderOf_ne_prime_mul_of_self_centralizing hP hC (q := 3) (by decide) g

end SemidihedralThreePrincipalCharacters

/-- ABG III.8 Proposition 5, Case II: the three-part is at most 27.
The original local and Schur hypotheses are retained; the parent supplies
the self-centralizing Sylow subgroup and its automizer of order three. -/
public theorem semidihedral_three_cyclic_not_eightyOne_dvd
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (_hS : IsSemidihedralGroup S) (_hN : IsNTwoGroup G)
    (x : G) (_hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (_hT : Nat.card T = 4) (_hxT : x ∈ T)
    (_hA : (threePrincipalCoreCentralizer x T).index ≠ 1)
    (c : SemidihedralThreePrincipalCharacters G x T) (hf : c.degree 1 = 13)
    (_hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (_hbound : Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13)
    (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : automizerIndex (P : Subgroup G) = 3) :
    ¬ 81 ∣ Nat.card G :=
  c.not_eightyOne_dvd_card hf P hP hC hindex

end Stellmacher.Recognition
