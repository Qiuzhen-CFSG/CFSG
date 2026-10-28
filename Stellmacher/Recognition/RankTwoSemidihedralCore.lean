module

public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import ABG.ChapterIII.Section8.ThreeCoreArithmetic
public import ABG.ChapterII.Section2.SemidihedralInvolutionFour
public import Stellmacher.Recognition.SemidihedralThreeCharacterBounds
public import Stellmacher.Recognition.SemidihedralCentralizingCore

/-!
# Trivial involution-centralizer odd cores in the semidihedral N₂ branch

The already proved local quotient theorem gives GL2(3) modulo the odd core.
Here the arithmetic at the end of ABG III.8 is connected to the actual
centralizer index. Its character bounds force the odd core to centralize the
chosen four-group. Once the normalizer argument kills such a core, the actual
involution centralizer is GL2(3), requiring no premise about other two-local
subgroups.

The global character bounds and the centralizing-core normalizer argument
discharge both inputs of the saved reductions. QD fusion supplies a four-group
through every involution. Thus each odd core is trivial and each actual
involution centralizer is GL2(3), without any local core-freeness premise.

Source: Alperin--Brauer--Gorenstein, III.7 Corollary 2 and III.8 Proposition 5,
article pp.110 and 117; see the preserved scan and source audit in
`refs/original/n-group-global/semidihedral-source/`.
-/

namespace Stellmacher.Recognition
open ABG
universe u

/-- Vanishing of the odd core of this particular centralizer suffices for its
actual GL2(3) model; no hypothesis on other two-local subgroups is needed. -/
public theorem involutionCentralizer_equiv_gl2_three_of_oddCore_eq_bot
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (hcore : pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥) :
    Nonempty (Subgroup.centralizer ({x} : Set G) ≃* GL2 3 1) := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hcore).symm).trans e⟩

/-- The source character bounds imply that an actual odd core centralizes the
chosen subgroup. The group-theoretic nature of the subgroup is needed when
proving those bounds, not for this final index argument. -/
public theorem involutionCentralizer_oddCore_le_centralizer_of_character_bounds
    {G : Type u} [Group G] [Finite G] (x : G) (T : Subgroup G)
    (hbounds :
      let K := (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype
      let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
      let a := Nat.card A
      let b := A.index
      b ≠ 1 → a * b ∣ 15 ∧
        ((a * b ^ 3 ∣ 3 ^ 4 * 5 ∧ a * b ^ 3 % 11 = 1) ∨
          (Nat.Coprime (a * b) 3 ∧ a * b ^ 3 % 13 = 1))) :
    (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype ≤
        Subgroup.centralizer (T : Set G) := by
  exact Subgroup.subgroupOf_eq_top.mp
    (Subgroup.index_eq_one.mp (threeCore_index_eq_one_of_bounds hbounds))

/-- Final assembly of the numerical and normalizer steps, with both remaining
mathematical inputs explicit. -/
public theorem involutionCentralizer_oddCore_eq_bot_of_character_bounds
    {G : Type u} [Group G] [Finite G] (x : G) (T : Subgroup G)
    (hkill :
      (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype ≤
          Subgroup.centralizer (T : Set G) →
      pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥)
    (hbounds :
      let K := (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype
      let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
      let a := Nat.card A
      let b := A.index
      b ≠ 1 → a * b ∣ 15 ∧
        ((a * b ^ 3 ∣ 3 ^ 4 * 5 ∧ a * b ^ 3 % 11 = 1) ∨
          (Nat.Coprime (a * b) 3 ∧ a * b ^ 3 % 13 = 1))) :
    pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ :=
  hkill (involutionCentralizer_oddCore_le_centralizer_of_character_bounds x T hbounds)

/-- In a finite simple semidihedral N₂-group every involution centralizer has
trivial odd core. No hypothesis on the odd cores of two-local subgroups is needed. -/
public theorem involutionCentralizer_oddCore_eq_bot_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  obtain ⟨T, hTe, hT, hxT⟩ :=
    (isQDGroup_of_simple ⟨S, hS⟩).exists_four_containing_involution S hS x hx
  let : IsElementaryAbelian 2 T := hTe
  exact involutionCentralizer_oddCore_eq_bot_of_character_bounds x T
    (involutionCentralizer_oddCore_eq_bot_of_centralizing_four S hS hN x hx T hT hxT)
    (semidihedral_three_character_bounds S hS hN x hx T hT hxT)

/-- The actual involution centralizers in the simple semidihedral N₂ branch
are GL2(3), with no additional odd-core hypothesis. -/
public theorem involutionCentralizer_equiv_gl2_three_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    Nonempty (Subgroup.centralizer ({x} : Set G) ≃* GL2 3 1) := by
  exact involutionCentralizer_equiv_gl2_three_of_oddCore_eq_bot S hS hN x hx
    (involutionCentralizer_oddCore_eq_bot_of_simple_nTwo S hS hN x hx)

end Stellmacher.Recognition
