module

public import Theory.Character.ModularBlock.CartanQuotient
public import Theory.Character.ModularBlock.PGroupCartan
public import Theory.Character.ModularBlock.SymmetricFourCartan

/-!
# Cartan computations from small quotients

A two-group quotient by an odd normal subgroup gives a singleton principal
Cartan matrix. A central subgroup of order four with quotient S₄ gives
matrix `[[16,8],[8,12]]`. These computations use actual simple modules and
ordinary decomposition rows through the quotient transfer theorems. Evaluating
the Cartan quadratic form gives the ordinary degree-square sums.

Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967),
printed p. 71, equations (6)–(7).
-/

public section
noncomputable section
namespace ModularBlock.Cartan
open PrincipalBlockConstruction CompatibleLocalBlock
open scoped BigOperators

variable {H : Type*} [Group H] [Finite H]

/-- A genuine singleton Cartan computation determines the ordinary block dimension. -/
theorem singleton_sum_degree_sq (d : PrincipalCongruenceBlockData H)
    (a : PrincipalDecompositionData d 1) {c : ℕ}
    (hdegree : a.family.degree 0 = 1) (hcartan : a.cartan 0 0 = c) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) ^ 2 = (c : ℂ) := by
  rw [a.sum_degree_sq]
  simp [hdegree, hcartan]

/-- The two-character matrix in Fong's local calculation has block dimension 96. -/
theorem twoCharacter_sum_degree_sq (d : PrincipalCongruenceBlockData H)
    (a : PrincipalDecompositionData d 2)
    (hd0 : a.family.degree 0 = 1) (hd1 : a.family.degree 1 = 2)
    (hc00 : a.cartan 0 0 = 16) (hc01 : a.cartan 0 1 = 8)
    (hc10 : a.cartan 1 0 = 8) (hc11 : a.cartan 1 1 = 12) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) ^ 2 = (96 : ℂ) := by
  rw [a.sum_degree_sq]
  norm_num [Fin.sum_univ_two, hd0, hd1, hc00, hc01, hc10, hc11]

/-- Odd-normal inflation of the two-group computation retains degree one and
has Cartan invariant equal to the quotient order. -/
theorem exists_twoGroup_oddQuotient_cartan
    (d : PrincipalCongruenceBlockData H) (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) (hQ : IsPGroup 2 (H ⧸ N)) :
    ∃ a : PrincipalDecompositionData d 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = Nat.card (H ⧸ N) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  let aQ := PGroupCartan.decompositionData q hQ
  refine ⟨aQ.ofOddQuotient d N hN, ?_, ?_⟩
  · rw [PrincipalDecompositionData.ofOddQuotient_degree]
    exact PGroupCartan.family_degree q hQ
  · rw [PrincipalDecompositionData.ofOddQuotient_cartan]
    exact PGroupCartan.cartan_eq_card q hQ

/-- A central order-four extension of S₄ has genuine principal Cartan matrix
`[[16,8],[8,12]]`, with simple modular degrees one and two. -/
theorem exists_centralFour_symmetricFour_cartan
    (d : PrincipalCongruenceBlockData H) (Z : Subgroup H) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center H) (hcard : Nat.card Z = 4)
    (e : (H ⧸ Z) ≃* Equiv.Perm (Fin 4)) :
    ∃ a : PrincipalDecompositionData d 2,
      a.family.degree 0 = 1 ∧ a.family.degree 1 = 2 ∧
      a.cartan 0 0 = 16 ∧ a.cartan 0 1 = 8 ∧
      a.cartan 1 0 = 8 ∧ a.cartan 1 1 = 12 := by
  have hZ : IsPGroup 2 Z := IsPGroup.of_card (n := 2) (by simpa using hcard)
  let q := (compatibleQuotientPrincipalCongruenceBlockData d Z).transport e
  let aS := SymmetricFourCartan.principalDecompositionData q
  obtain ⟨a, hd, hc⟩ := exists_centralTwoQuotient_of_equiv d Z hcentral hZ e aS
  refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [aS] using congrFun hd 0
  · simpa [aS] using congrFun hd 1
  · rw [hc, hcard,
      show aS.cartan 0 0 = 4 from
        SymmetricFourCartan.principalDecompositionData_cartan_zero_zero q]
  · rw [hc, hcard,
      show aS.cartan 0 1 = 2 from
        SymmetricFourCartan.principalDecompositionData_cartan_zero_one q]
  · rw [hc, hcard,
      show aS.cartan 1 0 = 2 from
        SymmetricFourCartan.principalDecompositionData_cartan_one_zero q]
  · rw [hc, hcard,
      show aS.cartan 1 1 = 3 from
        SymmetricFourCartan.principalDecompositionData_cartan_one_one q]

end ModularBlock.Cartan
