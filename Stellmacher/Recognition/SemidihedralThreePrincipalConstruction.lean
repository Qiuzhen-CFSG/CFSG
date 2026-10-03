module

public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import ABG.ChapterII.Section2.SemidihedralEightRoots
public import ABG.ChapterIII.Section2.ThreePrincipalData
public import ABG.ChapterIII.Section7.ThreePrincipalDegreeProduct
public import ABG.Recognition.ThreeQuotientPrincipalBlock
public import ABG.Recognition.ThreeQuotientRelations
public import Stellmacher.Recognition.SemidihedralThreePrincipalSections
public import Theory.Character.ModularBlock.InvolutionPairVanishing

/-!
# The semidihedral principal-block construction

The odd-core quotient theorem identifies the exact compatible local principal
block with the eight inflated GL₂(3) characters. Its squared degrees sum to 48,
so principal local column orthogonality computes the ambient involution-column
norm. The local degree-three row, the order-eight root, and the seven-character
induced catalog are all obtained without a core-free centralizer assumption.

The signed section construction enumerates the actual ambient principal block.
Blockwise involution-pair vanishing at a nonreal order-eight element gives the
degree product, and the signed degree congruences resolve the signs. Together
these prove existence of `ThreePrincipalData` under the simple semidihedral N₂
hypotheses.
Source: ABG II.1 Proposition 1, III.2 Propositions 1--7 and Corollary 2,
proved in III.5--7; Wong (1964), equation (3) and Appendix, via
`ThreeQuotientInduction`.
-/

namespace Stellmacher.Recognition
open ABG ModularBlock.PrincipalBlockConstruction ModularBlock.CompatibleBrauerBlock
open scoped BigOperators

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Every involution is the fourth power of an element of order eight. -/
public theorem exists_order_eight_fourth_eq_of_simple_nTwo
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    ∃ a : G, orderOf a = 8 ∧ a ^ 4 = x :=
  (isQDGroup_of_simple ⟨S, hS⟩).exists_order_eight_fourth_eq S hS
    (semidihedral_sylow_card_sixteen_of_simple_nTwo S hS hN) x hx

/-- The compatible local block has exactly eight actual irreducible rows. -/
public theorem semidihedral_local_principalBlock_card
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (d : PrincipalCongruenceBlockData G) :
    (localData d (Subgroup.centralizer ({x} : Set G))).block.card = 8 := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  exact threeOddCore_principalBlock_card e _

/-- The degree-three witness belongs to the prescribed compatible local block. -/
public theorem semidihedral_local_exists_degree_three_principal_row
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (d : PrincipalCongruenceBlockData G) :
    ∃ j : (localData d (Subgroup.centralizer ({x} : Set G))).I,
      j ∈ (localData d (Subgroup.centralizer ({x} : Set G))).block ∧
      (localData d (Subgroup.centralizer ({x} : Set G))).chi j (ConjClasses.mk 1) = 3 := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  obtain ⟨j, hj, _, hd⟩ := threeOddCore_principalBlock_exists_degree_three e
    (localData d (Subgroup.centralizer ({x} : Set G)))
  exact ⟨j, hj, hd⟩

/-- Local orthogonality gives the ambient principal-block column norm 48. -/
public theorem semidihedral_principalBlock_involution_column_norm
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (d : PrincipalCongruenceBlockData G) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk x) *
      star (d.chi i (ConjClasses.mk x)) = 48 := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  have hp : x ^ (2 ^ 1) = 1 := by
    simpa only [pow_one, hx] using pow_orderOf_eq_one x
  rw [ModularBlock.LocalColumnNorm.principalBlock_local_column_norm d x ⟨1, hp⟩]
  exact threeOddCore_principalBlock_degree_square_sum e _

/-- One local quotient supplies all seven distinct nontrivial ambient characters. -/
public theorem semidihedral_exists_quotient_character_catalog
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    ∃ e : (Subgroup.centralizer ({x} : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) ≃* GL2 3 1,
      Nonempty (ThreeCharacterDecomposition (threeQuotientInducedGenerator x e)) := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  exact ⟨e, exists_threeQuotientCharacterDecomposition x hx e⟩

omit [IsSimpleGroup G] in
/-- Final assembly from the signed section construction and the generic
blockwise vanishing theorem. Neither input assumes resolved degrees or signs. -/
public theorem exists_threePrincipalData_of_sections_and_nonreal_vanishing
    (x : G) (hsections : Nonempty (ThreePrincipalSectionData G x))
    (hvan : ∀ (d : PrincipalCongruenceBlockData G) (u : G),
      orderOf u = 8 → ¬ IsConj u u⁻¹ →
        ∑ i ∈ d.block, d.chi i (ConjClasses.mk x)^2 *
          d.chi i (ConjClasses.mk u) / d.chi i (ConjClasses.mk 1) = 0) :
    Nonempty (ThreePrincipalData G x) := by
  obtain ⟨c⟩ := hsections
  exact ⟨c.toPrincipalDataOfNonrealVanishing (hvan c.blockData)⟩

/-- The actual principal two-block has the full ABG characteristic-three
character package under the simple semidihedral N₂ hypotheses. -/
public theorem exists_threePrincipalData
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    Nonempty (ThreePrincipalData G x) := by
  apply exists_threePrincipalData_of_sections_and_nonreal_vanishing x
    (exists_threePrincipalSectionData S hS hN x hx)
  intro d u hu hnonreal
  exact ModularBlock.InvolutionPairVanishing.principalBlock_pairSum_eq_zero_of_nonreal_order_eight
    d x u hx hu hnonreal

end Stellmacher.Recognition
