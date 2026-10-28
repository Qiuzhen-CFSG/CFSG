module

public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import ABG.ChapterII.Section2.SemidihedralCentralizerIndex
public import ABG.Recognition.ThreeQuotientBlockExhaustion
public import ABG.Recognition.ThreeQuotientSectionAssembly
public import Stellmacher.Recognition.SemidihedralThreePrincipalCongruences

/-!
# The semidihedral principal block and signed-section assembly

The local odd-core quotient supplies Wong's induced catalog. Odd involution
class size excludes every extra principal-block row, giving exactly eight.
The section bridge and odd-order relations then assemble the signed section
package using the two degree congruences from restriction to the Sylow subgroup.

This module proves block exhaustion and section existence under the simple N2
hypotheses, without assuming the degree product or resolving the three signs.
Source: ABG III.2 Propositions 1--4 and 6, proved in III.5--6.
-/

namespace Stellmacher.Recognition
open ABG ModularBlock.PrincipalBlockConstruction

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The actual ambient principal block contains exactly the eight catalog rows. -/
public theorem semidihedral_principalBlock_card
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (b : PrincipalCongruenceBlockData G) :
    b.block.card = 8 := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  obtain ⟨d⟩ := exists_threeQuotientCharacterDecomposition x hx e
  exact threeQuotient_principalBlock_card x hx
    ((isQDGroup_of_simple ⟨S, hS⟩).odd_involution_class_card S hS x hx) e d b

/-- Final assembly with only the two signed Sylow restriction congruences
remaining. The block, catalog, and section witnesses are constructed here. -/
public theorem exists_threePrincipalSectionData_of_congruences
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (hcong : ∀ (e : (Subgroup.centralizer ({x} : Set G) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) ≃* GL2 3 1)
      (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e)),
      (16 ∣ -d.sign 0 * (d.principalSectionDegree 0 : ℤ) - 5) ∧
      (16 ∣ -d.sign 3 * (d.principalSectionDegree 1 : ℤ) - 3)) :
    Nonempty (ThreePrincipalSectionData G x) := by
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  obtain ⟨d⟩ := exists_threeQuotientCharacterDecomposition x hx e
  obtain ⟨b⟩ := exists_principalCongruenceBlockData G
  exact ⟨threeQuotientPrincipalSectionData x hx e d b
    (semidihedral_principalBlock_card S hS hN x hx b) (hcong e d).1 (hcong e d).2⟩

/-- The actual ambient principal block admits the signed section package,
including both degree congruences, under the simple semidihedral N2 hypotheses. -/
public theorem exists_threePrincipalSectionData
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    Nonempty (ThreePrincipalSectionData G x) := by
  apply exists_threePrincipalSectionData_of_congruences S hS hN x hx
  intro e d
  exact threeQuotient_principalCandidate_signed_degree_congruences S hS x hx hN e d

end Stellmacher.Recognition
