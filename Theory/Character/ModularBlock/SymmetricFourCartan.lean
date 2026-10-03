module

public import Theory.Character.ModularBlock.SymmetricFourCartanData
public import Theory.Character.ModularBlock.SymmetricFourOrdinary
public import Theory.Character.ModularBlock.SymmetricFourSimpleModules

/-!
# The characteristic-two Cartan computation for S₄

The five ordinary characters and the two characteristic-two simple modules
give decomposition rows `(1,0), (1,0), (0,1), (1,1), (1,1)`. The ordinary
central-character congruences put every row in the prescribed principal block;
the lifted eigenvalue computations identify their genuine Brauer restrictions.
Their Gram matrix is `[[4,2],[2,3]]`, with modular degrees `1,2`, and the
ordinary principal-block degree-square sum is 24.

Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967), p. 71.
-/

public section
noncomputable section

namespace ModularBlock.SymmetricFourCartan

open scoped BigOperators
open PrincipalBlockConstruction Cartan

variable (d : PrincipalCongruenceBlockData Group)

/-- Genuine characteristic-two principal decomposition data for S₄ at any
prescribed congruence datum. -/
def principalDecompositionData : PrincipalDecompositionData d 2 :=
  decompositionData (ordinaryCharacterData d) (simpleModuleData d)

@[simp] theorem principalDecompositionData_degree_zero :
    (principalDecompositionData d).family.degree 0 = 1 :=
  decompositionData_degree (ordinaryCharacterData d) (simpleModuleData d) 0

@[simp] theorem principalDecompositionData_degree_one :
    (principalDecompositionData d).family.degree 1 = 2 :=
  decompositionData_degree (ordinaryCharacterData d) (simpleModuleData d) 1

@[simp] theorem principalDecompositionData_cartan_zero_zero :
    (principalDecompositionData d).cartan 0 0 = 4 :=
  cartan_zero_zero (ordinaryCharacterData d) (simpleModuleData d)

@[simp] theorem principalDecompositionData_cartan_zero_one :
    (principalDecompositionData d).cartan 0 1 = 2 :=
  cartan_zero_one (ordinaryCharacterData d) (simpleModuleData d)

@[simp] theorem principalDecompositionData_cartan_one_zero :
    (principalDecompositionData d).cartan 1 0 = 2 :=
  cartan_one_zero (ordinaryCharacterData d) (simpleModuleData d)

@[simp] theorem principalDecompositionData_cartan_one_one :
    (principalDecompositionData d).cartan 1 1 = 3 :=
  cartan_one_one (ordinaryCharacterData d) (simpleModuleData d)

/-- The actual principal-block Cartan matrix of S₄ has entries `[[4,2],[2,3]]`
in trivial-first order, and its simple modules have dimensions one and two. -/
theorem exists_decompositionData :
    ∃ a : PrincipalDecompositionData d 2,
      a.family.degree 0 = 1 ∧ a.family.degree 1 = 2 ∧
      a.cartan 0 0 = 4 ∧ a.cartan 0 1 = 2 ∧
      a.cartan 1 0 = 2 ∧ a.cartan 1 1 = 3 :=
  ⟨principalDecompositionData d, principalDecompositionData_degree_zero d,
    principalDecompositionData_degree_one d,
    principalDecompositionData_cartan_zero_zero d,
    principalDecompositionData_cartan_zero_one d,
    principalDecompositionData_cartan_one_zero d,
    principalDecompositionData_cartan_one_one d⟩

/-- All five ordinary irreducibles belong to the principal two-block, whose
degree-square sum is `1 + 1 + 4 + 9 + 9 = 24`. -/
theorem sum_degree_sq :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) ^ 2 = (24 : ℂ) :=
  sum_degree_sq_of_ordinaryData (ordinaryCharacterData d)

end ModularBlock.SymmetricFourCartan
