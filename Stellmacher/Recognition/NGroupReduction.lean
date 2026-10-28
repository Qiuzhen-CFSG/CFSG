module

public import Stellmacher.Recognition.CatalogueReduction
public import Stellmacher.Recognition.EvenUnitaryNotN

/-!
# The actual-model reduction for all-prime N-groups

Among the N2 models, the even-field PSU3 family fails the all-prime N
condition: a nontrivial torus element has a nonsolvable centralizer.
Transporting that obstruction through actual isomorphisms leaves exactly
the seven families in Thompson's N catalogue. Applying this specialization
to the proved simple N2 reduction gives the all-prime reduction below.

The exceptional local types, semidihedral alternative, order-32 local
configuration and odd-core involution centralizer remain explicit. Their
global recognition is still required to complete the classification.
Source: Kurzweil--Stellmacher, Appendix p.370, and GLS1 (28.1), with the
concrete matrix obstruction proved in the imported even-unitary module.
-/

namespace Stellmacher.Recognition
universe u

/-- The even-unitary extra family is excluded by the all-prime N condition. -/
public theorem isNGroupModel_of_isNTwoGroupModel
    {G : Type u} [Group G] [Finite G]
    (hN : IsNGroup G) (hmodel : IsNTwoGroupModel G) : IsNGroupModel G := by
  rcases hmodel with hmodel | ⟨n, hn, ⟨e⟩⟩
  · exact hmodel
  · exact (not_isNGroup_PSU3Model n hn ((isNGroup_iff_of_mulEquiv e).mp hN)).elim

/-- Actual N-models, or one of the still-unresolved global recognition cases. -/
public theorem simple_nGroup_catalogue_reduction
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNGroup G) (S0 : Sylow 2 G) :
    IsNGroupModel G ∨
    (IsOfGTwoTwoDerivedType G ∨ IsOfTwistedF4TwoDerivedType G) ∨
    IsSemidihedralGroup S0 ∨
    (Nat.card S0 = 2 ^ 5 ∧ ∃ U : Subgroup G, IsMaximalTwoLocal U ∧
      Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  rcases simple_nTwo_catalogue_reduction hns (isNTwoGroup_of_isNGroup hN) S0 with
    hmodel | hrest
  · exact Or.inl (isNGroupModel_of_isNTwoGroupModel hN hmodel)
  · exact Or.inr hrest

end Stellmacher.Recognition
