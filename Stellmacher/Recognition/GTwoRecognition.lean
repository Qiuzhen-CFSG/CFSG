module

public import Stellmacher.Recognition.GTwoWreathed
public import Stellmacher.Recognition.FongWreathed
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Global recognition of the order-32 G₂ local type

The G₂ local-type data and Sylow order 32 give a wreathed Sylow subgroup
of height two. Its presentation supplies an involution, whose centralizer
is solvable by the N₂ hypothesis. Fong's recognition theorem then identifies
the ambient simple group with `PSU₃(3)` through its degree-28 action.

The terminal-branch wrapper retains nonsolvability and trivial two-local
odd cores, although this recognition argument needs neither extra premise.

Sources: Stellmacher, *N-Gruppen*, (8.6)(a1,a2), journal p. 41;
P. Fong, *Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), Theorem 2, p. 71, and its proof on pp. 72–75.
-/

namespace Stellmacher.Recognition

/-- The order-32 G₂ local type in a simple N₂ group determines `PSU₃(3)`. -/
public theorem nonempty_equiv_psu3_of_nTwo_gTwo_card32
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hType : IsOfGTwoTwoDerivedType G)
    (hcard : Nat.card S = 32) (hN : IsNTwoGroup G) :
    Nonempty (G ≃* ABG.PSU3 3 1 (by decide)) := by
  have hS := wreathed_of_gTwoTwoDerived_type_of_card32 S hType hcard
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation hS
  have hx : orderOf (P.x : G) = 2 :=
    (Subgroup.orderOf_coe P.x).trans P.x_orderOf
  let : Group.IsSolvable (Subgroup.centralizer ({(P.x : G)} : Set G)) :=
    hN _ (Theory.GroupTheory.isTwoLocal_involution_centralizer hx)
  exact FongWreathed.nonempty_equiv_psu3 S hS P.x hx

/-- Global recognition under the original terminal G₂-branch hypotheses. -/
public theorem nonempty_equiv_psu3_of_gTwo_card32
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (_hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥)
    (hType : IsOfGTwoTwoDerivedType G) (hcard : Nat.card S = 32) :
    Nonempty (G ≃* ABG.PSU3 3 1 (by decide)) :=
  nonempty_equiv_psu3_of_nTwo_gTwo_card32 S hType hcard hN

end Stellmacher.Recognition
