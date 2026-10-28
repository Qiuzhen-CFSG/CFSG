module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal.Reduction
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.Construction.StandardModel

/-!
# Geometric inputs for the Ree order-three centralizer calculation

One input constructs a representative in the actual exceptional fixed subgroup
and identifies its full centralizer with the identity-form SU₃ over GF(q²).
The other proves conjugacy of all order-three elements inside that same Ree
group. These are independent, unproved obligations, not source theorems.

The representative calculation must retain the central product of the two
algebraic A₂ components and its order-three center through exceptional descent.
The conjugacy calculation must descend from the algebraic class to the finite
fixed subgroup. Together they allow transport to every order-three subgroup;
they also suffice for both normalizer assertions, using permutation matrices
in the full SU₃. No simplicity or maximal-subgroup classification is an input.

Sources: GLS3, Table 4.7.3A (printed pp.225–229), component interchange on
p.232, and finite-class descent on pp.233–234, `refs/KGroup/GLS3/chapter4.tex`;
Example 2.6.3 (p.82), `refs/KGroup/GLS3/chapter2.tex`. Write q = 2^(2m+1);
GLS3's half-integer parameter has square q. Its representative is named t₂;
this does not identify it with coordinates of Malle's representative t₄.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal

open Subgroup

/-- Construct an order-three element of the genuine Ree carrier and its full
SU₃ centralizer. The equivalence is with SU₃, including its center, not PSU₃. -/
def RepresentativeCentralizerModels : Prop :=
  ∀ m, 1 ≤ m → ∃ t : Model m, orderOf t = 3 ∧
    Nonempty (centralizer ({t} : Set (Model m)) ≃*
      (SimpleNormal.Construction.standardForm m).specialSubgroup)

/-- The single order-three element class, with conjugators in the finite Ree
fixed subgroup. Algebraic conjugacy alone does not discharge this input. -/
def ThreeElementConjugacy : Prop :=
  ∀ m, 1 ≤ m → ∀ a b : Model m, orderOf a = 3 → orderOf b = 3 → IsConj a b

end ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal
