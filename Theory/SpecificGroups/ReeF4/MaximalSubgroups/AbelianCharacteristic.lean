module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics
public import Theory.GroupTheory.SolvableRadical.AbelianCharacteristic.Elementary
public import BenderSuzuki.MatrixGroups.Unitary

/-!
# Local inputs for Ree maximal subgroups with an abelian characteristic subgroup

The elementary characteristic-subgroup reduction separates the defining prime
two from the odd primes. At two, the needed input is a normalizer cover by a
proper full root-generated parabolic. At odd primes, the needed local analysis
identifies the nonsolvable maximal overgroup with the special-unitary extension
in Malle's list. The unitary layer is SU₃, with its central kernel retained,
and is normal of index two inside the maximal subgroup.

`TwoLocalCover` and `OddLocalStructure` are unproved geometric obligations,
not assertions of exhaustion. Their witnesses must be constructed from the
exceptional fixed-point model. No simplicity or classification hypothesis is
part of either contract. The independent generic reduction is imported from
`Theory.GroupTheory.SolvableRadical.AbelianCharacteristic.Elementary`.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E. The nonparabolic list, including the
distinct SU₃(q):2 and PGU₃(q):2 cases, is reproduced in the proof of Theorem 5
of arXiv:0910.4758, pp.2–3. The defining-prime route is finite Borel–Tits,
GLS3, Theorem 3.1.3 (`refs/KGroup/GLS3/chapter3.tex`).
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic

open Subgroup BenderSuzuki.MatrixGroups

/-- The defining-prime normalizer geometry, including properness of the full
parabolic. The image of `E` is only normal relative to `M`. -/
def TwoLocalCover : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → ∀ E : Subgroup M,
      E.Characteristic → IsElementaryAbelian 2 E → E ≠ ⊥ →
      ∃ (g : Model m) (s : LargeLocalSeeds.Side),
        ConverseParabolics.parabolic m s ≠ ⊤ ∧
        (normalizer (E.map M.subtype : Set (Model m))).map
          (MulAut.conj g).toMonoidHom ≤ ConverseParabolics.parabolic m s

/-- The odd-prime local classification still to be proved. The conclusion
contains an actual SU₃ matrix equivalence and the relative normal index-two
layer; it does not identify SU₃ with PGU₃ or assume a split extension. -/
def OddLocalStructure : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup M,
      E.Characteristic → IsElementaryAbelian p E → E ≠ ⊥ →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 ∧
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) ∧
        ∃ (N : Subgroup M) (_ : N.Normal),
          Nonempty (N ≃* J.specialSubgroup) ∧ Nat.card (M ⧸ N) = 2

end ReeF4.MaximalSubgroups.AbelianCharacteristic
