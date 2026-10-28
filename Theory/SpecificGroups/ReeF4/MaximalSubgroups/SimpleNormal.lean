module

public import Theory.SpecificGroups.ReeF4.Model
public import Theory.GroupTheory.SolvableRadical
public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Recognition and overgroup problems for simple normal Ree subgroups

The radical-free, almost-simple part of Malle's list has socle PSU₃(q),
Sp₄(q), or the derived subgroup of a smaller full Ree group. These definitions
separate recognition of the supplied simple subgroup from calculation of its
maximal overgroup. They assert no recognition or exhaustion theorem.

The unitary calculation must recover PGU₃(q) as a normal subgroup of index two;
an identification of the socle with PSU₃(q) does not provide that layer.
The symplectic calculation determines the index of the supplied simple normal
subgroup. The subfield calculation must recover the whole smaller Ree group
and a prime extension degree. Using its derived group only in `SocleType`
allows parameter zero without identifying the full binary Ree group with its
simple derived subgroup or requiring a separate comparison with a Tits model.

The application first separates off nontrivial centralizers by finite-group
component theory. Thus the remaining recognition and overgroup calculations
receive the genuine relative equality `C_M(S) = 1`.

Source: G. Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E. The unconditional list is reproduced inside
the proof of Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, pp.2–3.
The list motivates the obligations below; it is not a proof of them.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup Matrix BenderSuzuki.MatrixGroups

/-- Concrete possible socles. Every alternative retains a multiplicative
equivalence; there is no assertion here that these possibilities exhaust. -/
inductive SocleType (m : ℕ) (S : Type*) [Group S] : Prop where
  | unitary (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F = (2 ^ (2 * m + 1)) ^ 2)
      (hconj : ∀ x, J.conj x = x ^ (2 ^ (2 * m + 1)))
      (e : S ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  | symplectic (F : Type) [Field F] [Finite F]
      (hcard : Nat.card F = 2 ^ (2 * m + 1))
      (e : S ≃* symplecticGroup (Fin 2) F)
  | reeDerived (k : ℕ) (hlt : k < m) (hdiv : (2 * k + 1) ∣ (2 * m + 1))
      (e : S ≃* _root_.commutator (Model k))

/-- Remaining recognition obligation for a self-centralizing simple normal
subgroup. No simple-group catalogue is supplied as an input. -/
def SocleRecognition : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ → SocleType m S

/-- Remaining unitary overgroup calculation. The output is the projective
image of the full unitary group, not SU₃ or the supplied PSU₃ socle. -/
def UnitaryOvergroups : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 →
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) →
        (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        ∃ N : Subgroup M, N.Normal ∧
          Nonempty (N ≃* J.unitarySubgroup.map ProjGenLinGroup.mk) ∧
          Nat.card (M ⧸ N) = 2

/-- Remaining symplectic overgroup calculation: the actual Sp₄ socle has
index two in the whole maximal subgroup. -/
def SymplecticOvergroups : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F],
        Nat.card F = 2 ^ (2 * m + 1) →
        (S ≃* symplecticGroup (Fin 2) F) → Nat.card (M ⧸ S) = 2

/-- Remaining subfield overgroup calculation. The recognition input is only
the derived subgroup; the output identifies the entire `Model k`, also at
`k = 0`, and proves the source prime-power relation. -/
def SubfieldOvergroups : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ k, k < m → (2 * k + 1) ∣ (2 * m + 1) →
        (S ≃* _root_.commutator (Model k)) →
        ∃ a, Nat.Prime a ∧ 2 ^ (2 * m + 1) = (2 ^ (2 * k + 1)) ^ a ∧
          Nonempty (M ≃* Model k)

end ReeF4.MaximalSubgroups.SimpleNormal
