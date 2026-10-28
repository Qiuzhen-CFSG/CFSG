module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal
public import Mathlib.GroupTheory.Index

/-!
# Two concrete normalizer obligations for a symplectic Ree subgroup

For the supplied `S ≤ M ≤ Model m`, both problems concern its actual ambient
image `S.map M.subtype`. The first bounds the number of cosets in its
normalizer, taking properness as an explicit premise. The second asks for a
normalizing element outside that image and an ambient element outside the
normalizer. The latter supplies properness in final assembly, so the two
calculations can be developed independently. Neither is proved by this module.

The assumptions retain exactly the finite field, actual symplectic
equivalence, relative normality and centralizer supplied by
`SymplecticOvergroups`. In particular, the intrinsic isomorphism of `S`
does not assert conjugacy to a preferred embedded subgroup.

Source: G. Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E, Sections 2.2 and 2.11. The first constructs
the generic symplectic subgroup using Ree root subgroups and realizes its
graph automorphism. The second uses a binary symplectic subgroup and the
torus containing its elementary abelian subgroup of order nine to place an
arbitrary symplectic subgroup. These geometric arguments remain obligations;
an abstract isomorphism alone supplies neither placement nor the normalizer
witnesses. In Malle's notation `q²` is the ambient field size.

The resulting list entry is reproduced as case 9 in the proof of Theorem 5
of Himstedt–Nguyen–Tiep, arXiv:0910.4758, p.3. Neither that list nor these
definitions proves the requested normalizer assertions.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup Matrix

/-- The remaining upper bound for a proper ambient normalizer of the supplied
symplectic subgroup. The witness calculation supplies the properness premise. -/
def SymplecticNormalizerBound : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F],
        Nat.card F = 2 ^ (2 * m + 1) →
        (S ≃* symplecticGroup (Fin 2) F) →
        normalizer (S.map M.subtype : Set (Model m)) ≠ ⊤ →
        (S.map M.subtype).relIndex
          (normalizer (S.map M.subtype : Set (Model m))) ≤ 2

/-- The remaining concrete witnesses for nontriviality of the normalizer
extension and properness of that normalizer in the ambient Ree group. -/
def SymplecticNormalizerWitnesses : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F],
        Nat.card F = 2 ^ (2 * m + 1) →
        (S ≃* symplecticGroup (Fin 2) F) →
        ∃ t u : Model m,
          t ∈ normalizer (S.map M.subtype : Set (Model m)) ∧
          t ∉ S.map M.subtype ∧
          u ∉ normalizer (S.map M.subtype : Set (Model m))

end ReeF4.MaximalSubgroups.SimpleNormal
