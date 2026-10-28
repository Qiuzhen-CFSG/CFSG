module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.ProjectiveExtension

/-!
# Geometric obligations for the projective unitary normalizer

Write S₀ for the ambient image of the supplied simple subgroup, K for its
normalizer, and H for the image of the actual projective unitary extension.
The normalizer calculation separates into two independent geometric problems.

The witness problem asks for an element displacing S₀ and an element of K
outside H. The coset problem asks whether two elements of K outside H have
their quotient in H. It takes those elements as inputs, so it can be proved
without constructing the witnesses. Together these facts imply that K is
proper and that H is normal in K with index two.

These definitions retain every hypothesis of `UnitaryExtensionNormalizers`.
Neither obligation is asserted to hold here. They must be proved for every
supplied extension, not just for an unconnected standard unitary subgroup.
In particular, the relative equality C_M(S) = 1 is not an assertion about
the ambient centralizer C_G(S₀).

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E. The relevant PGU₃(q):2 entry is case 7
of the unconditional list in the proof of Theorem 5 of Himstedt–Nguyen–Tiep,
arXiv:0910.4758, p.3. Here q = 2^(2m+1) and the matrix field has order q².
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup Matrix BenderSuzuki.MatrixGroups

/-- Construct both the displacement certifying properness and a second
normalizer coset. The witnesses must come from the actual Ree carrier. -/
@[expose] def UnitaryNormalizerWitnesses : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 →
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) →
        (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        ∀ E : ProjectiveExtension (S.map M.subtype) J,
          (∃ g s : Model m, s ∈ S.map M.subtype ∧
            g * s * g⁻¹ ∉ S.map M.subtype) ∧
          ∃ t : Model m,
            t ∈ normalizer (S.map M.subtype : Set (Model m)) ∧
            t ∉ E.embedding.range

/-- There is at most one coset outside the embedded PGU subgroup. This
problem takes an arbitrary outside element as input; it does not assert
that such an element exists, nor that the normalizer is proper. -/
@[expose] def UnitaryNormalizerCosetControl : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 →
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) →
        (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        ∀ E : ProjectiveExtension (S.map M.subtype) J,
          ∀ t ∈ normalizer (S.map M.subtype : Set (Model m)),
            t ∉ E.embedding.range →
            ∀ x ∈ normalizer (S.map M.subtype : Set (Model m)),
              x ∉ E.embedding.range → x * t⁻¹ ∈ E.embedding.range

end ReeF4.MaximalSubgroups.SimpleNormal
