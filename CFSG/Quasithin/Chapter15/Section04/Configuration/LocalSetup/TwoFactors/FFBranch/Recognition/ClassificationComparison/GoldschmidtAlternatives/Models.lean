module
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicModel
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.Mathieu.M12.Basic
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Concrete groups and extension actions in F.6.18

These predicates retain actual matrix and permutation groups, quotient maps,
and conjugation formulas. A slash denotes a group extension with the displayed
kernel and quotient, not a quotient of the group named on the left. No splitting
is imposed. The hat on an alternating group denotes its perfect central triple
cover; on a symmetric group it retains that cover over the alternating subgroup
and the odd permutation action on its center.

The graph representative is inverse transpose for SL₃ and coefficient conjugation
for SU₃. The latter uses the standard antidiagonal Hermitian form. The parameter
of a unitary group is the fixed-field order. The quaternion square is the central
product of two actual commuting quaternion subgroups with common center of order
two, whereas Z₄² is a direct product.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18, pp.309–310; A.1.22, A.3.5, I.1.1 and F.1.12.
The imported field transport retains the attribution and license of the ATLAS
port. This module defines the source alternatives; it proves no classification.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.GoldschmidtAlternatives
universe u v w
abbrev C (n : ℕ) := Multiplicative (ZMod n)
abbrev E4 := C 2 × C 2
abbrev C4Square := C 4 × C 4
abbrev S3 := Equiv.Perm (Fin 3)
abbrev S4 := Equiv.Perm (Fin 4)

/-- The source `Q/N` extension notation: an actual surjection with kernel
isomorphic to N. No complement or splitting is imposed. -/
def Extension (G : Type u) [Group G] (N : Type v) [Group N]
    (Q : Type w) [Group Q] : Prop :=
  ∃ f : G →* Q, Function.Surjective f ∧ Nonempty (f.ker ≃* N)

/-- The source Q₈² is a central product, not a direct product. -/
def QuaternionSquareExtension (G : Type u) [Group G]
    (Q : Type v) [Group Q] : Prop :=
  ∃ f : G →* Q, Function.Surjective f ∧ Nonempty (QuaternionCentralProductData f.ker)

/-- A genuine triple cover, with the perfectness excluding the split product. -/
def TripleAlternating (G : Type u) [Group G] (n : ℕ) : Prop :=
  Group.IsPerfect G ∧ Nonempty (center G ≃* C 3) ∧
    Nonempty ((G ⧸ center G) ≃* alternatingGroup (Fin n))

/-- The triple symmetric cover retains its literal permutation quotient,
perfect alternating preimage, and the inversion action of odd permutations
on the three-kernel. -/
def TripleSymmetric (G : Type u) [Group G] (n : ℕ) : Prop :=
  ∃ f : G →* Equiv.Perm (Fin n), Function.Surjective f ∧
    Nonempty (f.ker ≃* C 3) ∧ Group.IsPerfect ((alternatingGroup (Fin n)).comap f) ∧
    (∀ g : G, ∀ z : f.ker,
      g * z.val * g⁻¹ = if Equiv.Perm.sign (f g) = 1 then z.val else z.val⁻¹)

/-- An index-two extension with the prescribed actual conjugation action.
The outside lift is not required to square to one, retaining nonsplit extensions. -/
def ExtensionBy (G : Type u) [Group G] {M : Type v} [Group M]
    (a : MulAut M) : Prop :=
  ∃ (i : M →* G) (t : G), Function.Injective i ∧ i.range.index = 2 ∧
    t ∉ i.range ∧ ∀ x, t * i x * t⁻¹ = i (a x)

/-- The fixed field has order p, and the coefficient field has order p². -/
def FieldExtension (G : Type u) [Group G] (p : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ 2 ∧
    ∃ σ : F ≃+* F, (∀ x, σ x = x ^ p) ∧
      ExtensionBy G (Atlas.fieldEquivPSL 2 σ)

/-- The special/projective linear alternatives of the specified field order. -/
def LinearThree (G : Type u) [Group G] (p : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    (Nonempty (G ≃* SL(3,F)) ∨ Nonempty (G ≃* PSL(3,F)))

/-- The special/projective unitary alternatives; p is the fixed-field order. -/
def UnitaryThree (G : Type u) [Group G] (p : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F),
    Nat.card F = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧
    (Nonempty (G ≃* J.specialSubgroup) ∨
      Nonempty (G ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))

/-- Graph extensions of the actual special or projective linear group. -/
def LinearGraphExtension (G : Type u) [Group G] (p : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    (ExtensionBy G (Matrix.PSL3.OuterSolvable.graphSL F) ∨
      ExtensionBy G (Matrix.PSL3.OuterSolvable.graph F))

/-- For the unitary group the graph action is the coefficient involution.
The antidiagonal form fixes a concrete representative of that action. -/
def UnitaryGraphExtension (G : Type u) [Group G] (p : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F),
    Nat.card F = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧
    ∃ hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0],
      ExtensionBy G (J.specialGraphAut hJ) ∨ ExtensionBy G (J.projectiveGraphAut hJ)

/-- PGL₂ uses its actual projective general linear carrier. -/
def PGLTwo (G : Type u) [Group G] (p : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    Nonempty (G ≃* PGL(2, F))
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.GoldschmidtAlternatives
