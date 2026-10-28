module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.ModelCases
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The universal source table needed by the degree-eight sieve

This is a forgetful interface to B.5.1(1) and the table in B.4.2, independent
of Chapter 15's local configuration. It is an explicit earlier-theorem input,
not a proof of that classification (whose owner is the B.5.1 development).
The input uses the complete known-simple class and the actual FF hypotheses.

All four branches of B.5.1(1) are retained. In the irreducible branch we forget
the offender ratios and the actions for groups which the sieve will exclude,
but retain actual group isomorphisms. The surviving actions are specified on
the literal quotient by fixed vectors. The small symplectic and G₂ cases use
their derived subgroups. The triple cover of A₆ is a surjective central cover
with kernel of order three, not a group-family tag. Natural modules may be
chosen up to a group isomorphism, which includes the contragredient choice.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2, printed
p.86; B.5.1(1) and its proof, pp.99–102; I.1.5–I.1.6(6), p.408. This interface
does not assert any A₈ recognition or any of the local module alternatives.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve
open Chapter2.ComponentRefinement.LieType.Binary

/-- Canonical fields keep the defining-field order separate from the dimension. -/
abbrev BinaryField (f : ℕ) := GaloisField 2 f

/-- The same actual projective action as `Models.naturalFour`, in any positive dimension. -/
noncomputable def natural (n : ℕ) [NeZero n] : Representation (ZMod 2) (PSL n) (Vector n) where
  toFun g := (pslEquivLinear n g).toLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

/-- The groups in B.4.2 other than its natural L₄/L₅ and orthogonal L₄ actions.
Only their actual group structure is needed to exclude them. Cases (5) and
(7) both allow A₇; case (11) retains the actual L₅(2) group. -/
inductive OtherIrreducibleGroup (H : Type*) [Group H] : Prop
  | linearTwo (f : ℕ) (positive : 0 < f)
      (model : H ≃* Matrix.SpecialLinearGroup (Fin 2) (BinaryField f))
  | linearThree (f : ℕ) (positive : 0 < f)
      (model : H ≃* Matrix.SpecialLinearGroup (Fin 3) (BinaryField f))
  | symplecticSmall
      (model : H ≃* commutator (Matrix.symplecticGroup (Fin 2) (BinaryField 1)))
  | symplecticLarge (f : ℕ) (large : 1 < f)
      (model : H ≃* Matrix.symplecticGroup (Fin 2) (BinaryField f))
  | g2Small (model : H ≃* commutator (Atlas.G2.Model (BinaryField 1)))
  | g2Large (f : ℕ) (large : 1 < f) (model : H ≃* Atlas.G2.Model (BinaryField f))
  | alternatingFive (model : H ≃* alternatingGroup (Fin 5))
  | alternatingSix (model : H ≃* alternatingGroup (Fin 6))
  | alternatingSeven (model : H ≃* alternatingGroup (Fin 7))
  | tripleSix (projection : H →* alternatingGroup (Fin 6))
      (onto : Function.Surjective projection) (central : projection.ker ≤ center H)
      (kernel : Nat.card projection.ker = 3)
  | linearFive (model : H ≃* PSL 5)

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- The natural quotient in B.4.2(9), without silently splitting its central cover. -/
structure NaturalQuotient (ρ : Representation (ZMod 2) K V) (L : Subgroup K)
    (n : ℕ) [NeZero n] where
  model : L ≃* PSL n
  coordinates : (V ⧸ fixedSpace ρ L) ≃ₗ[ZMod 2] Vector n
  equivariant : ∀ (l : L) v, coordinates ((fixedSpace ρ L).mkQ (ρ l v)) =
    natural n (model l) (coordinates ((fixedSpace ρ L).mkQ v))

/-- The action retained in B.5.1(1)(ii), over its actual defining field. -/
structure DoubleSLThree (ρ : Representation (ZMod 2) K V) (L : Subgroup K)
    (f : ℕ) where
  model : L ≃* Matrix.SpecialLinearGroup (Fin 3) (BinaryField f)
  coordinates : V ≃ₗ[ZMod 2] (Fin 2 → Fin 3 → BinaryField f)
  equivariant : ∀ (l : L) v i, coordinates (ρ l v) i =
    specialLinearNatural 3 (model l) (coordinates v i)

/-- B.5.1(1)(iii), in dimension four or five as specified by the table. -/
structure NaturalAndDual (ρ : Representation (ZMod 2) K V) (L : Subgroup K)
    (n : ℕ) [NeZero n] where
  model : L ≃* PSL n
  coordinates : V ≃ₗ[ZMod 2] (Vector n × Module.Dual (ZMod 2) (Vector n))
  equivariant : ∀ (l : L) v, coordinates (ρ l v) =
    ((natural n).prod (natural n).dual) (model l) (coordinates v)

/-- B.5.1(1)(iv), before specializing either dimension or multiplicity. -/
structure IsomorphicNaturals (ρ : Representation (ZMod 2) K V) (L : Subgroup K)
    (n r : ℕ) [NeZero n] where
  model : L ≃* PSL n
  coordinates : V ≃ₗ[ZMod 2] (Fin r → Vector n)
  equivariant : ∀ (l : L) v i, coordinates (ρ l v) i =
    natural n (model l) (coordinates v i)

/-- The forgetful B.4.2 table for the quotient in B.5.1(1)(i). -/
def IrreducibleTable (ρ : Representation (ZMod 2) K V) (L : Subgroup K) : Prop :=
  OtherIrreducibleGroup L ∨ Nonempty (NaturalQuotient ρ L 4) ∨
    Nonempty (NaturalQuotient ρ L 5) ∨ Nonempty (OrthogonalQuotient ρ L)

/-- All four branches of B.5.1(1), with B.4.2 expanded in branch (i).
This is universal classification output, and is not asserted to hold here. -/
def SourceCases (ρ : Representation (ZMod 2) K V) (L : Subgroup K) : Prop :=
  IrreducibleTable ρ L ∨
    (∃ f, 0 < f ∧ Nonempty (DoubleSLThree ρ L f)) ∨
    (Nonempty (NaturalAndDual ρ L 4) ∨ Nonempty (NaturalAndDual ρ L 5)) ∨
    (∃ r, 0 < r ∧ r ≤ 3 ∧ Nonempty (IsomorphicNaturals ρ L 4 r)) ∨
    (∃ r, 0 < r ∧ r ≤ 4 ∧ Nonempty (IsomorphicNaturals ρ L 5 r))

/-- The precise earlier-classification consequence consumed by the sieve.
No alternating-group hypothesis or Chapter 15 configuration occurs in this input.
The specialization `[V,L]=V` is already part of `FFInput`. -/
def UniversalFFClassification : Prop :=
  ∀ {K V : Type*} [Group K] [Finite K] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) K V) (L : Subgroup K),
    FFInput KnownSimple.IsKnownSimple ρ L → SourceCases ρ L

/-- I.1.6(6) for both choices of the natural module, in the dual coefficients
required by I.1.5. This is an earlier cohomological input, not a splitting premise. -/
def UniversalNaturalCohomology : Prop :=
  ∀ (n : ℕ) [NeZero n], (n = 4 ∨ n = 5) →
    Module.finrank (ZMod 2) (OneCohomology.H1 (natural n).dual) = 0

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve

end
