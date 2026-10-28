module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedReduction
public import CFSG.Quasithin.ChapterE.Section06.Basic
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The field fixed space in the contained branch of 6.1.15

The exceptional subspace in 6.1.13 is fixed by an element whose action on
the literal quotient L/O₂(L) is an involutory field automorphism. The
definition below records that action on every quotient representative,
using a genuine SL₂ marking and entrywise application of a nonidentity
field involution. Normalization of the module is also explicit.

This is the interface between the fixed-space classification in 6.1.13
and the local argument in 6.1.14(5); it asserts neither result.
Source: Aschbacher--Smith, printed pp.670--672 (PDF pp.687--689).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G]

/-- The field alternative of 6.1.13, with its actual quotient action.
The marking may be chosen so that the field involution is entrywise;
thus inner conjugates of field automorphisms are included. -/
def IsInvolutoryFieldFixedSpace (L M B U : Subgroup G) (n : ℕ) : Prop :=
  ∃ t : normalizer (L : Set G),
    (t : G) ∈ M ∧ (t : G) ∈ normalizer (B : Set G) ∧
    U = B ⊓ centralizer ({(t : G)} : Set G) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧
      ∃ (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
        (σ : F ≃+* F),
        σ ≠ 1 ∧ σ ^ 2 = 1 ∧
        ∀ l : L,
          e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom t l)) =
            Theory.PSL2.sl2FieldAut σ (e (QuotientGroup.mk' (pCore 2 L) l))

/-- The corank conclusion of 6.1.10(3), pulled back by g⁻¹ to B.
It also records that the fixed space is nonzero, as follows from
|B| = 2^(2n) and n > 0. This is a pending source input, not a theorem. -/
def ConjugateCorankFormula (T B : Subgroup G) (n : ℕ) : Prop :=
  ∀ g : G, B.map (MulAut.conj g).toMonoidHom ≤ T →
    ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G) →
    let U := B ⊓ centralizer (B.map (MulAut.conj g⁻¹).toMonoidHom : Set G)
    U ≠ ⊥ ∧ ChapterE.subgroupCorank B U = n

/-- The fusion conclusion of 6.1.11. Commutator containment in both
subgroups is expressed as mutual normalization. -/
def MutualConjugateFusion (T B Z : Subgroup G) : Prop :=
  ∀ g : G, B.map (MulAut.conj g).toMonoidHom ≤ T →
    ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G) →
    B ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G) →
    ∃ c ∈ centralizer (Z : Set G),
      B.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj c).toMonoidHom

/-- The local fixed-space classification used to prove 6.1.13.
The first row is the local centralizer equality; E.6.12 supplies its
global consequence in `source_ordinary_fixed_space_centralizer`. -/
def FixedSpaceAlternatives (L M B Z : Subgroup G) (n : ℕ) : Prop :=
  ∀ U : Subgroup G, U ≤ B → U ≠ ⊥ → ChapterE.subgroupCorank B U = n →
    M ⊓ centralizer (U : Set G) = M ⊓ centralizer (B : Set G) ∨
    (∃ l ∈ L, U = Z.map (MulAut.conj l).toMonoidHom) ∨
    IsInvolutoryFieldFixedSpace L M B U n

/-- The escape conclusion of 6.1.14(5), allowing the field actor in M.
Its proof must arrange the source Sylow subgroup inside the actual
normalizer of U. All subgroup normalizations remain relative. -/
def FieldConjugateEscape (L M B Z : Subgroup G) (n : ℕ) : Prop :=
  2 < n → ∀ (g : G) (U : Subgroup G),
    U ≠ ⊥ → ChapterE.subgroupCorank B U = n →
    IsInvolutoryFieldFixedSpace L M B U n →
    B.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) →
    B ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G) →
    ¬ B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G) →
    ¬ centralizer (Z : Set G) ≤ M

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
