module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateDefs
public import CFSG.Quasithin.ChapterE.Section03.Parameters

/-!
# Local inputs for the corank and fusion arguments

These are the three local mathematical obligations used by the deductions
of 6.1.10(3) and 6.1.11. The first bounds elementary action images; the
second describes actual offenders on the natural module; the third is the
normalizer factorization in 6.1.9(5). None asserts conjugate fusion or the
conjugate corank formula. Their source constructions remain separate from
the deductions, and are required before the source theorems are complete.

Source: Aschbacher--Smith, printed pp.669--670 (PDF pp.686--687).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

/-- The local upper bound on the rank of every elementary action image. -/
def ElementaryActionRankBound (B : Subgroup G) (n : ℕ) : Prop :=
  ∀ A : Subgroup G, IsElementaryAbelian 2 A →
    A ≤ normalizer (B : Set G) →
    ChapterE.subgroupCorank A (A ⊓ centralizer (B : Set G)) ≤ n

/-- Natural offenders fix a conjugate of the distinguished field line.
Inside the specified Sylow, that line is Z and is the entire commutator. -/
def NaturalOffenderFixedLines (T L B Z : Subgroup G)
    [IsElementaryAbelian 2 B] : Prop :=
  ∀ A : Subgroup G, IsElementaryAbelian 2 A →
    A ≤ normalizer (B : Set G) →
    IsOffender (ChapterE.automizerRepresentation B) (ChapterE.inducedAutomizer B A) →
    (∃ l ∈ L, B ⊓ centralizer (A : Set G) = Z.map (MulAut.conj l).toMonoidHom) ∧
    (A ≤ T → B ⊓ centralizer (A : Set G) = Z ∧ ⁅B, A⁆ = Z)

/-- The literal elementwise product in 6.1.9(5), with relative normalizers. -/
def CentralLineNormalizerFactorization (M Z : Subgroup G) : Prop :=
  ∀ d ∈ normalizer (Z : Set G),
    ∃ c ∈ centralizer (Z : Set G), ∃ m ∈ M ⊓ normalizer (Z : Set G), d = c * m

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
