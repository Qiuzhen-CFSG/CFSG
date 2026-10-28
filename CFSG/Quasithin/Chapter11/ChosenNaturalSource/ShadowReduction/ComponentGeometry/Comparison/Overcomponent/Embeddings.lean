module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements

/-!
# The proper-embedding target on printed p.776

These predicates specify the complete shortlist obtained by comparing
11.1.1 with A.3.12. They do not assert that this comparison has been proved.
In particular both odd linear/unitary rows and both odd-kernel extension
rows are retained. Covers are actual central covers of the stated groups.

The nilpotent row records the radical supplement supplied by the embedding
in A.3.12(21), not merely two unrelated abstract quotient models. The
reduced-module argument in Setup then excludes this row using the shared
maximal-local radical-centralization implication. Establishing the
shortlist from the full preceding alternatives remains a separate proof.
Source: Aschbacher--Smith, 11.4.2, printed p.776, and A.3.12, pp.47--48.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The six proper pairs whose larger two-core quotient is quasisimple.
Every occurrence refers to the literal quotient of the indicated subgroup. -/
inductive QuasisimplePair (B J : Subgroup G) : Prop where
  | linearFourMathieu
      (small : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 4)
      (large : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23))
  | alternatingMathieu
      (small : IsAlternating (B ⧸ pCore 2 B) 7)
      (large : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23))
  | primeLinear (p : ℕ) (prime : p.Prime) (bound : 11 ≤ p) (unitary : Bool)
      (small : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 p)
      (large : IsPSLSign (J ⧸ pCore 2 J) unitary 3 p ∨
        IsSLSign (J ⧸ pCore 2 J) unitary 3 p)
  | elementaryLinear (p : ℕ) (prime : p.Prime) (bound : 5 ≤ p)
      (small : HasExtension (B ⧸ pCore 2 B) (ElementaryModel p 2)
        (fun Q _ => Source.IsSL Q 2 p))
      (large : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 p ∨
        Source.IsSL (J ⧸ pCore 2 J) 3 p)
  | mathieu
      (small : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M22))
      (large : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23))
  | mathieuCoverJanko
      (small : IsM22Cover (B ⧸ pCore 2 B))
      (large : Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model))

/-- The nilpotent odd-by-SL₂(5) model; no splitting or exponent bound is imposed. -/
def NilpotentFiveExtension (A : Type*) [Group A] : Prop :=
  HasExtension A (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
    (fun Q _ => Source.IsSL Q 2 5)

/-- The full proper-overcomponent output, including the actual supplement
in the nonquasisimple row. This is an output contract, not an assumed
universal classification theorem. -/
inductive ProperEmbedding (B J : Subgroup G) : Prop where
  | quasisimple (pair : QuasisimplePair B J) (quasisimple : IsQuasisimple (J ⧸ pCore 2 J))
  | nilpotent
      (small : NilpotentFiveExtension (B ⧸ pCore 2 B))
      (large : NilpotentFiveExtension (J ⧸ pCore 2 J))
      (nonquasisimple : ¬ IsQuasisimple (J ⧸ pCore 2 J))
      (supplement : J = B ⊔ radicalIn J)

/-- Once the full embedding comparison is proved, the actual radical
centralization excludes its nilpotent row and supplies the genuine FSU
for the remaining six pairs. No FF assertion follows from this theorem. -/
theorem quasisimple_setup_of_embedding (h : EarlierGeometry E)
    (hrad : MaximalRadicalCentralization T) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hlt : E.Kz < J)
    (hemb : ProperEmbedding E.Kz J) :
    QuasisimplePair E.Kz J ∧ IsQuasisimple (J ⧸ pCore 2 J) ∧
      ChapterA.Section04.IsFaithfulSignalizerType J ∧
      Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T J) := by
  cases hemb with
  | quasisimple hp hq =>
    exact ⟨hp, hq, faithful h hJ.1 hlt, exists_fundamentalSetup h hJ hlt hq⟩
  | nilpotent _ _ hn hs =>
    exact (not_radical_supplement h hrad hJ hlt hn hs).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent
