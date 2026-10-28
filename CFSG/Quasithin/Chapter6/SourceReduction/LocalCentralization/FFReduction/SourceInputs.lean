module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.Preparation
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# Earlier source inputs to the local Cartan FF argument

The source uses two independent results before applying the FF classification:
exceptional component quotients survive maximal local enlargement, and the
rank-one Baumann normalizer lies in N_G(L). The former is the indicated
specialization of A.3.12 and 1.2.8; the latter is 5.1.7(1).

These declarations specify missing earlier implications. They do not assert
them, and neither contains the A₇ module classification as an assumption.
The FF reduction owner must discharge both in its final source assembly.

Source: Aschbacher--Smith, 1.2.8, pp.506--507, and 5.1.7, pp.633--634;
application in 5.1.13, p.637.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u

/-- The three literal quotients already present in the local Cartan witness. -/
abbrev LocalExceptionalQuotient {G : Type u} [Group G] (X : Subgroup G) : Prop :=
  Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)) ∨
    Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
    Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)

/-- Only the exceptional rows of the earlier local embedding theorem are needed. -/
def ExceptionalLocalOvercomponentModels (G : Type u) [Group G] [Finite G] : Prop :=
  IsSimpleQTKE KnownSimple.IsKnownSimple G →
    ∀ (T : Sylow 2 G) (X K : Subgroup G),
      X ∈ Chapter1.L G (T : Subgroup G) →
      (T : Subgroup G) ≤ normalizer (X : Set G) →
      K ∈ Chapter1.LStar G (T : Subgroup G) → X ≤ K →
      LocalExceptionalQuotient X → LocalExceptionalQuotient K

/-- The original rank-one 5.1.7(1), retaining the initial reduced module. -/
def RankOneBaumannNormalizerControl (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
    Input KnownSimple.IsKnownSimple T L W n →
      normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
