module
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.NoncentralStructure
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
/-!
# Source nonsolvable uniqueness from Theorems A and C

The genuine source model theorem supplies outer solvability and even order
for the component quotients. A.3.12 then gives unique containment, and the
proved noncentral branch gives the orbit bound. These discharge every
earlier input of 1.2.7 except the genuine Theorems A and C themselves.
The literal Sylow, local component and conjugate closure are preserved.

Source: Aschbacher–Smith A.3.7–12 and 1.2.7, printed pp.45–48, 506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u

/-- Source A.3.12 containment from genuine A and C, with no ordinary-cover
or full embedding-catalogue hypothesis. -/
theorem containment_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (X : Type u) [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hcore : pCore 2 X = ⊥)
    (T : Sylow 2 X) (B : Subgroup X)
    (hB : B ∈ ChapterA.Section03.localCComponents T) :
    ∃! L : Subgroup X, L.IsCComponent ∧ B ≤ L :=
  ChapterA.Section03.SourceComponents.containment hA
    (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC hC)
    hX hcore T B hB

/-- All four source 1.2.7 conclusions from genuine Theorems A and C.
The noncentral structural, orbit and characteristic-two inputs are proved. -/
theorem nonsolvable_uniqueness_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G)) :
    NonsolvableUniquenessConclusion T L :=
  nonsolvable_uniqueness_of_noncentral_structure
    (containment_of_theoremsAC hA hC)
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    hG T hL
end CFSG.Quasithin.Chapter1.Section02
