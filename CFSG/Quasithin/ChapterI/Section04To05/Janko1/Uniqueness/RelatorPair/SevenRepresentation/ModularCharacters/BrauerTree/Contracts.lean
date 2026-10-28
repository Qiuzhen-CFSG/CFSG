module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.TreeData

/-!
# Separate realization contracts for the eleven-block calculation

The ten path edges have distinct proposed dimensions. The four defect-zero
rows have dimensions 77, 77, 77, and 209, so their pairwise inequivalence must
also be established. These contracts ask for actual irreducible modules over
`ElevenClosure`; they do not assert existence or certify a block calculation.

The consumer `BrauerTree.treeFamily_of_modules` combines these two families,
proves their natural dimension equations, and proves completeness from the
fourteen eleven-regular classes of `OrdinaryData`. In particular, the realization
producers need no additional completeness hypothesis.

The row and edge ordering is specified in `../Source.md`, from the ATLAS/GAP
Brauer table. The arbitrary-source-group realization argument is Janko,
J. Algebra 3 (1966), 147–186, as described in Gorenstein §16.6, p.482.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

/-- Proposed edge dimensions along `0–8–12–10–11–3–2–4–13–9–1`. -/
@[expose] public def pathDegree : Fin 10 → ℕ :=
  ![1, 119, 14, 106, 27, 49, 7, 69, 64, 56]

/-- Dimensions of the four ordinary rows `5,6,7,14`. -/
@[expose] public def defectZeroDegree : Fin 4 → ℕ := ![77, 77, 77, 209]

/-- The actual simple modules required from the path calculation. -/
public structure PathModules (G : Type*) [Group G] where
  rep : ∀ i, Representation ElevenClosure G (Fin (pathDegree i) → ElevenClosure)
  irreducible : ∀ i, Representation.IsIrreducible (rep i)

/-- The actual simple modules required from the defect-zero reduction argument.
The three degree-77 modules must be distinct up to genuine equivalence. -/
public structure DefectZeroModules (G : Type*) [Group G] where
  rep : ∀ i, Representation ElevenClosure G (Fin (defectZeroDegree i) → ElevenClosure)
  irreducible : ∀ i, Representation.IsIrreducible (rep i)
  inequivalent : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j))

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree
