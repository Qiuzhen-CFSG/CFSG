module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Stem
public import Theory.Character.ModularBlock.PrimeCongruence
public import Theory.Representation.CyclicDefect.RealLine

/-!
# Principal block identification and projective-edge obligations

The first interface identifies the actual ordinary congruence block at a prime
above eleven, retaining its exact correspondence with the supplied ordinary
characters. The second asks for projective modules affording the adjacent sums
of an existing stem. Neither interface has an existence instance.

These separate the ordinary block calculation from Feit's cyclic-defect
module construction (VII.2, VII.6, VII.9) and from projective reciprocity.
Final construction, including discharge of both obligations, belongs to
`Construction.lean`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open ModularBlock.PrimeBlockConstruction

/-- Identify the exact ordinary principal block by reduction of central characters. -/
public structure PrincipalBlockIdentification {G : Type*} [Group G] [Finite G]
    (d : OrdinaryData G) where
  data : PrimeCongruenceBlockData 11 G
  rows : Fin 15 ≃ data.I
  characters : ∀ i, data.chi (rows i) = d.chi i
  principal : rows 0 = data.principal
  membership : ∀ i, rows i ∈ data.block ↔ ¬ 11 ∣ ordinaryDegree i

/-- Genuine projective modules, rather than numerical adjacent sums alone. -/
@[expose] public def ProjectiveEdges {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}
    (s : RealStem G d) : Type _ :=
  ∀ k : Fin 10, Representation.CyclicDefect.ProjectiveCharacterLift 11 s.roots
    (fun g => d.chi (s.row k.castSucc) (ConjClasses.mk g) +
      d.chi (s.row k.succ) (ConjClasses.mk g))

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
