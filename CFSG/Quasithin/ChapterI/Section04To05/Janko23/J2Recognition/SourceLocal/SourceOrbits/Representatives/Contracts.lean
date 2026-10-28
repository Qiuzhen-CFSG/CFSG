module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.RootFixer

/-!
# The two independent local constructions in 47.5

The five-local A₅ construction supplies both an A₄ pair and an A₅ pair.
The first retains its root-normalizer coordinates, from which `RootFixer`
proves the fixer and involution statements. The second requires its
literal C₂ × D₁₀ fixer. Independently, the original involution centralizer
supplies an SL₂(3) pair with an actual Sylow two stabilizer.

These records are outputs still to be constructed from the genuine earlier
47.1–47.3 conclusions. They are not additional hypotheses of those source
theorems, and their declarations do not assert that they are inhabited.
The assembly module combines them and applies the existing suborbit
completion, without repeating its counting argument.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5, printed p.263.
-/

@[expose] public section
open Subgroup MulAction
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives
variable {G : Type*} [Group G] [Finite G]

/-- Output of the five-local construction, including the compatible root marking. -/
structure FiveLocalPairs (D : Seed G) where
  edge : D.Vertex
  root : RootPairCoordinates D edge
  five : D.Vertex
  five_join : a5Join D D.base five
  five_fixer : Nonempty (edgeFixer G D.base five ≃*
    (Multiplicative (ZMod 2) × DihedralGroup 5))

/-- Output of the construction inside the original involution centralizer. -/
structure SL23Pair (D : Seed G) where
  vertex : D.Vertex
  join : sl2Join D D.base vertex
  sylow : ∃ P : Sylow 2 (normalizer (D.X : Set G)),
    (P : Subgroup (normalizer (D.X : Set G))) =
      stabilizer (normalizer (D.X : Set G)) vertex

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives
