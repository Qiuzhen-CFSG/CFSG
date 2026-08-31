module

public import GorensteinWalter.Section3.Basic
public import GorensteinWalter.Section4.Basic

/-!
# The Gorenstein--Walter theorem

The preceding files split Bender's proof into the classification layer and
Sections 2, 3, and 4.  This file contains only the final contradiction and
the theorem assembly.
-/

noncomputable section

namespace GorensteinWalter

universe u

/-! ## Final assembly -/

/-- The two alternatives of Theorem 2.10 are both impossible. -/
public theorem no_minimalCounterexample
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    False := by
  obtain ⟨c⟩ := exists_centralizerSetup hmin
  rcases theorem_2_10 hmin c with hfirst | hsecond
  · exact firstCase_impossible hmin c hfirst
  · exact secondCase_impossible hmin c hsecond

/-- **Gorenstein--Walter theorem.** Every finite group with dihedral Sylow
`2`-subgroups is a `D`-group. -/
public theorem gorensteinWalter : gorensteinWalterStatement.{u} := by
  by_contra h
  obtain ⟨G, hG, hfin, hmin⟩ := exists_minimalCounterexample h
  let : Group G := hG
  let : Finite G := hfin
  exact no_minimalCounterexample hmin

/-- Snake-case alias for the main theorem. -/
public theorem gorenstein_walter : gorensteinWalterStatement.{u} :=
  gorensteinWalter

end GorensteinWalter
