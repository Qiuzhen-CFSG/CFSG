module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Realization
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Checked
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Shape
public import Theory.GroupTheory.GeneratorCosetCoverFiniteIndex

/-!
# The 3125-coset bound for Gebhardt's parabolic

A checked Todd–Coxeter trace, using only the first nine literal relations,
gives 3125 representatives for `⟨a,b⟩` inside `⟨a,b,c⟩`. Each signed generator
transition carries an actual subgroup witness. Word induction therefore gives
a surjection onto the coset quotient, proving both finiteness of the quotient
and the upper bound. No order or finiteness assumption on either subgroup is
used. The producer and reproducible certificate are retained in
`GebhardtParabolicIndexCertificate/source/`.

Source: V. Gebhardt, "Two Short Presentations for Lyons' Sporadic Simple Group",
Experimental Mathematics 9 (2000), 333–338, Section 3B.
-/

namespace Lyons.Gebhardt
open Subgroup.CosetWordCertificate ParabolicIndexCertificate

/-- A cover by actual coset equations in the parabolic of the fixed presentation. -/
public def localTowerParabolicCosetCover :
    Subgroup.GeneratorCosetCover (LocalTower.base.subgroupOf LocalTower.parabolic)
      localGenerator (Fin 3125) := by
  have hall := all_hold valid
  have hinit : definitions.repr localGenerator (survivor (0 : Fin 3125)) = 1 := by
    have hs : survivor (0 : Fin 3125) = 0 := by decide +kernel
    rw [hs]
    exact definitions.repr_zero _
  exact coverOfFacts facts survivor 0 hinit dest output hshape
    (by intro i a; exact hall (output i a) (hlt i a))

/-- The base has positive relative index at most 3125 in the parabolic. -/
public theorem localTowerParabolic_relIndex_bounds :
    0 < LocalTower.base.relIndex LocalTower.parabolic ∧
      LocalTower.base.relIndex LocalTower.parabolic ≤ 3125 := by
  constructor
  · exact localTowerParabolicCosetCover.index_pos localGenerator_generates
  · change (LocalTower.base.subgroupOf LocalTower.parabolic).index ≤ 3125
    simpa only [Nat.card_fin] using
      localTowerParabolicCosetCover.index_le_card localGenerator_generates

end Lyons.Gebhardt
