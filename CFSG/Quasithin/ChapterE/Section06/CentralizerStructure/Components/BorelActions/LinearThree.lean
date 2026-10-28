module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearThree.Centers
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearThree.OrdinaryComplement
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearThree.CoverComplement

/-!
# PSL₃ Borel calculations for E.6.11

The ordinary PSL₃(2ⁿ) witness combines the matrix torus complement with the
identification of the displacement as the marked Sylow center. For every
central two-cover of PSL₃(4), Schur–Zassenhaus gives the cyclic complement,
and the quotient Sylow-center calculation bounds the center by the two-core
and the displacement. Both constructions refer to the actual embedded
subgroups and require no maximality of U or ambient normality of L.

These witnesses discharge the two linear-three model obligations in the
Borel case. Binary Singer regularity and the common deductions remain in
the separate final assembly of the torus action.

Source: Aschbacher–Smith, E.6.8(1) and E.6.11, printed pp.247–250.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}

/-- The cyclic complement and Sylow-center bound for the ordinary PSL₃(2ⁿ)
branch of E.6.8(1), supplying its model witness for E.6.11. -/
theorem modelWitness_linear_three
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    ModelWitness M V Q L n := by
  refine ⟨exists_complement_linear_three h hU hL b hn hVL hQ S hS iso, ?_⟩
  rw [center_eq_displacement_linear_three h hU hL b hn hVL hQ S hS iso]
  exact le_sup_right

/-- The cyclic complement and Sylow-center bound for every central two-cover
of PSL₃(4), with no restriction on the size of the covering center. -/
theorem modelWitness_linear_three_cover
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hn2 : n = 2) (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    ModelWitness M V Q L n := by
  exact ⟨exists_complement_linear_three_cover h hU hL b hn hVL hQ S hS hn2 hz iso,
    center_le_linear_three_cover h hU hL b hn hVL hQ S hS hn2 hz iso⟩

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
