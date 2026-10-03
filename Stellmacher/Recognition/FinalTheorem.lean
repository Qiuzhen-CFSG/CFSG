module

public import Stellmacher.Recognition.ClassificationOfOddCore
public import Stellmacher.Recognition.OddCoreRecognitionOfLyons
public import Stellmacher.Recognition.LyonsU3Four.TableIProducerOfMultiplicity
public import Stellmacher.Recognition.LyonsU3Four.TableISparseOppositeMultiplicityFactored

/-!
# The simple N₂ and N classifications

Every finite nonsolvable simple N₂ group is isomorphic to a concrete model in
`IsNTwoGroupModel`. Thompson's all-prime N condition excludes the additional
even-field unitary family, leaving `IsNGroupModel`, including the Tits group.

The exact sparse-opposite multiplicity classification completes Lyons's
character calculation and proves odd-core vanishing in the Lyons Sylow case.
The odd-core recognition theorem then closes the global branch of the terminal
reduction. The remaining local branches use the completed Fong and Parrott
recognition theorems. All intermediate hypotheses are discharged here.

Sources: Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable, VI* (1974), p. 573 (the Tits correction); Kurzweil–Stellmacher,
Appendix p. 370 (the N and N₂ catalogues); Lyons, *A Characterization of the
Group U₃(4)* (1972), pp. 374–386. Detailed local sources are recorded in the
imported recognition modules.
-/

namespace Stellmacher
universe u

/-- The generalized N₂ classification for finite nonsolvable simple groups,
with actual isomorphisms to the catalogue models. -/
public theorem nTwo_classification
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) :
    IsNTwoGroupModel G := by
  apply Recognition.isNTwoGroupModel_of_oddCore' hns hN
  intro t ht hbad
  apply Recognition.isNTwoGroupModel_of_nontrivial_oddCore_of_lyons hns hN
    (t := t) (ht := ht) (hbad := hbad)
  intro S hs x hx
  exact Recognition.LyonsU3Four.involutionCentralizer_oddCore_eq_bot_of_opposite_counts
    hN S hs Recognition.LyonsU3Four.SparseOppositeRows.classify_factored hx

/-- Thompson's corrected N classification for finite nonsolvable simple groups,
including the Tits group and excluding the extra even-field unitary family. -/
public theorem n_classification
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNGroup G) :
    IsNGroupModel G :=
  Recognition.isNGroupModel_of_isNTwoGroupModel hN
    (nTwo_classification hns (isNTwoGroup_of_isNGroup hN))

end Stellmacher
