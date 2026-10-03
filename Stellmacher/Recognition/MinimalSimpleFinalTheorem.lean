module

public import Stellmacher.Recognition.MinimalSimpleModelFilter
public import Stellmacher.Recognition.MinimalSimpleConverse
public import Stellmacher.Recognition.ClassificationOfOddCore
public import Stellmacher.Recognition.OddCoreRecognitionOfLyons
public import Stellmacher.Recognition.LyonsU3Four.TableIProducerOfMultiplicity
public import Stellmacher.Recognition.LyonsU3Four.TableISparseOppositeMultiplicityFactored

/-!
# Thompson's classification of finite minimal simple groups

A finite group is nonabelian minimal simple if and only if it is isomorphic
to one of the five models in `ThompsonMinimalSimpleModel`: PSL₂(2^p) for p
prime, PSL₂(3^p) for p an odd prime, PSL₂(p) for p > 3 prime with residue
two or three modulo five, Sz(2^p) for p an odd prime, or PSL₃(3).

Minimal simplicity supplies nonsolvable simplicity and the N₂ condition.
The proved sparse-opposite multiplicity classifier completes the Lyons
character argument. Its odd-core vanishing endpoint discharges the remaining
input to odd-core recognition, which in turn completes the terminal N₂
classification. The minimal-simple model filter then imposes exactly the
five-family restrictions. The converse transports the five model theorems
along their actual multiplicative equivalences.

Source: J. G. Thompson, *Nonsolvable finite groups all of whose local subgroups
are solvable*, I, Bull. Amer. Math. Soc. 74 (1968), Corollary 1, p. 388.
See `docs/thompson-minimal-simple-source-contract.md` and the source notes in
the imported recognition, parameter, and converse modules.
-/

namespace Stellmacher.Recognition

/-- Thompson's five-family classification, with exact parameter restrictions
and actual isomorphisms, in both directions. -/
public theorem isMinimalSimple_iff_thompsonModel
    {G : Type*} [Group G] [Finite G] :
    IsMinimalSimple G ↔ ThompsonMinimalSimpleModel G := by
  constructor
  · intro hG
    let : IsSimpleGroup G := hG.isSimpleGroup
    apply thompsonMinimalSimpleModel_of_isNTwoGroupModel hG
    apply isNTwoGroupModel_of_oddCore' hG.not_isSolvable hG.isNTwoGroup
    apply isNTwoGroupModel_of_nontrivial_oddCore_of_lyons
      hG.not_isSolvable hG.isNTwoGroup
    intro S hs t ht
    exact LyonsU3Four.involutionCentralizer_oddCore_eq_bot_of_opposite_counts
      hG.isNTwoGroup S hs LyonsU3Four.SparseOppositeRows.classify_factored ht
  · exact ThompsonMinimalSimpleModel.isMinimalSimple

end Stellmacher.Recognition
