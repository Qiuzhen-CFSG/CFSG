module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.ExceptionalSeven

/-!
# Source small-model actions in Lemma 13.6.22

This extension supplies concrete natural-module fixed-space calculations
and their transport through the actual conjugation and checked quotients.
The shared endpoint below applies B.2.14's centralizing supplement and
lifts fixation through ⟨v⟩. It is the application needed by the source
noncentrality contradiction, with the same Lᵥ, K, U and a throughout.

This is not yet the complete Lemma 13.6.22. Constructing the source markings,
the covered-A₆ and ordinary-A₇ reductions, all exceptional-A₇ actors, and
the A₆/G₂(2)′ cases remains with the family producers. The source assembly
also has to construct the B.2.14 supplement and the earlier conjugate a.
Legacy `SmallSourceCase` is preserved separately: in particular its Sp₄(4)
predicate cannot stand for the printed Sp₄(2)′ case.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.932–933.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels

/-- The ambient model calculation feeds the literal checked-quotient endgame.
The supplement is the remaining B.2.14 input, not a field of a case tag. -/
theorem centralizes_of_ambient_centralizer_eq
    {G : Type*} [Group G] [Finite G]
    (L K U : Subgroup G) (v : G) (a : Gv v) (F : Subgroup (Gcheck v))
    [IsMulCommutative F]
    (hK : K ≤ Gv v) (hpK : IsPPerfect 2 K) (hv : v ^ 2 = 1)
    (hLK : Lv L v ≤ K)
    (ha : (a : G) ∈ centralizer (Lv L v : Set G))
    (haF : checkedQuotientMap v a ∈ F)
    (hsplit : F = checkedImage v U ⊔ (F ⊓ centralizer (checkedImage v K : Set (Gcheck v))))
    (hfix : U ⊓ centralizer (Lv L v : Set G) = U ⊓ centralizer (K : Set G)) :
    K ≤ Gv (a : G) :=
  Source.centralizes_of_checked_fixed_space_comparison L K U v a F hK hpK hv hLK
    ha haF hsplit (checked_centralizer_eq_of_ambient L K U v hLK hv hfix)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
