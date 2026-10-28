module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.PairSplitting
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks

/-!
# Pair sections as an input to torus normalization

This is the assembly boundary for the additive local calculation.  The four
quartet sections remain an explicit premise supplied by the independent
nonabelian branch.
-/

public section
noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary.PairSplitting

open ReeF4
open ReeF4.ElementaryTwoBound

theorem exists_torusEquivariant_of_quartet_sections (m : ℕ) (hm : 1 ≤ m)
    {E : Type*} [Group E] [Finite E]
    (d : PerfectCentralCovering.Cover E (Model m))
    (hd : Nat.card d.toMonoidHom.ker = 2)
    (hq : ∀ j : Fin 4, ∃ s : X m (rootIndex (.inr j)) →* E,
      d.toMonoidHom.comp s = (X m (rootIndex (.inr j))).subtype) :
    ∃ L : BlockSections m d.toMonoidHom, L.TorusEquivariant := by
  apply exists_torusEquivariant_of_pair_and_quartet_sections m d hd
  · exact exists_pair_sections m hm d hd
  · exact hq

end ReeF4.CentralCovers.TwoPrimary.PairSplitting
