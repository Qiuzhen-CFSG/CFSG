module

public import Glauberman.SuzukiCharacterization.CharacterSelectionCore
public import Glauberman.SuzukiCharacterization.RestrictionDegreeLowerBound

/-!
# Selection of a character with zero Sylow fixed space

Proposition 2.3 supplies a central involution and a nonprincipal linear
character whose kernel contains the required commutator support. The weighted
principal-block column identity and column norm select a row of small degree.
The restriction-degree lower bound forces its principal restriction
multiplicity to vanish, hence its sum over the Sylow subgroup is zero.

The conditional selection API is re-exported from `CharacterSelectionCore`.
The theorem below discharges all its inputs from the group hypotheses.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Proposition 2.3, Lemma 4.1 and equations (4.1)–(4.7), ending on p. 90, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Glauberman.SuzukiCharacterization

/-- Under the Suzuki characterization hypotheses, some principal-block
irreducible character has no Sylow fixed vectors, expressed by its zero sum. -/
public theorem Hypotheses.exists_principalBlock_zero_sylow_sum
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) :
    ∃ i ∈ d.block, ∑ x : P, d.chi i (ConjClasses.mk (x : G)) = 0 := by
  obtain ⟨s⟩ := h.nonempty_commutatorSupportData P
  exact CharacterSelection.exists_zero_sum P h d s

end Glauberman.SuzukiCharacterization
