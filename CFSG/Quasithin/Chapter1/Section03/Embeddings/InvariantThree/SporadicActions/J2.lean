module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.LocalCenter
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Seed

/-!
# The J₂ pair-action exclusion under full automorphism coverage

Conjugate the source pair into the fixed ATLAS Sylow candidate and the normalizer
of the second radical candidate. The inverse image of the center of the local
quotient supplies a line in the odd complement. The radical is characteristic
in the fixed Sylow subgroup, so every actual pair automorphism preserves its
normalizer and this line. Surjectivity of `extensionAction` supplies a preimage
of the extending automorphism, so this argument includes outer automorphisms.

`j2_carrierPairExclusion_of_coverage` discharges placement, preservation, and the
intrinsic two-core quotient using the checked ATLAS calculations. The first
centralizer order supplies the Sylow premise of placement. Only full automorphism
coverage remains explicit; its independent standard-generator fusion and orbit
calculations belong to the parent assembly. The more general local-calculation
reduction remains available separately.

The source writes the J₂ configuration as Z₂/(S₃ × Z₃) and explicitly requires
the automorphism case. We keep the inner quotient S₃ × C₃ separate from the
permutation extension and its actual conjugation action. No splitting of the
local group or arbitrary action on a group of the right order is assumed.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of refs/quasithin.pdf); GLS3, Table 5.3g. Concrete words and original
ATLAS attribution are in `ExceptionalParabolics.Seed` and its source directory.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- Relative characteristicity in the chosen Sylow subgroup suffices for the
required preservation by the actual permutation extension. -/
theorem j2_extension_preserves_second_normalizer_of_characteristic
    (hqs : Seed.q₂ ≤ Seed.s) (hchar : (Seed.q₂.subgroupOf Seed.s).Characteristic)
    (z : Extension) (hs : ∀ x, extensionAction z x ∈ Seed.s ↔ x ∈ Seed.s) :
    ∀ x, extensionAction z x ∈ Seed.p₂ ↔ x ∈ Seed.p₂ :=
  J2.normalizer_preserved_of_characteristic hqs hchar (extensionAction z) hs

/-- Conditional assembly using the full extending action, with all remaining
local geometric calculations exposed as hypotheses. -/
theorem j2_carrierPairExclusion_of_local_calculations
    (hcoverage : Function.Surjective extensionAction)
    (hplacement : ∀ (S : Sylow 2 Carrier) (R : Subgroup Carrier), PairInput S R →
      ∃ g : Carrier, (S : Subgroup Carrier).map (MulAut.conj g).toMonoidHom = Seed.s ∧
        R.map (MulAut.conj g).toMonoidHom ≤ Seed.p₂)
    (hstable : ∀ z : Extension,
      (∀ x, extensionAction z x ∈ Seed.s ↔ x ∈ Seed.s) →
      ∀ x, extensionAction z x ∈ Seed.p₂ ↔ x ∈ Seed.p₂)
    (hcore : Nat.card (pCore 2 Seed.p₂) = 64)
    (e : (Seed.p₂ ⧸ pCore 2 Seed.p₂) ≃* J2.LocalQuotient) :
    CarrierPairExclusion ClassificationModels.SporadicName.j2.Carrier := by
  change CarrierPairExclusion Carrier
  intro _ _ _ S R h
  obtain ⟨g, hS, hR⟩ := hplacement S R h
  let f := MulAut.conj g
  apply pairReducible_of_map f (S : Subgroup Carrier) R
  apply J2.pairReducible_of_local_quotient (pairInput_map f h) hR _ hcore e
  intro b hb
  obtain ⟨z, hz⟩ := hcoverage b
  rw [← hz] at hb ⊢
  apply hstable z
  intro x
  have hh := hb x
  change extensionAction z x ∈ (S : Subgroup Carrier).map f.toMonoidHom ↔
    x ∈ (S : Subgroup Carrier).map f.toMonoidHom at hh
  simpa only [f, hS] using hh

/-- The checked local structure supplies a proper nonzero invariant subgroup
for every two-subgroup of the actual J₂ pair automizer. The sole extra premise
is full automorphism coverage, including the outer automorphisms. -/
theorem j2_carrierPairExclusion_of_coverage
    (hcoverage : Function.Surjective extensionAction) :
    CarrierPairExclusion ClassificationModels.SporadicName.j2.Carrier := by
  obtain ⟨hcore, ⟨e⟩⟩ :=
    PairNormalizer.p₂_core_and_quotient SecondParabolic.l₂_core_card
  exact j2_carrierPairExclusion_of_local_calculations hcoverage
    (j2_pair_placement_of_seed_sylow
      ⟨SecondParabolic.sylow FirstParabolic.card_l₁, SecondParabolic.sylow_coe _⟩)
    (j2_extension_preserves_second_normalizer_of_characteristic
      PairNormalizer.q₂_le_s PairNormalizer.q₂_characteristic)
    hcore e

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
