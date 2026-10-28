module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Commutator
public import Theory.GroupTheory.PrimeRankZero

/-!
# Interface for selecting an outside component from B.5.6

The candidate records a genuine C-component of `J(I)` with its actual star
image. The classification must supply that image's quasisimplicity and
trivial three-prime core. These are intermediate conclusions to be proved,
not assumptions added to `LocalData` or a statement of B.5.6 itself.

The star homomorphism is the restriction of `I → I/C_I(U_I)`. Vanishing
three-prime core and quasisimplicity imply positive three-rank in its image;
Cauchy's theorem and divisibility lift positivity to `L`. The three-prime
core of `L` maps trivially, hence lies in the literal action centralizer.
This isolates the input to the source's two-core quotient argument.

No component is constructed in this module. The B.5.6 selection remains a
proof obligation. `CoreQuotient` subsequently proves quasisimplicity of
`L/O₂(L)` conditional on the genuine universal A.3.6 theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6,
printed p.105, and 15.3.15(2)/26(2), printed pp.1125 and 1130.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup
variable {G : Type*} [Group G]

/-- The output to be derived from the actual B.5.6 alternatives. This is a
partial result, not an assumption in the source setup. In particular the
two-core quotient and the commutator identity have not been asserted. -/
structure StarComponentCandidate (d : LocalData G) (I : Subgroup G) where
  L : Subgroup G
  le_thompson : L ≤ Stellmacher.elementaryAbelianMaxJ I
  component : (L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I)).IsCComponent
  outside : ¬ L ≤ d.M
  star_quasisimple : Theory.GroupTheory.IsQuasisimple (d.starImage I L)
  star_threePrimeCore : pPrimeCore 3 (d.starImage I L) = ⊥

namespace LocalData
variable (d : LocalData G)

/-- The actual map from an ambient subgroup into its star image. -/
noncomputable def componentStarMap {I L : Subgroup G} (hLI : L ≤ I) :
    L →* d.starImage I L :=
  ((d.starMap I).subgroupMap (L.subgroupOf I)).comp
    (subgroupOfEquivOfLe hLI).symm.toMonoidHom

theorem componentStarMap_surjective {I L : Subgroup G} (hLI : L ≤ I) :
    Function.Surjective (d.componentStarMap hLI) :=
  ((d.starMap I).subgroupMap_surjective (L.subgroupOf I)).comp
    (subgroupOfEquivOfLe hLI).symm.surjective

theorem componentStarMap_apply {I L : Subgroup G} (hLI : L ≤ I) (l : L) :
    (d.componentStarMap hLI l : d.Star I) = d.starMap I ⟨l, hLI l.property⟩ := rfl

end LocalData

private theorem threePrimeCore_le_ker [Finite G] {H : Type*} [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hcore : pPrimeCore 3 H = ⊥) :
    pPrimeCore 3 G ≤ f.ker := by
  have hm : (pPrimeCore 3 G).map f ≤ pPrimeCore 3 H := by
    apply le_sSup
    refine ⟨(inferInstance : (pPrimeCore 3 G).Normal).map f hf, ?_⟩
    exact Nat.Coprime.of_dvd_right (card_map_dvd _ f) pPrimeCore_coprime_card
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp (hm.trans_eq hcore))

private theorem threeRank_pos [Finite G] [Theory.GroupTheory.IsQuasisimple G]
    (hcore : pPrimeCore 3 G = ⊥) : 1 ≤ primeRank 3 G := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : IsSimpleGroup (G ⧸ center G) := Theory.GroupTheory.IsQuasisimple.simple
  let _ : Nontrivial G := (QuotientGroup.mk'_surjective (center G)).nontrivial
  by_contra h
  have hz : primeRank 3 G = 0 := by omega
  have hcop : Nat.Coprime 3 (Nat.card G) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)
  have htop : (⊤ : Subgroup G) ≤ pPrimeCore 3 G :=
    le_sSup ⟨inferInstance, by simpa using hcop⟩
  have he : (⊤ : Subgroup G) = ⊥ := le_bot_iff.mp (htop.trans_eq hcore)
  exact top_ne_bot he

namespace StarComponentCandidate
variable [Finite G] {d : LocalData G} {I : Subgroup G} (c : StarComponentCandidate d I)

omit [Finite G] in
theorem le_overgroup : c.L ≤ I := c.le_thompson.trans (sSup_le fun _ hA => hA.1)

omit [Finite G] in
/-- The selected C-component already makes the overgroup nonsolvable;
its two-core quotient is not needed for this conclusion. -/
theorem not_isSolvable (c : StarComponentCandidate d I) : ¬ Group.IsSolvable I := by
  intro hI
  let _ := hI
  have hJI : Stellmacher.elementaryAbelianMaxJ I ≤ I := sSup_le fun _ hA => hA.1
  let _ : Group.IsSolvable (Stellmacher.elementaryAbelianMaxJ I) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hJI)
  exact c.component.not_isSolvable inferInstance

/-- Positive three-rank is lifted through the actual star homomorphism;
no equality of the two three-ranks is asserted. -/
theorem rank_pos : 1 ≤ primeRank 3 c.L := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := c.star_quasisimple
  have hp := threeRank_pos c.star_threePrimeCore
  by_contra h
  have hz : primeRank 3 c.L = 0 := by omega
  have hz' := PrimeRank.eq_zero_of_surjective (d.componentStarMap c.le_overgroup)
    (d.componentStarMap_surjective c.le_overgroup) hz
  omega

/-- The three-prime core is in the literal action kernel, as used in the
last part of the proof of 15.3.15(2). -/
theorem threePrimeCore_le_actionKernel :
    (pPrimeCore 3 c.L).map c.L.subtype ≤ I ⊓ centralizer (d.UI I : Set G) := by
  have hker := threePrimeCore_le_ker (d.componentStarMap c.le_overgroup)
    (d.componentStarMap_surjective c.le_overgroup) c.star_threePrimeCore
  rintro x ⟨l, hl, rfl⟩
  refine ⟨c.le_overgroup l.property, ?_⟩
  have he : d.componentStarMap c.le_overgroup l = 1 := hker hl
  have he' := congrArg Subtype.val he
  change d.starMap I ⟨l, c.le_overgroup l.property⟩ = 1 at he'
  have hk : (⟨l, c.le_overgroup l.property⟩ : I) ∈ localActionKernel d.Z I :=
    (QuotientGroup.eq_one_iff _).mp he'
  exact hk

end StarComponentCandidate
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
end
