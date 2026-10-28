module
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Cubic rank of the split G₂ Borel in even binary degree

The explicit two-parameter torus embeds in the positive-root Borel.
If the binary field degree is even, each parameter has a nontrivial
cubic subgroup, so the Borel has three-rank at least two. Inner Sylow
conjugacy transports this to any specified Sylow normalizer.

Source application: Aschbacher--Smith 14.6.20, printed p.1037. The terminal
component sieve uses this bound against the actual M-intersection image.
The torus and Sylow normalizer come from the attributed octonion model;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2
variable {F : Type*} [Field F] [Finite F]

/-- Two independent cubic torus parameters lie in the actual Borel. -/
theorem two_le_borel_threeRank_of_even_degree {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (he : Even n) :
    2 ≤ primeRank 3 (borel (K := F)) := by
  have hr : 1 ≤ primeRank 3 Fˣ := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    apply PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [Nat.card_units,hF]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he
  have hp : 2 ≤ primeRank 3 (Fˣ × Fˣ) := by
    rw [primeRank_prod_eq_add]
    omega
  have ht : 2 ≤ primeRank 3 (splitTorus (K := F)) := by
    rwa [←primeRank_equiv 3 torusParameterEquiv]
  exact ht.trans (primeRank_le_of_injective 3
    (inclusion (show splitTorus (K := F) ≤ borel from le_sup_right)) (inclusion_injective _))

/-- The same lower bound on the normalizer of any chosen Sylow subgroup. -/
theorem two_le_sylow_normalizer_threeRank_of_even_degree [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (he : Even n) (P : Sylow 2 (Model F)) :
    2 ≤ primeRank 3 (normalizer (P : Set (Model F))) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) P (LieParabolicSetup.sylow (F := F))
  have hm : (P : Subgroup (Model F)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  have hn : (normalizer (P : Set (Model F))).map (MulAut.conj g).toMonoidHom = borel := by
    change (normalizer ((P : Subgroup (Model F)) : Set (Model F))).map _ = _
    rw [map_equiv_normalizer_eq,hm,SylowNormalizer.normalizer_unipotent]
  let e := ((MulAut.conj g).subgroupMap (normalizer (P : Set (Model F)))).trans
    (MulEquiv.subgroupCongr hn)
  rw [primeRank_equiv 3 e]
  exact two_le_borel_threeRank_of_even_degree hF he
end Atlas.G2
