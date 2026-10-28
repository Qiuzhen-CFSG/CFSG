module

public import CFSG.Quasithin.Chapter12.Section08.Setup.SourceData
public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.TINormalizerControl

/-!
# The source normalizers in the higher-rank setup

The structural implication of 12.2.2 normalizes L by T. Its T-orbit is
therefore L itself, so the full universal 1.2.7 implication identifies the
unique maximal two-local over LT with N_G(L). The nonzero elementary
chosen V is normal in LT; its normalizer is two-local, hence lies in that
unique overgroup. TI then gives Mᵢ ≤ M_V for every nonzero flag term.

This avoids the unrelated local analysis in 12.2.7–12. These conclusions
are the literal normalizer inputs used by LocalKernel and NormalL1.
Source: Aschbacher–Smith, pp.506, 795–797 and 849–850.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08
open Section02 InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

namespace HigherRankHypothesis
variable (h : HigherRankHypothesis K T L V n)
variable (structural : Structural1222 K) (uniqueness : Uniqueness127 K)
include h structural

theorem sylow_normalizes : (T : Subgroup G) ≤ normalizer (L : Set G) :=
  (structural G T L h.source).1

theorem sylow_normalizes_seed : (T : Subgroup G) ≤ normalizer (V : Set G) :=
  ((structural G T L h.source).2.2 V h.chosen).1

theorem seed_reduced : IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) :=
  ((structural G T L h.source).2.2 V h.chosen).2.1

theorem seed_TI : ∀ g ∈ normalizer (L : Set G),
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V :=
  ((structural G T L h.source).2.2 V h.chosen).2.2.1

/-- T-normalization collapses the actual orbit appearing in 1.2.7. -/
theorem orbit_eq : componentOrbit L (T : Subgroup G) = L := by
  apply le_antisymm _ (le_componentOrbit L _)
  exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
    (h.sylow_normalizes structural)

/-- The source M = N_G(L) is the unique maximal two-local over LT. -/
theorem maximal_unique (uniqueness : Uniqueness127 K) :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} =
        {normalizer (L : Set G)} := by
  have hu := uniqueness G h.source.simpleQTKE T L h.source.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [h.orbit_eq structural] using hu.normalizer_maximal
  refine ⟨hm, Set.ext fun N => ?_⟩
  constructor
  · rintro ⟨hN, hLN⟩
    exact Set.mem_singleton_iff.mpr (by
      simpa only [h.orbit_eq structural] using hu.normalizer_unique N hN hLN)
  · intro hN
    obtain rfl := Set.mem_singleton_iff.mp hN
    exact ⟨hm, sup_le L.le_normalizer (h.sylow_normalizes structural)⟩

/-- The full normalizer of the original V lies in the source M. -/
theorem seed_normalizer_le (uniqueness : Uniqueness127 K) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  let := h.chosen.elementary
  apply normalizer_le_of_unique_maximalTwoLocal
    (J := L ⊔ (T : Subgroup G))
  · intro N hN hJN
    exact Set.mem_singleton_iff.mp ((h.maximal_unique structural uniqueness).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN, hJN⟩)
  · exact IsElementaryAbelian.isPGroup 2 V
  · exact h.chosen.ne_bot
  · exact sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural)

theorem seed_centralizer_le (uniqueness : Uniqueness127 K) :
    centralizer (V : Set G) ≤ normalizer (L : Set G) :=
  (centralizer_le_normalizer _).trans (h.seed_normalizer_le structural uniqueness)

/-- The actual relative seed normalizer is its full ambient normalizer. -/
theorem seedNormalizer_eq (uniqueness : Uniqueness127 K) :
    seedNormalizer (normalizer (L : Set G)) V =
    normalizer (V : Set G) :=
  inf_eq_right.mpr (h.seed_normalizer_le structural uniqueness)

/-- TI controls every nontrivial term, with the source's actual Mᵢ and M_V. -/
theorem flag_normalizer_le (F : InvariantFlag T V n) {i : ℕ}
    (hi : 1 ≤ i) (hin : i ≤ n) :
    F.Mi (normalizer (L : Set G)) i ≤ seedNormalizer (normalizer (L : Set G)) V := by
  have hne : F.Vi i ≠ ⊥ := by
    intro he
    have hc := F.card i hin
    rw [he, Subgroup.card_bot] at hc
    have hp : 1 < 2 ^ i := Nat.one_lt_pow (by omega) (by decide)
    omega
  exact le_inf inf_le_left
    (inf_normalizer_le_of_trivial_intersections (h.seed_TI structural) hne (F.le_seed i))

end HigherRankHypothesis
end CFSG.Quasithin.Chapter12.Section08
