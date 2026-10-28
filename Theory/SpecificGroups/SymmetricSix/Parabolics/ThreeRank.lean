module

public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.PGroupCore

/-!
# Three-rank in proper Sylow-two overgroups of A₆

The complete two-parabolic calculation places every proper overgroup of a
Sylow two-subgroup in a conjugate of a group of order 24. Its Sylow
three-subgroups are therefore cyclic. The bound lifts through a two-core
quotient because the actual quotient map has kernel of order prime to three.

This is the intrinsic A₆ obstruction used in Aschbacher–Smith 15.3.21,
combined manuscript (1 March 2004), printed p.1127.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix

/-- A proper Sylow-two overgroup in A₆ has order dividing 24. -/
theorem proper_sylow_overgroup_card_dvd_twenty_four
    (P : Sylow 2 A6) (K : Subgroup A6)
    (hPK : (P : Subgroup A6) ≤ K) (hK : K ≠ ⊤) :
    Nat.card K ∣ 24 := by
  obtain ⟨M, hM, hKM⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
  obtain ⟨g, _, hg⟩ := a6_coatoms_over_sylow P
  have hcM : Nat.card M = 24 := by
    rcases (hg M).mp ⟨hM, hPK.trans hKM⟩ with rfl | rfl
    · change Nat.card (a6DuadStabilizer.map (MulAut.conj g).toMonoidHom) = 24
      rw [card_map_of_injective (MulAut.conj g).injective, a6DuadStabilizer_order]
    · change Nat.card (a6SynthemeStabilizer.map (MulAut.conj g).toMonoidHom) = 24
      rw [card_map_of_injective (MulAut.conj g).injective, a6SynthemeStabilizer_order]
  exact hcM ▸ card_dvd_of_le hKM

private theorem three_rank_le_one_of_card_dvd_twenty_four
    {H : Type*} [Group H] [Finite H] (hc : Nat.card H ∣ 24) :
    primeRank 3 H ≤ 1 := by
  let P : Sylow 3 H := default
  apply P.primeRank_le_one_of_isCyclic
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hd : 3 ^ n ∣ 24 := hn ▸ ((P : Subgroup H).card_subgroup_dvd_card.trans hc)
  have hsmall : n ≤ 1 := by
    by_contra! h
    have : 9 ∣ 24 := (pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hd
    norm_num at this
  apply isCyclic_of_card_dvd_prime (p := 3)
  rw [hn]
  simpa using pow_dvd_pow 3 hsmall

/-- No proper Sylow-two overgroup in A₆ contains a subgroup of three-rank two. -/
theorem proper_sylow_overgroup_three_rank_le_one
    (P : Sylow 2 A6) (K : Subgroup A6)
    (hPK : (P : Subgroup A6) ≤ K) (hK : K ≠ ⊤) :
    primeRank 3 K ≤ 1 :=
  three_rank_le_one_of_card_dvd_twenty_four
    (proper_sylow_overgroup_card_dvd_twenty_four P K hPK hK)

/-- The same obstruction in an arbitrary finite extension of A₆ by its two-core. -/
theorem twoCoreQuotient_sylow_overgroup_three_rank_le_one
    {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* A6)
    (P : Sylow 2 H) (M : Subgroup H)
    (hPM : (P : Subgroup H) ≤ M) (hM : M ≠ ⊤) :
    primeRank 3 M ≤ 1 := by
  let f : H →* A6 := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkerM : f.ker ≤ M := by
    rw [hker]
    exact (pCore_isPGroup.le_sylow_of_normal P).trans hPM
  have hproper : M.map f ≠ ⊤ := by
    intro hh
    have he := comap_map_eq_self hkerM
    rw [hh, comap_top] at he
    exact hM he.symm
  have hr : primeRank 3 (M.map f) ≤ 1 :=
    proper_sylow_overgroup_three_rank_le_one (P.mapSurjective hf) (M.map f)
      (map_mono hPM) hproper
  let g : M →* M.map f := f.subgroupMap M
  have hg : IsPGroup 2 g.ker := by
    have he : g.ker = f.ker.comap M.subtype := by
      ext x
      change (⟨f x, _⟩ : M.map f) = 1 ↔ f x = 1
      exact Subtype.ext_iff
    rw [he, hker]
    exact pCore_isPGroup.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨n, hn⟩ := hg.exists_card_eq
  exact (primeRank_le_of_coprime_ker 3 g (by rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)).trans hr

end Theory.SpecificGroups.SymmetricSix
