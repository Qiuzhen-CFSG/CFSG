module

public import Theory.SpecificGroups.Tits.EscapingSylowOvergroups
public import Theory.Representation.Tits.FrobeniusDisplacement.GroupData
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Five-subgroups in proper Tits Sylow overgroups

The certified elementary subgroup of order 25 gives five-rank at least two.
Every proper overgroup of a full Sylow two-subgroup is contained in one of
the two original Tits parabolics. The second has order 6144, so any
five-subgroup of such an overgroup lies in the first parabolic, the
centralizer of the full Sylow center. Sylow conjugacy transports this
statement along the caller's actual model equivalence.

This is the local input for the original prime-five ordinary-component
exclusion in Aschbacher--Smith 15.1.22--23, printed pp.1098--1100.
The underlying parabolic and five-local certificates retain their
Parrott (1972), p.683, and ATLAS TF42G1-max8W1 references.
-/

public section
open Subgroup Theory.GroupTheory
namespace Tits.FiveSylowOvergroups
open ExceptionalParabolics
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The actual Tits carrier contains an elementary subgroup of order 25. -/
theorem five_rank_ge_two : 2 ≤ primeRank 5 ParrottGroup := by
  let := Representation.TitsFrobeniusDisplacement.fiveKernel_elementary
  exact IsElementaryAbelian.primeRank_ge_of_card fiveKernel fiveKernel_card

private theorem five_subgroup_le_first (H A : Subgroup Atlas1600Group)
    (hH : H ≠ ⊤) (hSH : S ≤ H) (hAH : A ≤ H) (hA : IsPGroup 5 A) : A ≤ first := by
  rcases ConverseLocalCoverage.le_first_or_second H hH hSH with hf | hs
  · exact hAH.trans hf
  · have hc : Nat.Coprime 5 (Nat.card A) := by
      apply (by decide : Nat.Coprime 5 6144).of_dvd_right
      rw [← second_card]
      exact card_dvd_of_le (hAH.trans hs)
    obtain ⟨k,hk⟩ := hA.exists_card_eq
    have hcard : Nat.card A = 1 := by
      by_cases hk0 : k = 0
      · simpa only [hk0,pow_zero] using hk
      · have hd : 5 ∣ Nat.card A := by rw [hk]; exact dvd_pow_self 5 hk0
        exact False.elim ((by decide : ¬ Nat.Coprime 5 5) (hc.of_dvd_right hd))
    exact (card_eq_one.mp hcard).trans_le bot_le

private theorem centralizer_map_equiv {K H : Type*} [Group K] [Group H]
    (e : K ≃* H) (Z : Subgroup K) :
    (centralizer (Z : Set K)).map e.toMonoidHom = centralizer (Z.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e z) (mem_map_of_mem _ hz)

/-- Every five-subgroup of a proper full-Sylow overgroup centralizes the Sylow center. -/
theorem five_subgroup_le_sylow_center_centralizer {K : Type*} [Group K]
    (e : K ≃* ParrottGroup) (P : Sylow 2 K) (H A : Subgroup K)
    (hH : H ≠ ⊤) (hPH : (P : Subgroup K) ≤ H) (hAH : A ≤ H) (hA : IsPGroup 5 A) :
    A ≤ centralizer ((center P).map (P : Subgroup K).subtype : Set K) := by
  obtain ⟨f,hf⟩ := RelativeSylowMarking.exists_sylow_marking
    (e.trans parrottFiniteImageEquiv) P
  have hZ : ((center P).map (P : Subgroup K).subtype).map f.toMonoidHom =
      (center atlas1600SylowTwoSubgroup).map atlas1600SylowTwoSubgroup.subtype := by
    rw [map_map, ← map_center_image_of_injective (P : Subgroup K) f.toMonoidHom f.injective, hf]
  have hC : (centralizer ((center P).map (P : Subgroup K).subtype : Set K)).map
      f.toMonoidHom = first := by
    rw [centralizer_map_equiv, hZ, SylowCenterMaximal.standard_centralizer]
  apply (f.mapSubgroup.le_iff_le).mp
  change A.map f.toMonoidHom ≤ (centralizer
    ((center P).map (P : Subgroup K).subtype : Set K)).map f.toMonoidHom
  rw [hC]
  apply five_subgroup_le_first (H.map f.toMonoidHom) (A.map f.toMonoidHom)
  · intro he
    apply hH
    apply map_injective (f := f.toMonoidHom) f.injective
    exact he.trans (map_top_of_surjective f.toMonoidHom f.surjective).symm
  · change atlas1600SylowTwoSubgroup ≤ H.map f.toMonoidHom
    rw [← hf]
    exact map_mono hPH
  · exact map_mono hAH
  · exact hA.map f.toMonoidHom
end Tits.FiveSylowOvergroups
