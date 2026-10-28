module
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# Odd subgroups in proper Sylow overgroups of an A₅ two-core section

The literal two-core quotient sends a full Sylow subgroup to a Sylow
four-group in A₅. Every proper overgroup lies in its order-twelve
normalizer. An odd subgroup embeds through the two-group kernel, so its
order divides three. The kernel is retained throughout.

Source application: Aschbacher–Smith 5.1.13, printed pp.636–637, the
prescribed right Cartan in the unpaired A₅ residual branch.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.Alternating.FiveSylowMaximal
variable {X : Type*} [Group X] [Finite X]

/-- An odd subgroup of a proper full-Sylow overgroup has order at most three. -/
theorem odd_subgroup_card_le_three_of_core_quotient
    (e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 X) (M Y : Subgroup X) (hSM : (S : Subgroup X) ≤ M)
    (hM : M ≠ ⊤) (hYM : Y ≤ M) (ho : Odd (Nat.card Y)) :
    Nat.card Y ≤ 3 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 X := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff x)
  have hkM : f.ker ≤ M := hk ▸ (pCore_isPGroup.le_sylow_of_normal S).trans hSM
  have hm : M.map f ≠ ⊤ := by
    intro he
    apply hM
    have hh := congrArg (comap f) he
    simpa only [comap_map_eq_self hkM, comap_top] using hh
  let S' := S.mapSurjective hf
  have hN := overgroup_le_sylow_normalizer S' (M.map f) (map_mono hSM) hm
  have hdiv : Nat.card (Y.map f) ∣ 12 := by
    rw [← FiveBorelOvergroups.sylow_normalizer_card S']
    exact card_dvd_of_le ((map_mono hYM).trans hN)
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card f.ker) := by
    obtain ⟨k,hkcard⟩ := (hk ▸ (pCore_isPGroup : IsPGroup 2 (pCore 2 X))).exists_card_eq
    rw [hkcard]
    exact ho.coprime_two_right.pow_right k
  have hi : Function.Injective (f.subgroupMap Y) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro y hy
    apply Subtype.ext
    exact mem_bot.mp ((disjoint_of_coprime_natCard hcop).le_bot
      ⟨y.property, congrArg Subtype.val (show f.subgroupMap Y y = 1 from hy)⟩)
  have hc : Nat.card (Y.map f) = Nat.card Y :=
    (Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap Y)
      ⟨hi,f.subgroupMap_surjective Y⟩).toEquiv).symm
  rw [hc] at hdiv
  have hd : Nat.card Y ∣ 3 := (ho.coprime_two_right.pow_right 2).dvd_of_dvd_mul_left hdiv
  exact Nat.le_of_dvd (by decide) hd

end Theory.SpecificGroups.Alternating.FiveSylowMaximal
