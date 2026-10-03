module
public import Stellmacher.SectionEight.GeneratedEightSixNormalizerExtraction
public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator

/-!
The literal commutator cost of a next-stabilizer actor is a power of two.
At critical length two, the next module and its center lie in the next
two-core, as does every actor displacement. Their joined subgroup is a
two-group, and the cost is a relative index dividing its order.

The companion arithmetic split states that a cost greater than two is
either four or at least eight. These are the two remaining large-index
branches in Stellmacher's proof of (8.6), printed p.44, before (15).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_actor_cost_is_two_power
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (actor : G) (ha : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ n : ℕ, eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 2 ^ n := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let J := ⁅V,Subgroup.zpowers actor⁆ ⊔ Z
  have hVR : V ≤ R := eight_six_neighborhood_closure_le_core Γ cp
    (by exact hlength ▸ by decide) _
  have hZQ : Z ≤ R := ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.firstStep cp.a
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hJV : ⁅V,Subgroup.zpowers actor⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr ha).trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hJQ : J ≤ R := sup_le (hJV.trans hVR) hZQ
  have hp : IsPGroup 2 R := by
    change IsPGroup 2 (Γ.twoCoreAt _)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hpJ : IsPGroup 2 J := hp.to_le hJQ
  obtain ⟨k,hk⟩ := hpJ.exists_card_eq
  have hdvd : Z.relIndex J ∣ 2^k := hk ▸ Subgroup.relIndex_dvd_card Z J
  obtain ⟨n,_,hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨n,hn⟩

public theorem eight_six_actor_cost_eq_four_or_ge_eight
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (actor : G) (ha : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 2 < eightSixCommutatorCost ctx.Γ ctx.criticalPath actor) :
    eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4 ∨
      8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath actor := by
  obtain ⟨n,hn⟩ := eight_six_actor_cost_is_two_power ctx hlength actor ha
  rw [hn] at hlarge ⊢
  by_cases hsmall : n ≤ 2
  · interval_cases n
    · norm_num at hlarge
    · norm_num at hlarge
    · exact Or.inl rfl
  · exact Or.inr (show 2^3 ≤ 2^n from Nat.pow_le_pow_right (by decide) (by omega))

end Stellmacher.SectionEight
