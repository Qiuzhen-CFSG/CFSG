module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Models
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import GorensteinWalter.PSL2CoprimeSylowCyclic

/-!
# Removing the PSL₂ and Suzuki covers on the actual actor

Every odd Sylow subgroup of these two models is cyclic, by the existing
matrix-group torus results. Central Sylow transfer therefore excludes
every odd prime from the kernel of the canonical perfect cover. Its
remaining two-part vanishes because the actor has trivial two-core.
This handles the possible exceptional two-covers of Sz(8) without
asserting that its multiplier is trivial or computing its full cover.

Thus centerlessness, J=O₂(H), and the marked actor models are fully
proved in the PSL₂ and Suzuki branches. The PSU₃ and rank-two branches
are separate; no multiplier-table hypothesis is used here.

Source: Aschbacher--Smith, E.2.2, pp.215--216; I.1.2, p.407;
and the single-component argument in 15.3.65, p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
open BorelReduction SourceCases
namespace CoverModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {H M K T Z ZS : Subgroup G} {f : ℕ}
variable [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
variable {a : LocalQuotientAction H (conjugateSpanBy ZS H) Z}
variable {I : Submodule (ZMod 2)
  (Additive ((conjugateSpanBy ZS H) ⧸ Z.subgroupOf (conjugateSpanBy ZS H)))}
variable (h : LocalInput 𝒦 H M K T Z ZS f a I)
include h

/-- Cyclic odd Sylow subgroups kill the odd kernel of the actual perfect
cover. Its possible two-kernel is killed by O₂(A)=1. -/
theorem center_eq_bot_of_cyclic_odd_sylows {X : Type*} [Group X] [Finite X]
    (e : sourceImage H M K ≃* X)
    (hcyclic : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ S : Sylow p X, IsCyclic S) :
    center (actorImage H K) = ⊥ := by
  apply card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  by_cases hp2 : p = 2
  · exact center_no_two h (hp2 ▸ hd)
  let : Fact p.Prime := ⟨hp⟩
  have hn := (modelCover h e).not_dvd_card_multiplier_of_isCyclic_sylow (hcyclic p hp2)
  change ¬ p ∣ Nat.card (modelCover h e).toMonoidHom.ker at hn
  rw [modelCover_ker] at hn
  exact hn hd

/-- No ordinary or exceptional Suzuki cover survives in this actor.
In particular this does not assume Sz(8) has trivial multiplier. -/
theorem suzuki_center_eq_bot {m : ℕ} (hm : 1 ≤ m)
    (e : sourceImage H M K ≃* SuzukiMatrixGroup m) :
    center (actorImage H K) = ⊥ := by
  apply center_eq_bot_of_cyclic_odd_sylows h e
  intro p hp hp2 S
  exact suzukiSylow_isCyclic_of_ne_two (by omega) hp2 S

/-- The odd-exponent binary PSL₂ cover collapses by torus cyclicity and transfer. -/
theorem psl2_center_eq_bot {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f)
    (e : sourceImage H M K ≃* BenderSuzuki.Converse.PSL2 F) :
    center (actorImage H K) = ⊥ := by
  have hf3 : 3 ≤ f := by
    have hf := h.source.exponent_gt_one
    obtain ⟨n, hn⟩ := h.odd
    omega
  have hseven : 7 ≤ Nat.card F := by
    rw [hF]
    exact (by decide : 7 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by decide) hf3)
  apply center_eq_bot_of_cyclic_odd_sylows h e
  intro p hp hp2 S
  apply GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF hseven p hp2 _ S
  rw [hF]
  exact (Nat.coprime_two_right.mpr (hp.out.odd_of_ne_two hp2)).pow_right f

/-- In both linear-two and Suzuki source branches the center calculation is
fully discharged on the actual local actor. -/
theorem exchangedModel_center_eq_bot (hm : ExchangedModel H M K f) :
    center (actorImage H K) = ⊥ := by
  rcases hm with ⟨F, hF, hfin, hc, _, hcard, e, _⟩ | ⟨m, hm, _, e, _⟩
  · exact psl2_center_eq_bot h hcard e
  · exact suzuki_center_eq_bot h hm e

/-- The actual kernel equality and Bender recognition are unconditional in
the PSL₂/Suzuki branches, even though the unitary branch remains separate. -/
theorem rankOne_models (hm : ExchangedModel H M K f) :
    sourceKernel H M = pCore 2 H ∧ ActorBenderModel H M K f := by
  have hz := exchangedModel_center_eq_bot h hm
  exact ⟨sourceKernel_eq_twoCore_of_center_eq_bot h hz, actor_bender_model h hz (Or.inl hm)⟩

end CoverModels
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
