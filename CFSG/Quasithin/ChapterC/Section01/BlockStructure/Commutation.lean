module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Defs
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.PerfectAction
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Quotient
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# Commutation of blocks with a quasisimple quotient

For distinct subnormal short groups X and Y, if X/O₂(X) is quasisimple,
the actual images in G/O₂(G) commute. The residual characterization lifts
normalization and puts their commutator in both intrinsic two-cores.
Inside X Y, the perfect group X therefore centralizes the normal short
group Y by the finite endomorphism-field argument.

This proves the quasisimple/quasisimple and mixed cases of C.1.9. The case
where both two-core quotients have order three still needs the source's
conditional hypothesis on F*(O₂,₃(G)); it is kept explicit in the assembly
lemma below. No unconditional C.1.9 is asserted here yet.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
C.1.9--10, printed pp.123--124; C.1.9 cites Aschbacher (1981), §3.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Distinct blocks commute when the first has quasisimple two-core quotient.
The second may have quotient of order three. -/
theorem IsBlock.commutator_eq_bot_of_quasisimple_quotient {X Y : Subgroup G}
    (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : IsQuasisimple (X ⧸ pCore 2 X)) (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ := by
  have hc := BlockCommutation.quotient_commutation X Y hX hY hqX hne
  obtain ⟨hnX, hnY, hcores⟩ := BlockCommutation.pair_core_bound X Y hX hY hc
  let M := X ⊔ Y
  let A := Y.subgroupOf M
  let B := X.subgroupOf M
  have hXM : X ≤ M := le_sup_left
  have hYM : Y ≤ M := le_sup_right
  have hAm : A.map M.subtype = Y := map_subgroupOf_eq_of_le hYM
  have hBm : B.map M.subtype = X := map_subgroupOf_eq_of_le hXM
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le hnY Y.le_normalizer)
  have hA : IsShort A := hY.short.of_mulEquiv (subgroupOfEquivOfLe hYM).symm
  let := hqX
  let : Group.IsPerfect X := BlockCommutation.perfect_of_quasisimple_quotient hX.short
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXM).symm.surjective
  have hB : IsPPerfect 2 B := hX.short.twoPerfect.of_surjective
    (subgroupOfEquivOfLe hXM).symm.toMonoidHom (subgroupOfEquivOfLe hXM).symm.surjective
  have hbound : ⁅A, B⁆ ≤ (Y.pCoreIn 2).subgroupOf M := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, hAm, hBm, commutator_comm]
    exact hcores.trans inf_le_right
  have hp : IsPGroup 2 ↥(⁅A, B⁆ : Subgroup M) :=
    (isPGroup_pCoreIn 2 Y).comap_subtype.to_le hbound
  have hcA : ⁅A, B⁆ ≤ A.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp (commutator_le_left _ _)
      (normalizer_commutator_ge_left _ _)
  have he := BlockCommutation.perfect_actor_centralizes A B hA hB hcA
  have hm := congrArg (Subgroup.map M.subtype) he
  rwa [map_commutator, hAm, hBm, Subgroup.map_bot, commutator_comm] at hm

/-- Only the cubic/cubic source branch remains after the quasisimple argument.
The explicit branch premise must be discharged before invoking C.1.9. -/
theorem blocks_commute_of_cubic_case
    (hcubic : ∀ X Y : Subgroup G, IsBlock X → IsBlock Y →
      Nat.card (X ⧸ pCore 2 X) = 3 → Nat.card (Y ⧸ pCore 2 Y) = 3 →
      BlockCommutationHypothesis G → X ≠ Y → ⁅X, Y⁆ = ⊥)
    (hG : BlockCommutationHypothesis G) {X Y : Subgroup G}
    (hX : IsBlock X) (hY : IsBlock Y) (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ := by
  rcases hX.short.quotient with hqX | hqX
  · exact hX.commutator_eq_bot_of_quasisimple_quotient hY hqX hne
  · rcases hY.short.quotient with hqY | hqY
    · rw [commutator_comm]
      exact hY.commutator_eq_bot_of_quasisimple_quotient hX hqY hne.symm
    · exact hcubic X Y hX hY hqX hqY hG hne

end CFSG.Quasithin.ChapterC
