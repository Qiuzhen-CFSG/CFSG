module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeTerminal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The changed-Sylow reduction on the chosen module

The original Chapter 12 input now proves that the selected prime actor moves
L₂, and constructs the Sylow subgroup of G₀T₀B over T₀. Any proper enlargement
is certified to be Sylow in G. The literal common-normal overgroup is also
available for the remaining component embedding argument.

The final application removes the movement premise from the elementary
order-27 contradiction. The cubic-plane classification itself remains an
explicit input, to be discharged by qt-d-1222-rankone-cartan-local-to-global.
The right-factor construction and zero-core model exclusions remain with
that same owner. None of these conditional applications is full 5.2.2.

Source: Aschbacher--Smith, original 5.2.2, pp.648--649, and 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B E L₂ : Subgroup G} (D : ChosenModule T L V)
include D

/-- The chosen-module consumer receives the literal changed Sylow and its
ambient-Sylow dichotomy, together with the required local overgroup. -/
theorem rankOne_prime_changedSylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (he : CartanPrimeActor A H p E)
    (d : Prime.LocalData T L H B E L₂)
    (hz : (Prime.generated L H E L₂).pCoreIn 2 ≠ ⊥) :
    ¬ E ≤ normalizer (L₂ : Set G) ∧
    normalizer (Prime.normalizingSylow T L₂ : Set G) ⊔ H ∈ Chapter1.HOver G (H : Set G) ∧
    ∃ P : Sylow 2 (Prime.extension T L H B E L₂),
      let T₁ := (P : Subgroup (Prime.extension T L H B E L₂)).map
        (Prime.extension T L H B E L₂).subtype
      Prime.normalizingSylow T L₂ ≤ T₁ ∧
      T₁ ≤ normalizer (Prime.normalizingSylow T L₂ : Set G) ∧
      (Prime.normalizingSylow T L₂).relIndex T₁ ≤ 2 ∧
      (T₁ = Prime.normalizingSylow T L₂ ∨ ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  refine ⟨d.prime_actor_not_normalizes_right hi hH c he hz,
    d.common_normal_overgroup hi hH c he hz, ?_⟩
  obtain ⟨P,hTP,hindex,hcases⟩ := d.exists_changedSylow hH.1.1.2 c he hz
  exact ⟨P,hTP,d.overgroup_two_subgroup_normalizes hH.1.1.2 c he hz
    (P.isPGroup'.map _) hTP,hindex,hcases⟩

/-- The cubic-plane output now suffices for the actual prime-actor contradiction:
movement of L₂ is proved from the original zero-core actor and nonzero G₀-core. -/
theorem rankOne_prime_excluded_of_cubic_plane
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (he : CartanPrimeActor A H 3 E)
    (d : Prime.LocalData T L H B E L₂)
    (hz : (Prime.generated L H E L₂).pCoreIn 2 ≠ ⊥)
    (hB : IsElementaryAbelian 3 B) (hcard : Nat.card B = 9) : False := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact hi.prime_actor_excluded_of_cubic_plane c he hB hcard d.B_normalizes_right
    (d.prime_actor_not_normalizes_right hi hH c he hz)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
