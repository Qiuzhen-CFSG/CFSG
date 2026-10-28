module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSylow
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Normalizer

/-!
# The changed-Sylow action on the chosen module

This application constructs the literal Sylow subgroup of `G₀T₀B` over
`T₀` and proves that it normalizes `DT₀`. The exact normalizer bound used
from source 4.3.17 is discharged using the original Sylow subgroup `T`:
it normalizes `T₀` of index two, and uniqueness over `LT` is already proved.
The remaining component analysis belongs to the consolidated owner
`qt-d-1222-rankone-cartan-local-to-global`; this is a step of 5.2.2,
not the final normalization theorem.

Source: Aschbacher--Smith, 5.2.2, p.648, and 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B E L₂ : Subgroup G} (D : ChosenModule T L V)
include D

/-- Source 4.3.17 in the literal index-two configuration of 5.2.2.
Only uniqueness over `LT` is needed in this application of 4.3.1. -/
theorem rankOne_prime_normalizingSylow_normalizer_le
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n p : ℕ}
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (he : CartanPrimeActor A H p E)
    (d : Prime.LocalData T L H B E L₂)
    (hz : (Prime.generated L H E L₂).pCoreIn 2 ≠ ⊥) :
    normalizer (Prime.normalizingSylow T L₂ : Set G) ≤ normalizer (L : Set G) := by
  have hTN := d.overgroup_two_subgroup_normalizes hH.1.1.2 c he hz T.isPGroup' inf_le_left
  have hTMN := le_inf D.sylow_normalizes_component hTN
  have hi : ¬ 2 ∣ (T : Subgroup G).relIndex
      (normalizer (L : Set G) ⊓ normalizer (Prime.normalizingSylow T L₂ : Set G)) :=
    fun hdiv => T.not_dvd_index (hdiv.trans (relIndex_dvd_index_of_le hTMN))
  obtain ⟨Q,hQ⟩ := Chapter4.Section03.RankOneUniqueness.exists_sylow_component D
  have hQT₀ : (Q : Subgroup L).map L.subtype ≤ Prime.normalizingSylow T L₂ := by
    rw [hQ]
    exact le_inf inf_le_left
      ((d.S_intersection_left.ge.trans inf_le_left).trans d.S_normalizes_right)
  exact Chapter4.Section03.RankOneUniqueness.normalizer_le_of_local_sylow D h hpsl
    (T : Subgroup G) (Prime.normalizingSylow T L₂)
    (T.isPGroup'.to_le inf_le_left) (inf_le_left.trans D.sylow_normalizes_component)
    ⟨Q,hQT₀⟩ T.isPGroup' hTMN hi
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h)

/-- Apply the source normalizer bound to the actual changed Sylow witness,
retaining its ambient-Sylow dichotomy and common-normal overgroup. -/
theorem rankOne_prime_changedSylow_action
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
      T₁ ≤ normalizer ((E ⊔ Prime.normalizingSylow T L₂ : Subgroup G) : Set G) ∧
      (Prime.normalizingSylow T L₂).relIndex T₁ ≤ 2 ∧
      (T₁ = Prime.normalizingSylow T L₂ ∨ ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  exact d.changedSylow_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH c he hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
