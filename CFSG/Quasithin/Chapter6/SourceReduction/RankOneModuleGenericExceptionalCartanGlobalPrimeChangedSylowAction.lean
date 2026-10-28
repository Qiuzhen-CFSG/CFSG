module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeNormalizer

/-!
# The source changed Sylow normalizes the prime-factor extension

In the nonzero-core branch of original 5.2.2, source 4.3.17 gives
`N_G(T₀) ≤ N_G(L)`, where `T₀ = N_T(L₂)`. A Sylow 2-subgroup over `T₀`
then normalizes both `T₀` and `L`. Its action on `T ∩ L` preserves the
local Borel `N_L(T ∩ L)`, and the Cartan characteristic-subgroup argument
shows it also preserves `(T ∩ L)D`. Together these imply normalization of
`DT₀`, the subgroup needed for the subsequent component argument.

The first theorem isolates the Cartan action argument. The final theorems
discharge its normalizer premise from the original `Input` and construct
the complete changed-Sylow witness needed by the component argument.
The final component classification remains with the consolidated owner
`qt-d-1222-rankone-cartan-local-to-global`. Source: Aschbacher--Smith,
4.3.1, p.613, and 5.2.2, p.648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The changed Sylow normalizes `DT₀` once source 4.3.17 places
`N_G(T₀)` inside `N_G(L)`. -/
theorem LocalData.changedSylow_normalizes_actor_join
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D L₂))
    (hTP : normalizingSylow T L₂ ≤
      (P : Subgroup (extension T L H B D L₂)).map
        (extension T L H B D L₂).subtype)
    (hN : normalizer (normalizingSylow T L₂ : Set G) ≤ normalizer (L : Set G)) :
    (P : Subgroup (extension T L H B D L₂)).map
      (extension T L H B D L₂).subtype ≤
      normalizer ((D ⊔ normalizingSylow T L₂ : Subgroup G) : Set G) := by
  let T₀ := normalizingSylow T L₂
  let T₁ := (P : Subgroup (extension T L H B D L₂)).map
    (extension T L H B D L₂).subtype
  have hT₁T₀ : T₁ ≤ normalizer (T₀ : Set G) :=
    d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz
      (P.isPGroup'.map (extension T L H B D L₂).subtype) hTP
  have hT₁L : T₁ ≤ normalizer (L : Set G) := hT₁T₀.trans hN
  have hST₀ : Global.sourceS L H ≤ T₀ := d.sourceS_le_normalizingSylow h hH
  have hUT₀ : (T : Subgroup G) ⊓ L ≤ T₀ := by
    rw [← d.S_intersection_left]
    exact inf_le_left.trans hST₀
  have hU : T₀ ⊓ L = (T : Subgroup G) ⊓ L := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · exact le_inf hUT₀ inf_le_right
  have hT₁U : T₁ ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    rw [← hU]
    exact (le_inf hT₁T₀ hT₁L).trans inf_normalizer_le_normalizer_inf
  have hT₁NU : T₁ ≤
      normalizer (normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) : Set G) :=
    hT₁U.trans (normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)).le_normalizer
  have hT₁Borel : T₁ ≤ normalizer (localBorel T L : Set G) := by
    change T₁ ≤ normalizer
      ((L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G)
    exact (le_inf hT₁L hT₁NU).trans inf_normalizer_le_normalizer_inf
  have hT₁UD : T₁ ≤
      normalizer ((((T : Subgroup G) ⊓ L) ⊔ D : Subgroup G) : Set G) :=
    hT₁Borel.trans
      (cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear hd.le_cartan)
  have hjoin : (((T : Subgroup G) ⊓ L) ⊔ D) ⊔ T₀ = D ⊔ T₀ := by
    calc
      (((T : Subgroup G) ⊓ L) ⊔ D) ⊔ T₀ =
          ((T : Subgroup G) ⊓ L) ⊔ (D ⊔ T₀) := sup_assoc _ _ _
      _ = D ⊔ T₀ := sup_eq_right.mpr (hUT₀.trans le_sup_right)
  have hT₁DT₀ : T₁ ≤ normalizer
      (((((T : Subgroup G) ⊓ L) ⊔ D) ⊔ T₀ : Subgroup G) : Set G) :=
    (le_inf hT₁UD hT₁T₀).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  simpa only [hjoin] using hT₁DT₀

/-- The original `Input` proves the normalizer bound required in the
nonzero-core branch of 5.2.2, without a chosen-module hypothesis. -/
theorem LocalData.normalizingSylow_normalizer_le
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    normalizer (normalizingSylow T L₂ : Set G) ≤ normalizer (L : Set G) := by
  apply h.normalizer_le_of_sylow_normalizes inf_le_left
  · rw [← d.S_intersection_left]
    exact inf_le_left.trans (d.sourceS_le_normalizingSylow h hH)
  · exact d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz T.isPGroup' inf_le_left

/-- Construct the literal changed Sylow together with its action on `DT₀`,
its ambient-Sylow dichotomy, and the common-normal overgroup. -/
theorem LocalData.changedSylow_action
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    ¬ D ≤ normalizer (L₂ : Set G) ∧
    normalizer (normalizingSylow T L₂ : Set G) ⊔ H ∈ Chapter1.HOver G (H : Set G) ∧
    ∃ P : Sylow 2 (extension T L H B D L₂),
      let T₁ := (P : Subgroup (extension T L H B D L₂)).map
        (extension T L H B D L₂).subtype
      normalizingSylow T L₂ ≤ T₁ ∧
      T₁ ≤ normalizer (normalizingSylow T L₂ : Set G) ∧
      T₁ ≤ normalizer ((D ⊔ normalizingSylow T L₂ : Subgroup G) : Set G) ∧
      (normalizingSylow T L₂).relIndex T₁ ≤ 2 ∧
      (T₁ = normalizingSylow T L₂ ∨ ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨P,hTP,hindex,hcases⟩ := d.exists_changedSylow hH.1.1.2 c hd hz
  refine ⟨d.prime_actor_not_normalizes_right h hH c hd hz,
    d.common_normal_overgroup h hH c hd hz, P, hTP, ?_, ?_, hindex, hcases⟩
  · exact d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz
      (P.isPGroup'.map (extension T L H B D L₂).subtype) hTP
  · exact d.changedSylow_normalizes_actor_join h hH c hd hz P hTP
      (d.normalizingSylow_normalizer_le h hH c hd hz)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
