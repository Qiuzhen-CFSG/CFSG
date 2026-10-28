module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PermutingSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Detecting the core of a join by a common centralizer

Let `X = ⟨A,H⟩` contain a Sylow subgroup `T`. Suppose that `A` permutes
with `T` and acts faithfully on a seed `Z` centralized by `T`. For an
`X`-invariant subgroup `U` containing `Z`, this identifies `C_AT(U)` with
`C_T(U)`. If also `C_H(U) ≤ T`, the same subgroup is normal in both
generators, hence in `X`. When `O_p(X)` centralizes `U`, this proves
`O_p(X) = C_T(U)` on the original ambient carriers.

Source: Aschbacher--Smith, proof of 6.1.5, printed p.667, first paragraph.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- A faithful seed action removes the complement from a larger centralizer. -/
theorem inf_centralizer_sup_eq_of_faithful_seed
    (A T Z U : Subgroup G)
    (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hTZ : T ≤ centralizer (Z : Set G)) (hZU : Z ≤ U)
    (hfaith : A ⊓ centralizer (Z : Set G) = ⊥) :
    (A ⊔ T) ⊓ centralizer (U : Set G) = T ⊓ centralizer (U : Set G) := by
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (A : Set G) * (T : Set G) :=
      coe_sup_eq_mul_of_permutes A T hperm ▸ hx.1
    obtain ⟨a, ha, t, ht, hat⟩ := hxprod
    have hxZ : x ∈ centralizer (Z : Set G) := centralizer_le hZU hx.2
    have haZ : a ∈ centralizer (Z : Set G) := by
      have haeq : a = x * t⁻¹ := eq_mul_inv_iff_mul_eq.mpr hat
      rw [haeq]
      exact (centralizer (Z : Set G)).mul_mem hxZ
        ((centralizer (Z : Set G)).inv_mem (hTZ ht))
    have haone : a = 1 := mem_bot.mp (hfaith ▸ (show a ∈ A ⊓ centralizer
      (Z : Set G) from ⟨ha, haZ⟩))
    have hxt : x = t := by simpa only [haone, one_mul] using hat.symm
    exact ⟨hxt ▸ ht, hx.2⟩
  · exact le_inf (inf_le_left.trans le_sup_right) inf_le_right

/-- The common centralizer is the actual ambient prime core of the join. -/
theorem pCoreIn_sup_eq_sylow_centralizer_of_faithful_seed
    {p : ℕ} (T : Sylow p G) (A H Z U : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G)) (hZU : Z ≤ U)
    (hfaith : A ⊓ centralizer (Z : Set G) = ⊥)
    (hH : H ⊓ centralizer (U : Set G) ≤ (T : Subgroup G))
    (hU : A ⊔ H ≤ normalizer (U : Set G))
    (hcore : (A ⊔ H).pCoreIn p ≤ centralizer (U : Set G)) :
    (A ⊔ H).pCoreIn p = (T : Subgroup G) ⊓ centralizer (U : Set G) := by
  let Q := (T : Subgroup G) ⊓ centralizer (U : Set G)
  have hHC : H ⊓ centralizer (U : Set G) = Q :=
    le_antisymm (le_inf hH inf_le_right)
      (le_inf (inf_le_left.trans hTH) inf_le_right)
  have hAC : (A ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) = Q :=
    inf_centralizer_sup_eq_of_faithful_seed A T Z U hperm hTZ hZU hfaith
  have hNC : A ⊔ H ≤ normalizer (centralizer (U : Set G) : Set G) :=
    hU.trans (normalizer_le_normalizer_centralizer U)
  have hHQ : H ≤ normalizer (Q : Set G) := by
    rw [← hHC]
    exact (le_inf H.le_normalizer (le_sup_right.trans hNC)).trans
      inf_normalizer_le_normalizer_inf
  have hAQ : A ≤ normalizer (Q : Set G) := by
    rw [← hAC]
    exact (le_inf (le_sup_left.trans (A ⊔ (T : Subgroup G)).le_normalizer)
      (le_sup_left.trans hNC)).trans inf_normalizer_le_normalizer_inf
  have hTX : (T : Subgroup G) ≤ A ⊔ H := hTH.trans le_sup_right
  have hcoreT : (A ⊔ H).pCoreIn p ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTX] using
      pCoreIn_le_sylow (A ⊔ H) (T.subtype hTX)
  exact le_antisymm (le_inf hcoreT hcore)
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans hTX) (sup_le hAQ hHQ))

end Subgroup
