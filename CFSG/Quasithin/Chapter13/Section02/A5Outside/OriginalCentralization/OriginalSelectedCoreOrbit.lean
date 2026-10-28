module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobal
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The actual Sylow orbit of a nonzero selected pair core

The normalizer in T of the selected right factor fixes L, R and the original
source core S, so it fixes the pair core. The full T cannot fix a nonzero
pair core: uniqueness over LT would place the escaping right factor in N(L).
When the factor normalizer has index at most two, the two normalizers agree
and have index exactly two.

This retains the genuine two-element core orbit. It does not assert that
either core lies in S, or that the two right factors normalize their join.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G}

/-- A nonzero pair core has precisely the selected factor's index-two
normalizer in the original ambient Sylow. -/
theorem original_selected_pair_core_normalizer
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : R ⊔ (T : Subgroup G) = H)
    (hindex : ((T : Subgroup G) ⊓ normalizer (R : Set G)).relIndex
      (T : Subgroup G) ≤ 2)
    (hne : (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≠ ⊥) :
    let U := (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2
    (T : Subgroup G) ⊓ normalizer (U : Set G) =
      (T : Subgroup G) ⊓ normalizer (R : Set G) ∧
    ((T : Subgroup G) ⊓ normalizer (U : Set G)).relIndex (T : Subgroup G) = 2 := by
  let N := ChapterF.Source.generated ![L,R] (Global.sourceS L H)
  let U := N.pCoreIn 2
  let T₀ := (T : Subgroup G) ⊓ normalizer (R : Set G)
  have hNU : N ≤ normalizer (U : Set G) :=
    N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hTU : ¬ (T : Subgroup G) ≤ normalizer (U : Set G) := by
    intro hn
    have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (U : Set G) :=
      sup_le ((show L ≤ N from le_sup_left.trans le_sup_left).trans hNU) hn
    have hNM := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
      (isPGroup_pCoreIn 2 N) hne hLT
    have hRM : R ≤ normalizer (L : Set G) :=
      (show R ≤ N from le_sup_right.trans le_sup_left).trans (hNU.trans hNM)
    exact hH.1.2 (hgen ▸ sup_le hRM d.normalizes_L)
  have hTS : (T : Subgroup G) ≤ normalizer (Global.sourceS L H : Set G) :=
    (le_inf d.normalizes_L hH.1.1.2).trans (Global.intersection_normalizes_sourceS L H)
  have hT₀N : T₀ ≤ normalizer (N : Set G) := by
    change T₀ ≤ normalizer ((L ⊔ R ⊔ Global.sourceS L H : Subgroup G) : Set G)
    apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
    refine le_inf ?_ (inf_le_left.trans hTS)
    apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact le_inf (inf_le_left.trans d.normalizes_L) inf_le_right
  have hT₀U : T₀ ≤ normalizer (U : Set G) :=
    hT₀N.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hi : T₀.relIndex (T : Subgroup G) = 2 := by
    have hp : T₀.relIndex (T : Subgroup G) ≠ 0 :=
      (T₀.subgroupOf (T : Subgroup G)).index_ne_zero_of_finite
    have hn : T₀.relIndex (T : Subgroup G) ≠ 1 :=
      fun hh => hTU ((relIndex_eq_one.mp hh).trans hT₀U)
    change T₀.relIndex (T : Subgroup G) ≤ 2 at hindex
    omega
  have he : (T : Subgroup G) ⊓ normalizer (U : Set G) = T₀ := by
    have hle : T₀ ≤ (T : Subgroup G) ⊓ normalizer (U : Set G) := le_inf inf_le_left hT₀U
    have hh := relIndex_mul_relIndex T₀ ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (T : Subgroup G) hle inf_le_left
    rw [hi] at hh
    have hp : (T₀.relIndex ((T : Subgroup G) ⊓ normalizer (U : Set G)) *
      ((T : Subgroup G) ⊓ normalizer (U : Set G)).relIndex (T : Subgroup G)).Prime :=
      hh.symm ▸ Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_,h₁⟩ | ⟨_,h₁⟩
    · exact (hTU ((relIndex_eq_one.mp h₁).trans inf_le_right)).elim
    · exact le_antisymm (relIndex_eq_one.mp h₁) hle
  exact ⟨he,he ▸ hi⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
