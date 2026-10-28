module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Order.Atoms
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Overgroups of an index-two parabolic

For a maximal subgroup L of a normalized factor C, with [L⋅T:L]=2, every
overgroup of L in C⋅T either equals L or L⋅T or contains C. This elementary
alternatives lemma supplies the source 5.2.20 edge-fixer argument.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.QuasithinM23

private theorem coatom_intersection {G : Type*} [Group G]
    (L C R : Subgroup G) (hLC : L ≤ C) (hm : IsCoatom (L.subgroupOf C))
    (hLR : L ≤ R) (hn : ¬ C ≤ R) : C ⊓ R = L := by
  have hproper : R.subgroupOf C ≠ ⊤ := fun hh => hn (subgroupOf_eq_top.mp hh)
  have hh := (hm.le_iff_eq hproper).mp (subgroupOf_mono C hLR)
  have hh' := congrArg (Subgroup.map C.subtype) hh
  rw [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hLC] at hh'
  exact (inf_comm _ _).trans hh'

/-- Above a maximal subgroup of a normalized factor, only the normalizer
branch and subgroups containing the whole factor can occur. -/
theorem parabolic_overgroup_alternatives {G : Type*} [Group G]
    (L C T : Subgroup G) (hLC : L ≤ C) (hm : IsCoatom (L.subgroupOf C))
    (hTN : T ≤ normalizer (L : Set G)) (hTC : T ≤ normalizer (C : Set G))
    (hCN : ¬ C ≤ normalizer (L : Set G))
    (hi : L.relIndex (L ⊔ T) = 2)
    (R : Subgroup G) (hLR : L ≤ R) (hRX : R ≤ C ⊔ T) :
    R = L ∨ R = L ⊔ T ∨ C ≤ R := by
  by_cases hCR : C ≤ R
  · exact Or.inr (Or.inr hCR)
  have hcap := coatom_intersection L C R hLC hm hLR hCR
  have hRN : R ≤ normalizer (L : Set G) := by
    rw [←hcap]
    exact (le_inf (hRX.trans (sup_le C.le_normalizer hTC)) R.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hNC := coatom_intersection L C (normalizer (L : Set G)) hLC hm L.le_normalizer hCN
  have hRL : R ≤ L ⊔ T := by
    intro r hr
    have hp : r ∈ (C : Set G) * (T : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left C T hTC]
      exact hRX hr
    obtain ⟨c,hc,t,ht,rfl⟩ := hp
    have hcN : c ∈ normalizer (L : Set G) := by
      have hh := (normalizer (L : Set G)).mul_mem (hRN hr)
        ((normalizer (L : Set G)).inv_mem (hTN ht))
      simpa only [mul_inv_cancel_right] using hh
    exact mul_mem_sup (hNC ▸ (show c ∈ C ⊓ normalizer (L : Set G) from ⟨hc,hcN⟩)) ht
  have hmax : IsCoatom (L.subgroupOf (L ⊔ T)) := by
    refine ⟨fun hh => by simp [show L.relIndex (L ⊔ T) = (L.subgroupOf (L ⊔ T)).index from rfl,hh] at hi,
      fun B hB => ?_⟩
    have hh := relIndex_mul_index hB.le
    change _ = L.relIndex (L ⊔ T) at hh
    rw [hi] at hh
    have hp : ((L.subgroupOf (L ⊔ T)).relIndex B * B.index).Prime := hh ▸ Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hb⟩ | ⟨_,hb⟩
    · exact index_eq_one.mp hb
    · exact (hB.not_ge (relIndex_eq_one.mp hb)).elim
  by_cases htop : R.subgroupOf (L ⊔ T) = ⊤
  · exact Or.inr (Or.inl (le_antisymm hRL (subgroupOf_eq_top.mp htop)))
  · have hh := (hmax.le_iff_eq htop).mp (subgroupOf_mono (L ⊔ T) hLR)
    have hh' := congrArg (Subgroup.map (L ⊔ T).subtype) hh
    rw [map_subgroupOf_eq_of_le hRL,map_subgroupOf_eq_of_le le_sup_left] at hh'
    exact Or.inl hh'
end Theory.GroupTheory.QuasithinM23
