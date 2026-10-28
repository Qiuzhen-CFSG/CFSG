module

public import Mathlib.GroupTheory.Sylow

/-!
# Sylow normalizers inside an overgroup

If a subgroup contains the full normalizer of one ambient Sylow subgroup,
then it contains the full normalizer of every ambient Sylow subgroup lying
in it. Conjugacy is taken inside the overgroup, so the conjugating element
also preserves the overgroup. This upgrades a conjugate parabolic cover of
a Sylow overgroup to a simultaneous cover of its Sylow normalizer.

We also record the elementary maximality argument placing a normalized
p-subgroup inside the normalizing Sylow subgroup.
Source: Sylow conjugacy and maximality; used in the parabolic argument of
Aschbacher--Smith, 15.3.43(e), printed p.1140.
-/

public section
open Subgroup

/-- A p-subgroup normalized by a Sylow p-subgroup lies in that Sylow. -/
theorem IsPGroup.le_sylow_of_normalized {G : Type*} [Group G] {p : ℕ}
    {R : Subgroup G} (hR : IsPGroup p R) (P : Sylow p G)
    (hn : (P : Subgroup G) ≤ normalizer (R : Set G)) : R ≤ P := by
  have h := P.is_maximal' (hR.to_sup_of_normal_left' P.isPGroup' hn) le_sup_right
  exact h ▸ le_sup_left

/-- Internal Sylow conjugacy transports containment of the full ambient
normalizer to every ambient Sylow subgroup in the overgroup. -/
theorem Sylow.normalizer_le_of_normalizer_le {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (U P : Sylow p G) (H : Subgroup G)
    (hU : normalizer (U : Set G) ≤ H) (hP : (P : Subgroup G) ≤ H) :
    normalizer (P : Set G) ≤ H := by
  have hUH : (U : Subgroup G) ≤ H := le_normalizer.trans hU
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (U.subtype hUH) (P.subtype hP)
  rw [Sylow.smul_subtype] at hh
  have he := congrArg Sylow.toSubgroup (Sylow.subtype_injective hh)
  change (U : Subgroup G).map (MulAut.conj (h : G)).toMonoidHom = (P : Subgroup G) at he
  change normalizer ((P : Subgroup G) : Set G) ≤ H
  rw [← he, ← map_equiv_normalizer_eq]
  rintro _ ⟨u, hu, rfl⟩
  exact H.mul_mem (H.mul_mem h.property (hU hu)) (H.inv_mem h.property)

/-- A proper cover after a change of coordinates covers the chosen Sylow
normalizer too, provided it contains one full ambient Sylow normalizer. -/
theorem Sylow.normalizer_sup_lt_top_of_map_le {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (U P : Sylow p G) (M H : Subgroup G)
    (e : G ≃* G) (hPM : (P : Subgroup G) ≤ M)
    (hMH : M.map e.toMonoidHom ≤ H) (hUH : normalizer (U : Set G) ≤ H)
    (hH : H < ⊤) : normalizer (P : Set G) ⊔ M < ⊤ := by
  have hN := U.normalizer_le_of_normalizer_le
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) H hUH
    ((map_mono hPM).trans hMH)
  change normalizer ((P : Subgroup G).map e.toMonoidHom : Set G) ≤ H at hN
  rw [← map_equiv_normalizer_eq] at hN
  have hlt := lt_of_le_of_lt (sup_le hN hMH) hH
  rw [← Subgroup.map_sup, ← map_top_of_surjective e.toMonoidHom e.surjective] at hlt
  exact (map_lt_map_iff_of_injective e.injective).mp hlt
