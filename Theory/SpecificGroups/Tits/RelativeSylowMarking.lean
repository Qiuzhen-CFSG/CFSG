module

public import Theory.SpecificGroups.Tits.FiniteSimple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Marking a Sylow subgroup of the simple Tits group

Sylow conjugacy aligns any supplied Sylow two-subgroup with the certified
Atlas subgroup. Its center has precisely one nonidentity element, r5, so the
same marking sends every supplied nonidentity central element to r5.
Centerlessness follows from simplicity and the composite group order.

Only the simple Tits carrier is used. No automorphism extension or parabolic
core calculation is required. Source: Sylow conjugacy and Parrott (1972),
§5, p.683; the concrete center certificate is in Atlas1600SylowTwo.
-/

@[expose] public section

open Subgroup
namespace Tits.RelativeSylowMarking

/-- The concrete simple group is centerless. -/
theorem atlas_center_eq_bot : center Atlas1600Group = ⊥ := by
  rcases (inferInstance : (center Atlas1600Group).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let : IsMulCommutative Atlas1600Group := center_eq_top_iff.mp h
    have hp : (Nat.card Atlas1600Group).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rw [atlas1600Group_card] at hp
    have hd := (Nat.dvd_prime hp).mp (by norm_num : 2 ∣ 17971200)
    omega

variable {K : Type*} [Group K]

/-- Centerlessness transports to every actual model of the Tits group. -/
theorem center_eq_bot (e : K ≃* Atlas1600Group) : center K = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ center Atlas1600Group := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx a)
  rw [atlas_center_eq_bot, mem_bot] at he
  exact e.injective (he.trans (map_one e).symm)

/-- A marking can retain any prescribed Sylow two-subgroup. -/
theorem exists_sylow_marking (e : K ≃* Atlas1600Group) (R : Sylow 2 K) :
    ∃ f : K ≃* Atlas1600Group,
      (R : Subgroup K).map f.toMonoidHom = atlas1600SylowTwoSubgroup := by
  let : Finite K := Finite.of_injective e e.injective
  let Q : Sylow 2 Atlas1600Group := R.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Atlas1600Group Q atlas1600SylowTwo
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change (R : Subgroup K).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← Subgroup.map_map]
  have hh := congrArg Sylow.toSubgroup hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, atlas1600SylowTwo_coe] at hh
  change (Q : Subgroup Atlas1600Group).map (MulAut.conj g).toMonoidHom =
    atlas1600SylowTwoSubgroup at hh
  have hQ : (Q : Subgroup Atlas1600Group) = (R : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective R
  rwa [hQ] at hh

/-- Aligning the Sylow subgroup also aligns its nonidentity central element. -/
theorem image_eq_r5_of_sylow_center (e : K ≃* Atlas1600Group) (R : Sylow 2 K)
    (hR : (R : Subgroup K).map e.toMonoidHom = atlas1600SylowTwoSubgroup)
    {t : K} (ht : t ∈ (R : Subgroup K))
    (hc : t ∈ centralizer (R : Set K)) (hne : t ≠ 1) : e t = atlas1600R5 := by
  have ht' : e t ∈ atlas1600SylowTwoSubgroup :=
    hR ▸ mem_map_of_mem e.toMonoidHom ht
  have hc' : (⟨e t, ht'⟩ : atlas1600SylowTwoSubgroup) ∈
      center atlas1600SylowTwoSubgroup := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, hx, hxy⟩ := (show (y : Atlas1600Group) ∈
      (R : Subgroup K).map e.toMonoidHom from hR.symm ▸ y.property)
    apply Subtype.ext
    change (y : Atlas1600Group) * e t = e t * (y : Atlas1600Group)
    rw [← hxy]
    exact (map_mul e x t).symm.trans
      ((congrArg e (mem_centralizer_iff.mp hc x hx)).trans (map_mul e t x))
  rcases (atlas1600SylowTwo_mem_center_iff ⟨e t, ht'⟩).mp hc' with he | he
  · exact (hne (e.injective (he.trans (map_one e).symm))).elim
  · exact he

end Tits.RelativeSylowMarking

end
