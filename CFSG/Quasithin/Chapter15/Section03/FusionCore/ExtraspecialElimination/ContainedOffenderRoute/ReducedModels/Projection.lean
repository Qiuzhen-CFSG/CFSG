module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Basic

/-!
# Projection and cubic control with a solvable base

These adapters use the lower proofs in ModelReduction.InvariantProjection
and BinaryModels.CubicControl with precisely their needed solvability input,
Y₀T. The old public records and their stronger assumptions are preserved.
The inner-projection proof still constructs its nontrivial invariant image;
its cubic element yields containment through the actual Y₀/O₂(Y₀).

This is the terminal algebra for (k), not the missing Borel/automorphism
analysis supplying an inner action. The cubic-envelope obstruction will
also be used to collapse the component orbit after (k).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1144, proof of 15.3.49(k)–(l).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open Subgroup ComponentReduction ModelReduction
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

theorem containment_of_inner_action
    (H M Y0 L T : Subgroup G) [Group.IsSolvable (Y0 ⊔ T : Subgroup G)]
    (hgen : H = reducedOvergroup L Y0 T)
    (hθ : theta (M ⊓ H) = Y0)
    (hj : ∀ K : Subgroup G, Group.IsSolvable K → Y0 ⊔ T ≤ K → K ≤ H → K ≤ M ⊓ H)
    (hY : IsPPerfect 2 Y0) (hcard : Nat.card ((Y0.subgroupOf H) ⧸ pCore 2 (Y0.subgroupOf H)) = 3)
    (hTY : T ≤ normalizer (Y0 : Set G)) (hcomm : L = ⁅L, Y0⁆)
    (hne : starImage H (localSpan L T) ≠ ⊥)
    (hcenter : center (starImage H (localSpan L T)) = ⊥)
    (hinner : ∀ y : starImage H Y0, ∃ l : starImage H (localSpan L T),
      ∀ x : starImage H (localSpan L T),
        (l : H ⧸ pCore 2 H) * x * l⁻¹ = y * x * y⁻¹) : Y0 ≤ localSpan L T := by
  let L0 := localSpan L T
  have hL0H : L0 ≤ H := hgen ▸ le_sup_left
  have hYH : Y0 ≤ H := hgen ▸ (le_sup_left.trans le_sup_right)
  have hTH : T ≤ H := hgen ▸ (le_sup_right.trans le_sup_right)
  let Y' := Y0.subgroupOf H
  let T' := T.subgroupOf H
  let L' := L0.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hnorm : L'.Normal := by
    have hh := componentClosure_normal_in_replacement L Y0 T
      (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hTY
    rwa [← hgen] at hh
  let := hnorm
  let : (L'.map q).Normal := hnorm.map q (QuotientGroup.mk'_surjective _)
  have hjoin : Y' ⊔ T' = (Y0 ⊔ T).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hYH, map_subgroupOf_eq_of_le hTH,
      map_subgroupOf_eq_of_le (sup_le hYH hTH)]
  let : Group.IsSolvable (Y' ⊔ T' : Subgroup H) := by
    rw [hjoin]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (sup_le hYH hTH)).toMonoidHom)
      (subgroupOfEquivOfLe (sup_le hYH hTH)).injective
  have hθ' : theta ((M ⊓ H).subgroupOf H) = Y' := by
    apply map_injective H.subtype_injective
    rw [theta_map_of_injective _ H.subtype_injective,
      map_subgroupOf_eq_of_le inf_le_right, hθ, map_subgroupOf_eq_of_le hYH]
  have hTY' : T' ≤ normalizer (Y' : Set H) := by
    apply le_normalizer_iff.mpr
    intro t ht y hy
    exact le_normalizer_iff.mp hTY t ht y hy
  have hcomm' : L' = ⁅L', Y'⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hL0H, map_subgroupOf_eq_of_le hYH]
    exact componentClosure_commutator L Y0 T hcomm hTY
  have hle : Y' ≤ L' := by
    apply le_of_inner_image_action q (QuotientGroup.mk'_surjective _)
      (by dsimp [q]; rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
      ((M ⊓ H).subgroupOf H) Y' T' L' hθ' ?_
      (hY.of_surjective (subgroupOfEquivOfLe hYH).symm.toMonoidHom
        (subgroupOfEquivOfLe hYH).symm.surjective)
      hcard hTY' hcomm' hne hcenter ?_
    · intro K hK hYK
      let := hK
      let : Group.IsSolvable (K.map H.subtype) :=
        Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective K)
      have hle : Y0 ⊔ T ≤ K.map H.subtype := by
        have hm := map_mono (f := H.subtype) hYK
        rwa [hjoin, map_subgroupOf_eq_of_le (sup_le hYH hTH)] at hm
      exact (map_le_iff_le_comap).mp (hj _ inferInstance hle (map_subtype_le K))
    · intro y
      obtain ⟨l, hl⟩ := hinner y
      exact ⟨l, MulEquiv.ext (fun x => Subtype.ext (hl x))⟩
  have hm := map_mono (f := H.subtype) hle
  rwa [map_subgroupOf_eq_of_le hYH, map_subgroupOf_eq_of_le hL0H] at hm

private theorem image_card_not_dvd_nine {D : Type*} [Group D] (f : G →* D) (Y : Subgroup G)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) : ¬ 9 ∣ Nat.card (Y.map f) := by
  intro hd
  have hdY : 9 ∣ Nat.card Y := hd.trans (Y.card_map_dvd f)
  have he : Nat.card (pCore 2 Y) * 3 = Nat.card Y := by
    simpa only [Subgroup.index, hY] using (pCore 2 Y).card_mul_index
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  have hc : Nat.Coprime 9 (Nat.card (pCore 2 Y)) := by
    rw [hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  rw [← he] at hdY
  exact (by decide : ¬ 9 ∣ 3) (hc.dvd_of_dvd_mul_left hdY)

theorem invariant_solvable_theta_le_starImage (H M Y T : Subgroup G)
    [Group.IsSolvable (Y ⊔ T : Subgroup G)]
    (hYH : Y ≤ H) (hTH : T ≤ H) (hθ : theta (M ⊓ H) = Y)
    (hj : ∀ K : Subgroup G, Group.IsSolvable K →
      Y ⊔ T ≤ K → K ≤ H → K ≤ M ⊓ H)
    (P : Subgroup (H ⧸ pCore 2 H)) [Group.IsSolvable P]
    (hn : starImage H (Y ⊔ T) ≤ normalizer (P : Set (H ⧸ pCore 2 H))) :
    theta P ≤ starImage H Y := by
  let Y' := Y.subgroupOf H
  let T' := T.subgroupOf H
  have hjoin : Y' ⊔ T' = (Y ⊔ T).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hYH, map_subgroupOf_eq_of_le hTH,
      map_subgroupOf_eq_of_le (sup_le hYH hTH)]
  let : Group.IsSolvable (Y' ⊔ T' : Subgroup H) := by
    rw [hjoin]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (sup_le hYH hTH)).toMonoidHom)
      (subgroupOfEquivOfLe (sup_le hYH hTH)).injective
  have hθ' : theta ((M ⊓ H).subgroupOf H) = Y' := by
    apply map_injective H.subtype_injective
    rw [theta_map_of_injective _ H.subtype_injective,
      map_subgroupOf_eq_of_le inf_le_right, hθ, map_subgroupOf_eq_of_le hYH]
  apply ModelReduction.invariant_solvable_theta_le_image (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    ((M ⊓ H).subgroupOf H) Y' T' hθ' ?_ P ?_
  · intro K hK hYK
    let := hK
    let : Group.IsSolvable (K.map H.subtype) :=
      Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective K)
    have hle : Y ⊔ T ≤ K.map H.subtype := by
      have hm := map_mono (f := H.subtype) hYK
      rwa [hjoin, map_subgroupOf_eq_of_le (sup_le hYH hTH)] at hm
    exact (map_le_iff_le_comap).mp (hj _ inferInstance hle (map_subtype_le K))
  · simpa only [hjoin, starImage] using hn


namespace Input
variable {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

/-- The terminal step of (k), once the preceding model analysis has made
Y₀'s action on the centerless component closure inner. -/
theorem y_le_closure_of_inner
    (hcenter : center (starImage H (localSpan L T)) = ⊥)
    (hinner : ∀ y : starImage H Y0, ∃ l : starImage H (localSpan L T),
      ∀ x : starImage H (localSpan L T),
        (l : H ⧸ pCore 2 H) * x * l⁻¹ = y * x * y⁻¹) :
    Y0 ≤ localSpan L T := by
  let := d.base_solvable
  exact containment_of_inner_action H M Y0 L T d.replacement d.placed.theta_eq
    d.overgroups d.placed.toLocalInput.twoPerfect d.quotient_card_in d.normalizes
    d.component.commutator_eq d.closure_star_ne_bot hcenter hinner

/-- Universal (j) controls the cubic generators without solvability of M ∩ H. -/
theorem invariant_theta_le (P : Subgroup (H ⧸ pCore 2 H)) [Group.IsSolvable P]
    (hn : starImage H (Y0 ⊔ T) ≤ normalizer (P : Set (H ⧸ pCore 2 H))) :
    theta P ≤ starImage H Y0 := by
  let := d.base_solvable
  exact invariant_solvable_theta_le_starImage H M Y0 T d.y_le d.t_le
    d.placed.theta_eq d.overgroups P hn

/-- The full image Y₀* may have a two-core, but nine cannot divide its order. -/
theorem no_cubic_envelope (P : Subgroup (H ⧸ pCore 2 H)) [Group.IsSolvable P]
    (htheta : theta P = P)
    (hn : starImage H (Y0 ⊔ T) ≤ normalizer (P : Set (H ⧸ pCore 2 H)))
    (hP : 9 ∣ Nat.card P) : False := by
  have hPY := d.invariant_theta_le P hn
  rw [htheta] at hPY
  exact image_card_not_dvd_nine (QuotientGroup.mk' (pCore 2 H))
    (Y0.subgroupOf H) d.quotient_card_in (hP.trans (card_dvd_of_le hPY))

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
