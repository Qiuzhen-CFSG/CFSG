module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.InvariantProjection
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# The cubic obstruction to a nontrivial component orbit

Universal (j) and θ(M ∩ H) = Y₀ put the cubic generators of every invariant
solvable subgroup of H/O₂(H) in Y₀*. The source equality
|Y₀/O₂(Y₀)| = 3 implies that nine does not divide the order of any image
of Y₀: its order divides three times a power of two. Thus an invariant
solvable subgroup P with θ(P) = P and nine dividing |P| is impossible.
This applies to the product of two cubic projections even when that
product has a nontrivial two-core.

LocalControl records genuine earlier local hypotheses and (j), without a
component-closure or parabolic conclusion. Constructing the invariant
solvable envelope from a putative L₃(2) component orbit remains a separate
step. This file does not assert the completed source (l).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144,
the application of (j) and (b) immediately before clause (l).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels
variable {G D : Type*} [Group G] [Finite G] [Group D]

private theorem image_card_not_dvd_nine (f : G →* D) (Y : Subgroup G)
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

/-- The local control hypotheses of (b) and (j), with their actual quotient. -/
structure LocalControl (H M Y T : Subgroup G) : Prop where
  sylow : IsSylowIn 2 T H
  t_le_m : T ≤ M
  solvable_intersection : Group.IsSolvable (M ⊓ H : Subgroup G)
  theta_eq : theta (M ⊓ H) = Y
  normalizer_eq : normalizer (Y : Set G) = M
  normalizes : T ≤ normalizer (Y : Set G)
  twoPerfect : IsPPerfect 2 Y
  quotient_card : Nat.card (Y ⧸ pCore 2 Y) = 3
  overgroups : ∀ K : Subgroup G, Group.IsSolvable K →
    Y ⊔ T ≤ K → K ≤ H → K ≤ M ⊓ H

/-- Universal (j) forces the cubic generators of an invariant solvable star subgroup into Y₀*. -/
theorem invariant_solvable_theta_le_starImage (H M Y T : Subgroup G)
    (c : LocalControl H M Y T)
    (P : Subgroup (H ⧸ pCore 2 H)) [Group.IsSolvable P]
    (hn : starImage H (Y ⊔ T) ≤ normalizer (P : Set (H ⧸ pCore 2 H))) :
    theta P ≤ starImage H Y := by
  have hYH : Y ≤ H := (c.theta_eq ▸ theta_le _).trans inf_le_right
  have hTH : T ≤ H := (isSylowIn_iff.mp c.sylow).2.1
  have hYM : Y ≤ M := (c.theta_eq ▸ theta_le _).trans inf_le_left
  let Y' := Y.subgroupOf H
  let T' := T.subgroupOf H
  have hjoin : Y' ⊔ T' = (Y ⊔ T).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hYH, map_subgroupOf_eq_of_le hTH,
      map_subgroupOf_eq_of_le (sup_le hYH hTH)]
  let := c.solvable_intersection
  let : Group.IsSolvable (Y ⊔ T : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (sup_le (le_inf hYM hYH) (le_inf c.t_le_m hTH)))
  let : Group.IsSolvable (Y' ⊔ T' : Subgroup H) := by
    rw [hjoin]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (sup_le hYH hTH)).toMonoidHom)
      (subgroupOfEquivOfLe (sup_le hYH hTH)).injective
  have hθ' : theta ((M ⊓ H).subgroupOf H) = Y' := by
    apply map_injective H.subtype_injective
    rw [theta_map_of_injective _ H.subtype_injective,
      map_subgroupOf_eq_of_le inf_le_right, c.theta_eq, map_subgroupOf_eq_of_le hYH]
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
    exact (map_le_iff_le_comap).mp (c.overgroups _ inferInstance hle (map_subtype_le K))
  · simpa only [hjoin, starImage] using hn

/-- An invariant solvable cubic envelope of order divisible by nine contradicts the source quotient of Y₀. -/
theorem no_invariant_solvable_cubic_product_star (H M Y T : Subgroup G)
    (c : LocalControl H M Y T)
    (P : Subgroup (H ⧸ pCore 2 H)) [Group.IsSolvable P]
    (htheta : theta P = P)
    (hn : starImage H (Y ⊔ T) ≤ normalizer (P : Set (H ⧸ pCore 2 H)))
    (hP : 9 ∣ Nat.card P) : False := by
  have hYH : Y ≤ H := (c.theta_eq ▸ theta_le _).trans inf_le_right
  have hPY := invariant_solvable_theta_le_starImage H M Y T c P hn
  rw [htheta] at hPY
  let e := subgroupOfEquivOfLe hYH
  have he := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hc : Nat.card ((Y.subgroupOf H) ⧸ pCore 2 (Y.subgroupOf H)) = 3 :=
    (Nat.card_congr he.toEquiv).trans c.quotient_card
  exact image_card_not_dvd_nine (QuotientGroup.mk' (pCore 2 H)) (Y.subgroupOf H) hc
    (hP.trans (card_dvd_of_le hPY))


end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels
