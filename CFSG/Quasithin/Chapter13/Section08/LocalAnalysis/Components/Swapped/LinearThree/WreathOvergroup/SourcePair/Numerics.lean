module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.SourcePair.Input

/-!
# The order bound in the moving PSL₃(2) branch

The two actual component images have order 168². Their normal product has a
two-group supplement in H*, and H → H* has two-core kernel. The two quotient
order formulas therefore show that 27 does not divide |H|. The source input
also supplies an ambient Sylow subgroup whose restriction gives the literal
Sylow marking of T inside H.

Source: the PSL₃(2) case in Aschbacher–Smith 13.8.16(1), printed p.952.
This arithmetic is independent of the remaining parabolic selection and wreath
quotient calculations; no numerical model consequence is an input.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.SourcePair
variable {G : Type*} [Group G] [Finite G]

/-- A normal star subgroup of order 168² and a two-group supplement
leave no third factor of three, even after lifting through O₂(H). -/
theorem not_twentyseven_dvd_of_star_card (H K₀ T : Subgroup G) (hK : K₀ ≤ H) (hT : T ≤ H)
    (hgen : H = K₀ ⊔ T) (hn : (K₀.subgroupOf H).Normal)
    (htwo : IsPGroup 2 T) (hcard : Nat.card (Source.starImage H K₀) = 168 ^ 2) :
    ¬ 27 ∣ Nat.card H := by
  let A := Source.starImage H K₀
  let B := Source.starImage H T
  let : A.Normal := hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
  have hB : IsPGroup 2 B := htwo.comap_subtype.map _
  have hsup : A ⊔ B = ⊤ := by
    rw [← LinearTwo.starImage_sup H K₀ T hK hT, ← hgen]
    simp only [Source.starImage, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hquot : IsPGroup 2 (Source.Hstar H ⧸ A) :=
    isPGroup_quotient_of_sup_eq_top A B hB hsup
  obtain ⟨n, hn⟩ := hquot.exists_card_eq
  obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hstar := card_eq_card_quotient_mul_card_subgroup A
  have hH := card_eq_card_quotient_mul_card_subgroup (pCore 2 H)
  change Nat.card A = 168 ^ 2 at hcard
  rw [hn, hcard] at hstar
  rw [hstar, hm] at hH
  rw [hH]
  have hcop : Nat.Coprime 27 (2 ^ n * 2 ^ m) := by
    exact ((by decide : Nat.Coprime 27 2).pow_right n).mul_right
      ((by decide : Nat.Coprime 27 2).pow_right m)
  intro h
  have hd : 27 ∣ 168 ^ 2 := hcop.dvd_of_dvd_mul_left (by convert h using 1; ring)
  norm_num at hd


namespace Input
variable {H L₁ T K K₀ : Subgroup G} (d : Input H L₁ T K K₀)
include d

/-- The actual two-component image has order 168². -/
theorem card_star_orbit : Nat.card (Source.starImage H K₀) = 168 ^ 2 := by
  rw [d.orbit_eq]
  exact card_moving_star H K d.component_le d.component d.quasisimple d.model
    (d.T_le d.mover_mem) d.mover_not_normalizes

/-- The numerical bound is derived from the actual factors and supplement. -/
theorem not_twentyseven_dvd_card : ¬ 27 ∣ Nat.card H :=
  not_twentyseven_dvd_of_star_card H K₀ T d.orbit_le d.T_le
    d.generated_by_orbit_T d.orbit_normal d.two d.card_star_orbit

/-- The numerical and intrinsic Sylow outputs consumed by the full-overlap
calculation. Neither is an assumed parabolic or automizer consequence. -/
theorem numerical_outputs : ¬ 27 ∣ Nat.card H ∧
    ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = T :=
  ⟨d.not_twentyseven_dvd_card, d.sylow_marking⟩

end Input
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup.SourcePair
end
