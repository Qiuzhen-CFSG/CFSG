module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.Setup

/-!
# Odd primes in the literal fixed subgroup

The fixed subgroup lies in H, whose original quotient by O₂(H) is S₅;
therefore seven does not divide its order. Its two-residual is K, whose
image in that same quotient is A₅, so five does divide its order.
These facts are the actual source inputs to the M₁₂, M₂₂ and J₄
centralizer comparisons; they do not assert those model calculations.

Source: Aschbacher–Smith 14.7.63 and 14.7.68(2), printed pp.1069 and 1071.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

include d in
/-- The actual residual has the A₅ image in the original H/O₂(H). -/
theorem five_dvd_card_K : 5 ∣ Nat.card (K F) := by
  have hd := (((K F).subgroupOf F.H).card_map_dvd d.qH)
  rw [d.K_image, Nat.card_congr (subgroupOfEquivOfLe (K_le_H F)).toEquiv] at hd
  have h5 : 5 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  exact h5.trans hd

include d in
/-- The exact S₅ quotient excludes seven from H. -/
theorem not_seven_dvd_card_H : ¬ 7 ∣ Nat.card F.H := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := F.H)).exists_card_eq
  have hi : (pCore 2 F.H).index = 120 := by
    rw [index_eq_card, Nat.card_congr d.model.toEquiv]
    change Nat.card (Equiv.Perm (Fin 5)) = 120
    rw [Nat.card_perm, Nat.card_fin]
    decide
  rw [← (pCore 2 F.H).card_mul_index, hn, hi]
  intro hd
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp hd with hp | hc
  · have h := (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 7)) hp
    norm_num at h
  · norm_num at hc

/-- Every fixed subgroup in this source configuration has a factor of five. -/
theorem five_dvd_card_fixedComponent_fixedSubgroup (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u) (hKLu : K F ≤ Lu)
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
    (ha : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
      ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹) :
    5 ∣ Nat.card α.fixedSubgroup := by
  have hr : 5 ∣ Nat.card (MulAut.embeddedFixedResidual 2 α) := by
    rw [Nat.card_congr (d.fixedComponentResidualEquiv u hLu hKLu α ha).toEquiv]
    exact d.five_dvd_card_K
  have he : Nat.card (MulAut.embeddedFixedResidual 2 α) =
      Nat.card (pResidual 2 α.fixedSubgroup) := by
    exact card_map_of_injective α.fixedSubgroup.subtype_injective
  rw [he] at hr
  exact hr.trans (pResidual 2 α.fixedSubgroup).card_subgroup_dvd_card

/-- Seven cannot occur in the same fixed subgroup, using its actual inclusion. -/
theorem not_seven_dvd_card_fixedComponent_fixedSubgroup (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
    (ha : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
      ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹) :
    ¬ 7 ∣ Nat.card α.fixedSubgroup := by
  have he := card_map_of_injective (d.fixedComponentInclusion_injective u Lu)
    (K := α.fixedSubgroup)
  rw [d.fixedComponent_fixedSubgroup_image u hLu α ha] at he
  have hd : Nat.card (Lu ⊓ centralizer ({d.z} : Set G) : Subgroup G) ∣ Nat.card F.H :=
    card_dvd_of_le (by rw [d.centralizer_eq]; exact inf_le_right)
  rw [he] at hd
  exact fun h => d.not_seven_dvd_card_H (h.trans hd)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
