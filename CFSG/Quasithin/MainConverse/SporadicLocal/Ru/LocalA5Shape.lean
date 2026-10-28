module
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core.Center
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core
public import Theory.GroupTheory.SelfCentralizingCoreCenter
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.LocalA5Supplement
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max6Residual

/-!
# The core center of a Sylow-normalized A₅ section in Rudvalis

The full Sylow supplement is max6. The three native generator relations
put its two-core in its two-residual, hence inside the original normalized
subgroup. Self-centralization then embeds the center of that subgroup's
two-core in the center of the max6 two-core, whose order is at most two.
No independent order for the original two-core is required.

Source: Aschbacher–Smith A.3.14(12) and 10.2.9, pp.48–49 and 750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuEven
open Rudvalis Rudvalis.SylowOvergroups

/-- A full Sylow-normalized A₅ section in Rudvalis has small core center,
without a separate core-shape assumption. -/
theorem normalized_a5_core_center_card_le_two (P : Sylow 2 Model) (B : Subgroup Model)
    (hPB : (P : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card (center (pCore 2 B)) ≤ 2 := by
  by_cases hc : pCore 2 B = ⊥
  · have hh := (center (pCore 2 B)).card_le_card_group
    have hh' : Nat.card (pCore 2 B) = 1 := by rw [hc,card_bot]
    omega
  obtain ⟨a,ha,hn⟩ := normalized_a5_max6_placement P B hPB hc eB
  let C := (B.map a.toMonoidHom).subgroupOf max6
  let R := ((P : Subgroup Model).map a.toMonoidHom).subgroupOf max6
  let : C.Normal := hn
  have hp : IsPGroup 2 R := (P.isPGroup'.map a.toMonoidHom).comap_subtype
  have hsup : C ⊔ R = ⊤ := by
    change (B.map a.toMonoidHom).subgroupOf max6 ⊔
      ((P : Subgroup Model).map a.toMonoidHom).subgroupOf max6 = ⊤
    rw [←subgroupOf_sup,←Subgroup.map_sup,ha,subgroupOf_self]
    all_goals rw [←ha]; exact map_mono (by aesop)
  have hr : pResidual 2 max6 ≤ C :=
    (pResidual_le_iff_isPGroup_quotient 2 C).mpr
      (isPGroup_quotient_of_sup_eq_top C R hp hsup)
  have hsmall : Nat.card (center (pCore 2 C)) ≤ 2 :=
    (center_pCore_card_le_of_pCore_le 2 C (CoreQuotients.max6_pCore_le_pResidual.trans hr)
      max6_pCore_selfCentralizing).trans Max6Core.max6_core_center_card_le_two
  have hB : B.map a.toMonoidHom ≤ max6 := by
    rw [←ha]
    exact map_mono le_sup_left
  let g : B ≃* C := (a.subgroupMap B).trans (subgroupOfEquivOfLe hB).symm
  let eg : pCore 2 B ≃* pCore 2 C :=
    (g.subgroupMap (pCore 2 B)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 g))
  rw [Nat.card_congr (centerCongr eg).toEquiv]
  exact hsmall

end CFSG.Quasithin.MainConverse.SporadicLocal.RuEven
