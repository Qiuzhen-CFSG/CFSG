module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.PushingSetup
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin

/-!
# The solvable Fitting-preimage join in the C.2.6 application

A radical two-subgroup contains the original two-core. The Fitting subgroup
above that core has odd order, so the radical is Sylow in its join with the
Fitting preimage. Characteristic two passes from the original group to the
normal preimage and then to the join. This is the literal local setup used
in 15.4.3; no ordered-product conclusion of C.2.6 is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.SolvableCompletion
variable {H : Type*} [Group H] [Finite H]

theorem fitting_preimage_sylow (R : Subgroup H) (hr : IsPRadical 2 R) :
    let F := (fittingSubgroup (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))
    ∃ S : Sylow 2 (F ⊔ R : Subgroup H),
      (S : Subgroup (F ⊔ R : Subgroup H)).map (F ⊔ R : Subgroup H).subtype = R := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let F := (fittingSubgroup (H ⧸ Q)).comap q
  have hQR : Q ≤ R := pCore_le_of_pCore_normalizer_le R hr.isPGroup hr.2.le
  have hQF : Q ≤ F := by
    intro x hx
    change q x ∈ fittingSubgroup (H ⧸ Q)
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  let f : F →* H ⧸ Q := q.comp F.subtype
  have hk : f.ker = Q.subgroupOf F := by
    ext x
    exact QuotientGroup.eq_one_iff (x : H)
  have hrange : f.range = fittingSubgroup (H ⧸ Q) := by
    rw [MonoidHom.range_comp, range_subtype]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) _
  have hfodd : Nat.Coprime 2 (Nat.card (fittingSubgroup (H ⧸ Q))) :=
    (pPrimeCore_coprime_card (p := 2) (G := H ⧸ Q)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2
        (pCore_quotient_pCore_eq_bot 2)))
  have hi : ¬ 2 ∣ (Q.subgroupOf F).index := by
    rw [← hk, index_ker, hrange]
    exact Nat.prime_two.coprime_iff_not_dvd.mp hfodd
  apply IsPGroup.exists_sylow_sup_of_coprime_index F R hr.isPGroup
    le_normalizer_of_normal (Q.subgroupOf F) hi
  rw [map_subgroupOf_eq_of_le hQF]
  exact hQR

theorem fitting_preimage_join_characteristicTwo (R : Subgroup H)
    (hr : IsPGroup 2 R) (hc : HasCharacteristicTwo H) :
    let F := (fittingSubgroup (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))
    HasCharacteristicTwo (F ⊔ R : Subgroup H) := by
  let F := (fittingSubgroup (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))
  have hF : centralizer (pCore 2 F : Set F) ≤ pCore 2 F :=
    subnormal_core_selfCentralizing hc F (inferInstance : F.Normal).isSubnormal
  exact centralizer_pCore_sup_le 2 F R hF hr le_normalizer_of_normal

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.SolvableCompletion
