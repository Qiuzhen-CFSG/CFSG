module
public import Theory.GroupTheory.PGroup.SecondCenterCommutator
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Exhaustion by the second center

If a finite two-group has elementary center and Z(Z₂(P))=Z(P), then
Z₂(P)=P. Indeed C_P(Z₂(P))/Z(P) is normal and has trivial intersection
with the center of P/Z(P), hence is trivial. The commutator pairing puts
Φ(P) inside that centralizer, so P′≤Φ(P)≤Z(P).

The upper-module recognition argument in
LinearThreeMS.NonbinarySource.SecondCenterExhaustion supplies this center
identity from nonabelian doubled-dual sections. No class-two hypothesis is
assumed. Source: elementary finite p-group theory applied to the sections
of Aschbacher–Smith C.1.34, pp.136–137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.SecondCenterFrattini
variable {P : Type*} [Group P] [Finite P]
local notation "T₂" => Subgroup.upperCentralSeries P 2

theorem second_eq_top_of_center_eq (hP : IsPGroup 2 P)
    (hc : (center T₂).map (T₂).subtype = center P)
    [IsElementaryAbelian 2 (center P)] : T₂ = ⊤ := by
  let C := centralizer (T₂ : Set P)
  have hzC : center P ≤ C := center_le_centralizer _
  have hCZ : C ⊓ T₂ = center P := by
    rw [←hc]
    ext x
    constructor
    · rintro ⟨hxC,hxT⟩
      exact ⟨⟨x,hxT⟩,mem_center_iff.mpr (fun y => Subtype.ext (hxC y y.property)),rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨fun y hy => congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩),x.property⟩
  have hC : C = center P := by
    apply le_antisymm _ hzC
    let f := QuotientGroup.mk' (center P)
    have ht : T₂ = (center (P ⧸ center P)).comap f := by
      rw [←Subgroup.upperCentralSeries_one (P ⧸ center P),
        Subgroup.comap_upperCentralSeries_quotient_center]
    let : (C.map f).Normal := (inferInstance : C.Normal).map f (QuotientGroup.mk'_surjective _)
    have hbot : (C.map f) = ⊥ := by
      by_contra hn
      have hh := Subgroup.center_inf_ne_bot_of_normal (hP.to_quotient (center P)) (C.map f) hn
      apply hh
      apply bot_unique
      rintro y ⟨hy,hyC⟩
      obtain ⟨x,hx,rfl⟩ := hyC
      have hxT : x∈T₂ := ht ▸ hy
      exact (QuotientGroup.eq_one_iff x).mpr (hCZ ▸ ⟨hx,hxT⟩)
    intro x hx
    have hx0 : f x=1 := by
      have hh := mem_map_of_mem f hx
      rwa [hbot,mem_bot] at hh
    exact (QuotientGroup.eq_one_iff x).mp hx0
  have hPhi : frattini P ≤ center P := by
    rw [←hC]
    exact le_centralizer_iff.mp second_le_frattini_centralizer
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  have hd : _root_.commutator P ≤ center P :=
    (commutator_le_frattini_of_isPGroup (p := 2)).trans hPhi
  apply top_unique
  intro x _
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro y
  rw [Subgroup.upperCentralSeries_one]
  exact hd (commutator_mem_commutator (mem_top x) (mem_top y))
end Theory.GroupTheory.SecondCenterFrattini
