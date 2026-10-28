module
public import Theory.GroupTheory.PResidual.PermutingPrimeLift
/-!
# Lifting a normal prime subgroup with a prescribed Sylow subgroup

A normal subgroup of odd prime order in a finite quotient has a prime-group
lift permuting with any prescribed Sylow two-subgroup of the original group.
Restrict the quotient to the join of the prime subgroup and the Sylow image.
Its two-residual is exactly that prime subgroup, so the permuting residual-lift
theorem applies to the full preimage. No solvability of the original group or
its quotient kernel is required.

Source application: Aschbacher--Smith 15.1.23, printed p.1100. This constructs
the five-group actor even if the full marked-centralizer residual has order
fifteen; the prime subgroup is not identified with that larger residual.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

/-- A normal odd prime subgroup of a quotient lifts to a prime subgroup
permuting with a prescribed Sylow two-subgroup. -/
theorem exists_permuting_normal_prime_lift
    (f : G →* Q) (hf : Function.Surjective f) (S : Sylow 2 G)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (P : Subgroup Q) [P.Normal] (hP : Nat.card P = p) :
    ∃ Y : Subgroup G, IsPGroup p Y ∧ IsPPerfect 2 Y ∧
      (S : Set G) * (Y : Set G) = (Y : Set G) * (S : Set G) ∧
      Y.map f = P ∧ Y ≤ pResidual 2 G := by
  let B := (S : Subgroup G).map f
  let H := P ⊔ B
  let PH := P.subgroupOf H
  let BH := B.subgroupOf H
  let q := QuotientGroup.mk' PH
  have hPH : Nat.card PH = p :=
    (Nat.card_congr (subgroupOfEquivOfLe (show P ≤ H from le_sup_left)).toEquiv).trans hP
  have hgen : PH ⊔ BH = ⊤ := by
    rw [←subgroupOf_sup (show P ≤ H from le_sup_left) (show B ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hPHq : PH.map q = ⊥ := by
    rw [map_eq_bot_iff,QuotientGroup.ker_mk']
  have hBHq : BH.map q = ⊤ := by
    have he := congrArg (map q) hgen
    rw [Subgroup.map_sup,hPHq,bot_sup_eq,map_top_of_surjective q
      (QuotientGroup.mk'_surjective PH)] at he
    exact he
  have hBtwo : IsPGroup 2 BH := (S.isPGroup'.map f).of_equiv
    (subgroupOfEquivOfLe (show B ≤ H from le_sup_right)).symm
  have hquot : IsPGroup 2 (H ⧸ PH) :=
    (hBHq ▸ hBtwo.map q).of_equiv Subgroup.topEquiv
  have hres : pResidual 2 H = PH := by
    refine le_antisymm (show pResidual 2 H ≤ PH from sInf_le ⟨inferInstance,hquot⟩) ?_
    intro x hx
    apply mem_pResidual_of_orderOf_coprime
    have hcard : orderOf (⟨x,hx⟩ : PH) ∣ p := hPH ▸ _root_.orderOf_dvd_natCard (⟨x,hx⟩ : PH)
    have ho : orderOf x ∣ p := by
      exact (orderOf_injective PH.subtype PH.subtype_injective (⟨x,hx⟩ : PH)) ▸ hcard
    exact ((Nat.prime_two.coprime_iff_not_dvd).mpr
      (fun hd => hp ((Nat.dvd_prime Fact.out).mp hd |>.resolve_left (by decide)).symm)).of_dvd_right ho
  let A := H.comap f
  have hSA : (S : Subgroup G) ≤ A := by
    intro x hx
    exact (show B ≤ H from le_sup_right) (mem_map_of_mem f hx)
  let a := f.subgroupComap H
  obtain ⟨Y,hY,hperf,hperm,him,hYR⟩ := exists_permuting_prime_residual_lift
    a (f.subgroupComap_surjective_of_surjective H hf) (S.subtype hSA)
    (hres ▸ hPH)
  refine ⟨Y.map A.subtype,hY.map A.subtype,
    hperf.of_surjective (A.subtype.subgroupMap Y) (A.subtype.subgroupMap_surjective Y),?_,?_,
    (map_mono hYR).trans (map_pResidual_le 2 A.subtype)⟩
  · have he := congrArg (Set.image A.subtype) hperm
    rw [Set.image_mul,Set.image_mul] at he
    change (((S.subtype hSA : Sylow 2 A) : Subgroup A).map A.subtype : Set G) *
      (Y.map A.subtype : Set G) = (Y.map A.subtype : Set G) *
      (((S.subtype hSA : Sylow 2 A) : Subgroup A).map A.subtype : Set G) at he
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSA] at he
    simpa only [Sylow.coe_coe] using he
  · have he := congrArg (map H.subtype) him
    rw [hres,map_subgroupOf_eq_of_le (show P ≤ H from le_sup_left),map_map] at he
    rw [map_map]
    exact he
end Subgroup
