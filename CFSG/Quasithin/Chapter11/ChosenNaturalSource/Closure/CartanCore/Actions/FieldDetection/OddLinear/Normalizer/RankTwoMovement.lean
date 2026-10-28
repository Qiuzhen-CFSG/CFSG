module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.RankTwo
public import Theory.SpecificGroups.PSL3.BorelCoprimeFieldAction
public import Theory.GroupTheory.OddElementLift

/-!
# PSL₃ Borel movement from the original coprime Cartan actor

The actual quotient actor has a nontrivial coefficient factor. Its odd-order
restriction moves the odd subfield, whose root-torus elements have simultaneous
normalizer lifts. Extract an odd-order power preserving the quotient image.
Trivial movement modulo T would put a nonidentity root-torus element in the
unipotent two-group, a contradiction. The inner and graph factors are retained;
no invariant torus, field actor, or normalizer-lift callback is assumed.

Source: Aschbacher--Smith 11.5.6(3), printed p.781.
-/

public section
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3.CartanActions.RootTorusControl Matrix.PSL3.CartanActions.BorelQuotient
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.RankTwo.Coordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I : Subgroup G}
variable {F : BinaryField} (c : Coordinates T I F)
variable {L V : Subgroup G} {D : ChosenModule T L V} {E : Geometry D}

include c in
/-- The original coprime Cartan actor moves a constructed odd-order
normalizer lift of a root-torus coefficient from the odd subfield. -/
theorem borel_movement
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G)) (hIY : I ≤ E.Y)
    (x : normalizer (I : Set G)) (hxX : (x : G) ∈ E.X)
    (hxS : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G))
    (ho : Odd (Nat.card E.X)) (hc : Nat.Coprime (Nat.card E.X) (Nat.card I))
    (hne : coreQuotientAction I x ≠ 1) : E.BorelMovement := by
  have hα : c.actor x ≠ 1 := by
    intro h
    exact hne ((MulAut.congr c.model).injective (h.trans (map_one _).symm))
  have hd : orderOf (c.actor x) ∣ Nat.card E.X := by
    apply ((orderOf_map_dvd (MulAut.congr c.model).toMonoidHom _).trans
      (orderOf_map_dvd (coreQuotientAction I) x)).trans
    rw [← Subgroup.orderOf_coe x]
    exact E.X.orderOf_dvd_natCard hxX
  have hcop : Nat.Coprime (orderOf (c.actor x)) (Nat.card PSL(3,F.Carrier)) :=
    hc.of_dvd hd (card_dvd_of_surjective c.quotient c.quotient_surjective)
  have hroot := c.actor_preserves_root x hxS
  obtain ⟨m,σ,ε,hσ,hdσ,he⟩ := exists_nontrivial_coefficient F.Carrier F.degree_pos F.card_eq
    (c.actor x) hα (ho.of_dvd_nat hd) hcop hroot
  have hσodd : Odd (orderOf σ) := ho.of_dvd_nat (hdσ.trans hd)
  have hne' := oddRestriction_ne_one F σ hσodd hσ
  have hunits : Odd (Nat.card F.Carrierˣ) := units_odd F.Carrier F.card_eq
  have hdU : Disjoint (unipotent F.Carrier) (rootTorus F.Carrier).range := by
    apply disjoint_of_coprime_natCard
    rw [card_unipotent,F.card_eq,← pow_mul]
    exact (hunits.of_dvd_nat (card_range_dvd (rootTorus F.Carrier))).coprime_two_left.pow_left _
  by_contra hmove
  apply hne'
  have hfix (u : (oddField F).Carrierˣ) :
      Units.map (oddRestriction F σ).toMonoidHom u = u := by
    obtain ⟨b,hbN,hbu⟩ := c.odd_rootTorus_lifts hTI u
    have hbo : Odd (orderOf (c.quotient b)) := by
      rw [hbu]
      exact hunits.of_dvd_nat ((orderOf_map_dvd (rootTorus F.Carrier) _).trans
        (orderOf_dvd_natCard _))
    obtain ⟨r,hr,hro,hre⟩ := c.quotient.exists_odd_power_with_image b hbo
    have hrN : (r : G) ∈ normalizer (T : Set G) := by
      obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hr
      exact (normalizer (T : Set G)).zpow_mem hbN n
    let B : Subgroup G := zpowers (r : G)
    have hBY : B ≤ E.Y := zpowers_le.mpr (hIY r.property)
    have hBN : B ≤ normalizer (T : Set G) := zpowers_le.mpr hrN
    have hBo : Odd (Nat.card B) := by
      rw [Nat.card_zpowers,Subgroup.orderOf_coe r]
      exact hro
    have hcomm : ⁅E.X,B⁆ ≤ (T : Subgroup G) := by
      by_contra hn
      exact hmove ⟨B,hBY,hBN,hBo,hn⟩
    let d : I := I.normalizerMonoidHom x r * r⁻¹
    have hdT : d ∈ (T : Subgroup G).subgroupOf I :=
      hcomm (commutator_mem_commutator hxX (mem_zpowers (r : G)))
    have hdq : c.actor x (c.quotient r) * (c.quotient r)⁻¹ ∈ unipotent F.Carrier := by
      have hh := mem_map_of_mem c.quotient hdT
      rw [c.quotient_sylow_image] at hh
      change c.quotient (I.normalizerMonoidHom x r * r⁻¹) ∈ _ at hh
      rwa [map_mul,map_inv,← c.actor_quotient] at hh
    rw [hre,hbu,he] at hdq
    obtain ⟨v,hv,hve⟩ := actor_rootTorus_factor F.Carrier m σ ε (he ▸ hroot)
      (Units.map (oddInclusion F).toMonoidHom u)
    rw [hve] at hdq
    have ht : rootTorus F.Carrier
        (Units.map σ.toMonoidHom (Units.map (oddInclusion F).toMonoidHom u) *
          (Units.map (oddInclusion F).toMonoidHom u)⁻¹) ∈ unipotent F.Carrier := by
      have hh := (unipotent F.Carrier).mul_mem ((unipotent F.Carrier).inv_mem hv) hdq
      simpa only [map_mul,map_inv,← mul_assoc,inv_mul_cancel,one_mul] using hh
    have ht1 := disjoint_def.mp hdU ht (show rootTorus F.Carrier _ ∈
      (rootTorus F.Carrier).range from ⟨_,rfl⟩)
    have hz := (rootTorus_injective F.Carrier) (ht1.trans (map_one _).symm)
    rw [mul_inv_eq_one] at hz
    apply Units.ext
    apply (oddInclusion F).injective
    change oddInclusion F (oddRestriction F σ u.val) = oddInclusion F u.val
    rw [oddRestriction_apply]
    exact congrArg Units.val hz
  ext z
  by_cases hz : z = 0
  · simp [hz]
  · exact congrArg Units.val (hfix (Units.mk0 z hz))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.RankTwo.Coordinates
