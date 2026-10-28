module

public import Theory.GroupTheory.QuaternionCentralProductCenter
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

/-!
# Commutators and centralizers in a quaternion central supplement

Let B be a quaternion group of order eight and let U commute with B,
with |B ∩ U| = 2. For h in BU outside U, the subgroup [⟨h⟩, B]
is precisely B ∩ U. If U is commutative, C_{BU}(h) = ⟨h⟩U.

Write h = bu and use the actual quaternion isomorphism on B. Three small
kernel-checked tables give the cyclic centralizer of a noncentral quaternion
element, its full central commutator image, and centrality of all commutators.
The proofs transport the elements and their powers back to the ambient group.

Source: the central-product step in Aschbacher–Smith, Lemma J.2.4,
combined manuscript of 1 March 2004, printed p.434 (PDF p.445).
-/

public section

open Subgroup
open scoped Pointwise commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem quaternion_centralizer (a b : QuaternionGroup 2)
    (ha : ¬ ∀ c, c * a = a * c) (hab : a * b = b * a) :
    ∃ n : Fin 4, b = a ^ (n : ℕ) := by
  revert a b
  decide

private theorem quaternion_commutator (a z : QuaternionGroup 2)
    (ha : ¬ ∀ c, c * a = a * c) (hz : ∀ c, c * z = z * c) :
    ∃ b, ⁅a,b⁆ = z := by
  revert a z
  decide

private theorem quaternion_commutator_central (a b : QuaternionGroup 2) :
    ∀ c, c * ⁅a,b⁆ = ⁅a,b⁆ * c := by
  revert a b
  decide

variable (B U : Subgroup G) (e : B ≃* QuaternionGroup 2)
    (hi : Nat.card (B ⊓ U : Subgroup G) = 2)
    (hc : B ≤ centralizer (U : Set G))

omit [Finite G] in
include hc in
private theorem decomp {h : G} (hh : h ∈ B ⊔ U) :
    ∃ b ∈ B, ∃ u ∈ U, b*u=h := by
  change h ∈ (↑(B ⊔ U) : Set G) at hh
  rw [coe_mul_of_left_le_normalizer_right B U
    (hc.trans (centralizer_le_normalizer _))] at hh
  exact hh

include hi hc in
private theorem factor_not_central {b u : G} (hb : b ∈ B) (hu : u ∈ U)
    (hn : b*u ∉ U) : ¬ ∀ c, c * e ⟨b,hb⟩ = e ⟨b,hb⟩ * c := by
  intro hz
  have hbcenter : (⟨b,hb⟩ : B) ∈ center B := by
    apply mem_center_iff.mpr
    intro c
    apply e.injective
    simpa only [map_mul] using hz (e c)
  have hbU : b ∈ B ⊓ U := by
    rw [intersection_eq_factor_center B U ⟨e⟩ hi (fun b hb u hu => (hc hb u hu).symm)]
    exact mem_map.mpr ⟨⟨b,hb⟩,hbcenter,rfl⟩
  exact hn (U.mul_mem hbU.2 hu)

include e hi hc in
/-- In a central product of a quaternion eight and a commutative supplement,
the centralizer of an element outside the supplement is its cyclic subgroup
joined with the supplement. -/
theorem centralizer_quaternion_product [IsMulCommutative U]
    {h : G} (hh : h ∈ B ⊔ U) (hn : h ∉ U) :
    (B ⊔ U) ⊓ centralizer ({h} : Set G) = zpowers h ⊔ U := by
  obtain ⟨b,hb,u,hu,rfl⟩ := decomp B U hc hh
  have hb0 := factor_not_central B U e hi hc hb hu hn
  have hU : U ≤ centralizer ((B ⊔ U : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr (sup_le hc U.le_centralizer)
  apply le_antisymm
  · intro x hx
    obtain ⟨c,hcB,v,hv,rfl⟩ := decomp B U hc hx.1
    have hbc : b*c=c*b := by
      have hh := mem_centralizer_singleton_iff.mp hx.2
      have huC := (hc hcB u hu).symm
      have hbV := (hc hb v hv).symm
      have huv := (hU hu v (mem_sup_right hv)).symm
      have he : (c*b)*(v*u)=(b*c)*(v*u) := by
        calc
          (c*b)*(v*u) = (c*v)*(b*u) := by
            calc
              _ = c*(b*v)*u := by group
              _ = c*(v*b)*u := by rw [hbV]
              _ = _ := by group
          _ = (b*u)*(c*v) := hh
          _ = (b*c)*(v*u) := by
            calc
              _ = b*(u*c)*v := by group
              _ = b*(c*u)*v := by rw [← huC]
              _ = (b*c)*(u*v) := by group
              _ = _ := by rw [huv]
      exact (mul_right_cancel he).symm
    obtain ⟨n,hnpow⟩ := quaternion_centralizer (e ⟨b,hb⟩) (e ⟨c,hcB⟩) hb0
      (by simpa only [map_mul] using congrArg e (show (⟨b,hb⟩ : B)*⟨c,hcB⟩ =
        ⟨c,hcB⟩*⟨b,hb⟩ from Subtype.ext hbc))
    have hcG : c = b ^ (n : ℕ) := congrArg Subtype.val
      (e.injective (hnpow.trans (map_pow e _ _).symm))
    have hbu : Commute b u := (hc hb u hu).symm
    have hm : c*v = (b*u)^(n : ℕ) * ((u^(n : ℕ))⁻¹ * v) := by
      rw [hcG, hbu.mul_pow]
      group
    rw [hm]
    exact (zpowers (b*u) ⊔ U).mul_mem
      (mem_sup_left (pow_mem (mem_zpowers _) _))
      (mem_sup_right (U.mul_mem (U.inv_mem (U.pow_mem hu _)) hv))
  · apply sup_le
    · exact zpowers_le.mpr ⟨mul_mem (mem_sup_left hb) (mem_sup_right hu),
        mem_centralizer_singleton_iff.mpr rfl⟩
    · exact le_inf le_sup_right (fun x hx => mem_centralizer_singleton_iff.mpr
        (hU hx (b*u) (mul_mem (mem_sup_left hb) (mem_sup_right hu))).symm)

include e hi hc in
/-- Every central quaternion element is a commutator with a prescribed
noncentral element, including after multiplying it by the commuting supplement. -/
theorem commutator_quaternion_product {h : G} (hh : h ∈ B ⊔ U) (hn : h ∉ U) :
    ⁅zpowers h, B⁆ = B ⊓ U := by
  have hiC := intersection_eq_factor_center B U ⟨e⟩ hi (fun b hb u hu => (hc hb u hu).symm)
  obtain ⟨b,hb,u,hu,rfl⟩ := decomp B U hc hh
  have hb0 := factor_not_central B U e hi hc hb hu hn
  have hbu : Commute b u := (hc hb u hu).symm
  have hcomm (n : ℤ) (c : G) (hcB : c ∈ B) :
      ⁅(b*u)^n,c⁆ = ⁅b^n,c⁆ := by
    rw [hbu.mul_zpow]
    have hh : Commute (u^n) c := (show Commute u c from hc hcB u hu).zpow_left n
    simp only [commutatorElement_def, mul_inv_rev]
    rw [mul_assoc (b^n) (u^n) c, hh.eq]
    group
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha c hcB
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp ha
    rw [hcomm n c hcB, hiC]
    refine mem_map.mpr ⟨⁅(⟨b,hb⟩ : B)^n,⟨c,hcB⟩⁆, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro d
    apply e.injective
    simpa only [map_mul, map_commutatorElement] using
      quaternion_commutator_central (e ((⟨b,hb⟩ : B)^n)) (e ⟨c,hcB⟩) (e d)
  · intro z hz
    have hzC : (⟨z,hz.1⟩ : B) ∈ center B := by
      have hz' : z ∈ (center B).map B.subtype := hiC ▸ hz
      obtain ⟨x,hx,he⟩ := hz'
      exact (show x = ⟨z,hz.1⟩ from Subtype.ext he) ▸ hx
    have hze : ∀ c, c * e ⟨z,hz.1⟩ = e ⟨z,hz.1⟩ * c := by
      intro c
      simpa only [map_mul, e.apply_symm_apply] using
        congrArg e (mem_center_iff.mp hzC (e.symm c))
    obtain ⟨c,hcc⟩ := quaternion_commutator (e ⟨b,hb⟩) (e ⟨z,hz.1⟩) hb0 hze
    let cB := e.symm c
    have heB : ⁅(⟨b,hb⟩ : B),cB⁆ = ⟨z,hz.1⟩ := by
      apply e.injective
      simpa only [map_commutatorElement, e.apply_symm_apply, cB] using hcc
    have he : ⁅b,(cB : G)⁆ = z := congrArg Subtype.val heB
    have hh : ⁅b*u,(cB : G)⁆ = z := by simpa only [zpow_one] using (hcomm 1 cB cB.property) |>.trans (by simpa using he)
    exact hh ▸ commutator_mem_commutator (mem_zpowers _) cB.property
end Subgroup
