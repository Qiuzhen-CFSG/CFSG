module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Concrete marks in SL₃(2) × S₃

The residual and Borel generate the point parabolic. Its two-core is the
same translation four-group as the core of its residual: commutators with
a cubic Levi element force a core element into that residual. Together
with the transposition subgroup of S₃, these calculations identify the
Sylow subgroup and all intrinsic cores needed in the covered product.

Source: Aschbacher–Smith, 13.8.21(1), printed p.957.
-/

@[expose] public section
open Subgroup
namespace Matrix.PSL3Two.MarkedProduct
open MarkedAutomorphisms

/-- The second Sylow mark is tied to the literal transposition. -/
def R : Subgroup (Equiv.Perm (Fin 3)) := zpowers (Equiv.swap (1 : Fin 3) 2)

theorem card_R : Nat.card R = 2 := by
  rw [R, Nat.card_zpowers]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem R_isPGroup : IsPGroup 2 R := IsPGroup.of_card (n := 1) card_R

theorem borel_isPGroup : IsPGroup 2 borelSL := IsPGroup.of_card (n := 3) card_borelSL

/-- The Borel and the marked transposition form a Sylow subgroup of the product. -/
noncomputable def productSylow : Sylow 2 (SL × Equiv.Perm (Fin 3)) :=
  Sylow.ofCard (borelSL.prod R) (by
    rw [Nat.card_congr (prodEquiv borelSL R).toEquiv, Nat.card_prod, card_borelSL,
      card_R, Nat.card_prod, card_SL]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    decide +kernel)

/-- The point residual and its actual Borel supplement generate the point parabolic. -/
theorem residual_sup_borel : residual pointParabolicSL ⊔ borelSL = pointParabolicSL := by
  have hB : borelSL ≤ pointParabolicSL := inf_le_left
  let S : Sylow 2 pointParabolicSL := Sylow.ofCard (borelSL.subgroupOf pointParabolicSL) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv, card_borelSL, card_pointParabolicSL]
    decide +kernel)
  have he := congrArg (fun B : Subgroup pointParabolicSL => B.map pointParabolicSL.subtype)
    (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  change residual pointParabolicSL ⊔
    (borelSL.subgroupOf pointParabolicSL).map pointParabolicSL.subtype = _ at he
  rwa [map_subgroupOf_eq_of_le hB] at he

/-- The same residual/Sylow supplement identifies the whole second factor. -/
theorem alternating_sup_R : alternatingGroup (Fin 3) ⊔ R = ⊤ := by
  let S : Sylow 2 (Equiv.Perm (Fin 3)) := Sylow.ofCard R (by
    rw [card_R]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    decide +kernel)
  simpa only [S, Sylow.coe_ofCard, Equiv.Perm.twoResidual_eq_alternating] using pResidual_sup_sylow_eq_top S

/-- The parabolic core is the actual translation four-group. -/
theorem pointParabolic_core : pointParabolicSL.pCoreIn 2 = pointV := by
  have hrestrict : pointA ⊓ pointParabolicSL.pCoreIn 2 ≤ pointV := by
    rw [← point_core]
    exact inf_pCoreIn_le_of_le 2 pointA_le
  apply le_antisymm
  · rintro g ⟨x,hx,rfl⟩
    have hxcore : x.val ∈ pointParabolicSL.pCoreIn 2 := ⟨x,hx,rfl⟩
    have hcA : x.val * cubic * x.val⁻¹ * cubic⁻¹ ∈ pointA :=
      pointA.mul_mem (pointA_conj x x.property cubic cubic_mem) (pointA.inv_mem cubic_mem)
    let c : pointParabolicSL := ⟨cubic,pointA_le cubic_mem⟩
    have hcN : x * c * x⁻¹ * c⁻¹ ∈ pCore 2 pointParabolicSL := by
      have h := (pCore 2 pointParabolicSL).mul_mem hx
        ((inferInstance : (pCore 2 pointParabolicSL).Normal).conj_mem x⁻¹
          ((pCore 2 pointParabolicSL).inv_mem hx) c)
      simpa only [mul_assoc] using h
    have hcV : x.val * cubic * x.val⁻¹ * cubic⁻¹ ∈ pointV :=
      hrestrict ⟨hcA,⟨x*c*x⁻¹*c⁻¹,hcN,rfl⟩⟩
    exact hrestrict ⟨quotient_fixer_test x x.property hcV,hxcore⟩
  · rw [← point_core]
    apply pCoreIn_mono_of_normalizes pointA_le
    exact le_normalizer_iff.mpr pointA_conj

theorem symmetric_core : (⊤ : Subgroup (Equiv.Perm (Fin 3))).pCoreIn 2 = ⊥ := by
  have h := ker_eq_twoCore_of_surjective_perm_three
    (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id
    (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
  have he : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by simpa only [MonoidHom.ker_id] using h.symm
  exact (pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm (Fin 3))) ≃* _)).trans he

/-- The residual core survives in the first factor. -/
theorem residual_product_core :
    ((residual pointParabolicSL).prod (⊥ : Subgroup (Equiv.Perm (Fin 3)))).pCoreIn 2 =
      pointV.prod ⊥ := by
  rw [pCoreIn_prod, point_residual, point_core,
    pCoreIn_eq_self_of_isPGroup 2 ⊥ (IsPGroup.of_subsingleton 2 _)]

theorem sylow_product_core : (borelSL.prod R).pCoreIn 2 = borelSL.prod R :=
  pCoreIn_eq_self_of_isPGroup 2 _ productSylow.isPGroup'

theorem point_sylow_product_core : (pointParabolicSL.prod R).pCoreIn 2 = pointV.prod R := by
  rw [pCoreIn_prod, pointParabolic_core, pCoreIn_eq_self_of_isPGroup 2 R R_isPGroup]

theorem point_full_product_core :
    (pointParabolicSL.prod (⊤ : Subgroup (Equiv.Perm (Fin 3)))).pCoreIn 2 = pointV.prod ⊥ := by
  rw [pCoreIn_prod, pointParabolic_core, symmetric_core]

end Matrix.PSL3Two.MarkedProduct
