module

public import Theory.Representation.BinaryConjugationSection.Canonical
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Faithful action through the actual section kernel

Conjugation on U/Z descends through a surjective actor map whose kernel is
exactly the pointwise section kernel. The descended binary representation
is faithful and keeps the literal quotient coordinates. This is the
actual-action bridge for Aschbacher--Smith13.7.12(3), printed p.942.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G D:Type*} [Group G] [Group D]
/-- Construct the literal binary section through its actual conjugation kernel. -/
theorem exists_faithful_quotient_actor
    (H U Z:Subgroup G) (hUH:U≤H) (hZU:Z≤U)
    (hNU:H≤normalizer (U:Set G)) (hNZ:H≤normalizer (Z:Set G))
    [(Z.subgroupOf U).Normal] [IsElementaryAbelian 2 (U⧸Z.subgroupOf U)]
    (π:H→*D) (hπ:Function.Surjective π)
    (hk:∀a:H,π a=1 ↔ ∀u∈U,⁅(a:G),u⁆∈Z) :
    ∃ (σ:Representation (ZMod 2) D (Additive (U⧸Z.subgroupOf U)))
      (c:BinaryConjugationSection H U Z (σ.comp π)),
      Function.Injective σ ∧
      ∀u:U,(c.coordinates u).toAdd=Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) := by
  let Q:=U⧸Z.subgroupOf U
  let q:=QuotientGroup.mk' (Z.subgroupOf U)
  obtain ⟨α,hα⟩:=exists_quotient_conjugation_action H U Z hNU hNZ inferInstance
  have hker:∀a:H,α a=1 ↔ π a=1 := by
    intro a
    rw [hk]
    constructor
    · intro ha u hu
      have he:=congrArg (fun f:MulAut Q=>f (q ⟨u,hu⟩)) ha
      rw [hα] at he
      change q _=q ⟨u,hu⟩ at he
      have hm:=QuotientGroup.eq_iff_div_mem.mp he
      change (a:G)*u*(a:G)⁻¹/u∈Z at hm
      simpa only [div_eq_mul_inv,commutatorElement_def] using hm
    · intro ha
      apply MulEquiv.ext
      intro w
      obtain ⟨u,rfl⟩:=QuotientGroup.mk'_surjective (Z.subgroupOf U) w
      rw [hα]
      change q _=q u
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (a:G)*(u:G)*(a:G)⁻¹/(u:G)∈Z
      simpa only [div_eq_mul_inv,commutatorElement_def] using ha u u.property
  have hkill:π.ker≤α.ker:=fun a ha=>(hker a).mpr ha
  let β:D→*MulAut Q:=π.liftOfSurjective hπ ⟨α,hkill⟩
  have hβ(a:H):β (π a)=α a:=π.liftOfRightInverse_comp_apply (Function.surjInv hπ)
    (Function.rightInverse_surjInv hπ) ⟨α,hkill⟩ a
  let σ:Representation (ZMod 2) D (Additive Q):={
    toFun a:=(β a).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one':=by ext v;change β 1 v.toMul=v.toMul;rw [map_one];rfl
    map_mul' a b:=by ext v;change β (a*b) v.toMul=β a (β b v.toMul);rw [map_mul];rfl }
  let cU:U→*Multiplicative (Additive Q):={
    toFun u:=Multiplicative.ofAdd (Additive.ofMul (q u))
    map_one':=q.map_one
    map_mul':=q.map_mul }
  let c:BinaryConjugationSection H U Z (σ.comp π):={
    section_le:=hUH
    kernel_le:=hZU
    normalized:=hNU
    coordinates:=cU
    onto:=QuotientGroup.mk'_surjective _
    kernel_eq:=QuotientGroup.ker_mk' _
    equivariant:=by
      intro a u
      change q _=β (π a) (q u)
      rw [hβ]
      exact (hα a u).symm }
  refine ⟨σ,c,?_,fun _=>rfl⟩
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨b,rfl⟩:=hπ a
  have he:β (π b)=1 := by
    apply MulEquiv.ext
    intro w
    have hh:=congrArg (fun f:Module.End (ZMod 2) (Additive Q)=>f (Additive.ofMul w)) ha
    exact hh
  exact (hker b).mp ((hβ b).symm.trans he)
end Representation.BinaryConjugationSection
