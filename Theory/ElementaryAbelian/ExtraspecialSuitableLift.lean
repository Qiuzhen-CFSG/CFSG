module
public import Theory.ElementaryAbelian.ExtraspecialCommutatorPairing

/-!
# A suitable inner twist over an extraspecial binary quotient

Let Q be a finite extraspecial two-group and C a subgroup containing its
center. An automorphism α fixes the center pointwise and acts trivially
on C modulo the center. Then some inner twist α * conj(r) fixes C
pointwise. No involutivity assumption on α or elementary hypothesis on C
is needed.

The central discrepancy c ↦ α(c)c⁻¹ is a homomorphism on C that kills the
kernel of C → Q/Z(Q). It therefore defines a homomorphism on the image
of C in the elementary binary central quotient. A linear retraction onto
that image extends the homomorphism to Q/Z(Q). Extraspecial commutator
duality represents the extension by [r,-]. Since α fixes the center and
each central element has square one, α * conj(r) cancels the discrepancy.

This is the group-theoretic input for the suitable-representative reading
of Stellmacher (8.6)(c3), printed p.41, approved after the source/action
audit. The native application separately supplies C as the preimage of the
quotient fixed space and its order32; composing conjugations corresponds
to the ambient representative x*r.
-/

open scoped IsMulCommutative commutatorElement
open Subgroup

private theorem binary_hom_extends {X Z : Type*} [Group X] [Group Z]
    [IsElementaryAbelian 2 X] [IsElementaryAbelian 2 Z]
    (H : Subgroup X) (f : H →* Z) :
    ∃ g : X →* Z, ∀ h : H, g h = f h := by
  let _ : IsElementaryAbelian 2 H := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun h =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 X) (h : X)) }
  let inclusion : Additive H →ₗ[ZMod 2] Additive X :=
    H.subtype.toAdditive.toZModLinearMap 2
  have hinj : Function.Injective inclusion := by
    intro x y h
    exact congrArg Additive.ofMul (Subtype.ext (congrArg Additive.toMul h))
  obtain ⟨retraction, hret⟩ := inclusion.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let extension : Additive X →ₗ[ZMod 2] Additive Z :=
    (f.toAdditive.toZModLinearMap 2).comp retraction
  let g : X →* Z := MonoidHom.toAdditive.symm extension.toAddMonoidHom
  refine ⟨g, ?_⟩
  intro h
  have hh := LinearMap.congr_fun hret (Additive.ofMul h)
  exact congrArg (fun v : Additive H => f v.toMul) hh

/-- A central discrepancy on a subgroup of an extraspecial binary group can be removed by an inner twist. -/
public theorem extraspecial_two_exists_inner_twist_fixing_subgroup
    {Q : Type*} [Group Q] [Finite Q] [IsExtraspecial 2 Q]
    (C : Subgroup Q) (_hZC : center Q ≤ C) (α : MulAut Q)
    (hαZ : ∀ z : Q, z ∈ center Q → α z = z)
    (hαC : ∀ c : Q, c ∈ C → α c * c⁻¹ ∈ center Q) :
    ∃ r : Q, ∀ c : Q, c ∈ C → (α * MulAut.conj r) c = c := by
  classical
  let _ := IsExtraspecial.quotient_elementary_abelian 2 Q
  let _ : IsElementaryAbelian 2 (center Q) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [IsExtraspecial.center_order_p 2 Q] using (pow_card_eq_one' (x := z)) }
  let discrepancy : C →* center Q := {
    toFun c := ⟨α c * (c : Q)⁻¹, hαC c c.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' c d := by
      apply Subtype.ext
      change α ((c : Q) * (d : Q)) * ((c : Q) * (d : Q))⁻¹ =
        (α c * (c : Q)⁻¹) * (α d * (d : Q)⁻¹)
      have hc := mem_center_iff.mp (hαC d d.property) (c : Q)⁻¹
      rw [map_mul, mul_inv_rev]
      calc
        α c * α d * ((d : Q)⁻¹ * (c : Q)⁻¹) =
            α c * ((α d * (d : Q)⁻¹) * (c : Q)⁻¹) := by group
        _ = α c * ((c : Q)⁻¹ * (α d * (d : Q)⁻¹)) := by rw [← hc]
        _ = _ := by group }
  let projection : C →* (Q ⧸ center Q) := (QuotientGroup.mk' (center Q)).comp C.subtype
  have hker : projection.ker ≤ discrepancy.ker := by
    intro c hc
    have hcZ : (c : Q) ∈ center Q := (QuotientGroup.eq_one_iff (N := center Q) (c : Q)).mp hc
    apply Subtype.ext
    change α c * (c : Q)⁻¹ = 1
    rw [hαZ c hcZ, mul_inv_cancel]
  let factor : projection.range →* center Q :=
    (QuotientGroup.lift projection.ker discrepancy hker).comp
      (QuotientGroup.quotientKerEquivRange projection).symm.toMonoidHom
  obtain ⟨extended, hext⟩ := binary_hom_extends projection.range factor
  have hagree (c : C) : extended (projection c) = discrepancy c := by
    have h := hext (projection.rangeRestrict c)
    have hpre : (QuotientGroup.quotientKerEquivRange projection).symm
        (projection.rangeRestrict c) = QuotientGroup.mk' projection.ker c := by
      apply (QuotientGroup.quotientKerEquivRange projection).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change extended (projection c) = (QuotientGroup.lift projection.ker discrepancy hker)
      ((QuotientGroup.quotientKerEquivRange projection).symm (projection.rangeRestrict c)) at h
    rw [hpre] at h
    exact h
  obtain ⟨r, hr⟩ := extraspecial_two_commutator_represents_hom extended
  refine ⟨r, ?_⟩
  intro c hc
  have hcomm : ⁅r, c⁆ = α c * c⁻¹ := by
    have hh := congrArg Subtype.val (hagree (⟨c, hc⟩ : C))
    exact (hr c).symm.trans hh
  have hcommZ : ⁅r, c⁆ ∈ center Q := hcomm ▸ hαC c hc
  have hsquare : (α c * c⁻¹)^2 = 1 := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center Q)) ⟨α c * c⁻¹, hαC c hc⟩
    exact congrArg Subtype.val hh
  change α (r * c * r⁻¹) = c
  have heq : r * c * r⁻¹ = ⁅r, c⁆ * c := by simp [commutatorElement_def, mul_assoc]
  rw [heq, map_mul, hαZ _ hcommZ, hcomm]
  have hαeq : α c = (α c * c⁻¹) * c := by group
  calc
    (α c * c⁻¹) * α c = (α c * c⁻¹) * ((α c * c⁻¹) * c) :=
      congrArg (fun z : Q => (α c * c⁻¹) * z) hαeq
    _ = (α c * c⁻¹)^2 * c := by
      simpa only [pow_two] using (mul_assoc (α c * c⁻¹) (α c * c⁻¹) c).symm
    _ = c := by rw [hsquare, one_mul]
