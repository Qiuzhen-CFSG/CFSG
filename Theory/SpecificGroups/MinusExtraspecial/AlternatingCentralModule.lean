module
public import Theory.SpecificGroups.MinusExtraspecial.AlternatingAction
public import Theory.SpecificGroups.MinusExtraspecial.FivePointQuotient

/-!
# The actual natural module in the central quotient

The full core image in the central quotient has the commutation coordinates
of the minus extraspecial group. These coordinates preserve conjugation by
every original representative, with the same five-point alternating quotient
marking. No complement is used to identify the module.
-/

public noncomputable section
open Subgroup
namespace MinusExtraspecial.AlternatingCentralModule
open AlternatingAction FixedFourCalculation.Outside
local notation "V" => Multiplicative (BinaryPermutation.core (Fin 5))
local notation "A5" => alternatingGroup (Fin 5)
variable {H : Type*} [Group H] (Q : Subgroup H) [Q.Normal]

set_option maxHeartbeats 800000 in
/-- The full central quotient carries the actual marked natural binary core
module, with the canonical original quotient retained on representatives. -/
theorem exists_marked_module (eQ : Q ≃* Model)
    (hself : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* A5) :
    ∃ (d : (H ⧸ Q) ≃* A5) (p : (H ⧸ center H) →* A5),
      Function.Surjective p ∧
      (∀ h : H, p (QuotientGroup.mk' (center H) h) = d (QuotientGroup.mk' Q h)) ∧
      p.ker = Q.map (QuotientGroup.mk' (center H)) ∧
      ∃ e : p.ker ≃* V,
        (∀ (x : Q) (hx : QuotientGroup.mk' (center H) (x : H) ∈ p.ker),
          e ⟨QuotientGroup.mk' (center H) (x : H), hx⟩ = FivePointQuotient.coordinates (eQ x)) ∧
        ∀ (w : H ⧸ center H) (v : p.ker),
          (e (MulAut.conjNormal w v)).toAdd =
            BinaryPermutation.coreRepresentation (Fin 5) (p w).val (e v).toAdd := by
  obtain ⟨d,hd⟩ := exists_quotient_marking Q eQ hself eA
  let q := QuotientGroup.mk' (center H)
  have hZeq : center H = (center Q).map Q.subtype := center_eq_center_image Q eQ hself
  have hZQ : center H ≤ Q := hZeq ▸ map_subtype_le _
  let F : H →* A5 := d.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hFker : F.ker = Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  let p : (H ⧸ center H) →* A5 := QuotientGroup.lift (center H) F (hFker.symm ▸ hZQ)
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨h,hh⟩ := (d.surjective.comp (QuotientGroup.mk'_surjective Q)) z
    exact ⟨q h,hh⟩
  have hpker : p.ker = Q.map q := by
    ext w
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (center H) w
    change F h = 1 ↔ q h ∈ Q.map q
    change h ∈ F.ker ↔ h ∈ (Q.map q).comap q
    rw [hFker,comap_map_eq_self (by simpa only [q,QuotientGroup.ker_mk'] using hZQ)]
  let b : Q →* p.ker := (q.comp Q.subtype).codRestrict p.ker (fun x =>
    hpker.symm ▸ mem_map_of_mem q x.property)
  have hb : Function.Surjective b := by
    intro v
    have hv : (v : H ⧸ center H) ∈ Q.map q := hpker ▸ v.property
    obtain ⟨x,hx,he⟩ := hv
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hbker : b.ker = center Q := by
    ext x
    change (b x = 1) ↔ x ∈ center Q
    rw [Subtype.ext_iff]
    change q (x : H) = 1 ↔ x ∈ center Q
    change (QuotientGroup.mk (x : H) : H ⧸ center H) = 1 ↔ x ∈ center Q
    rw [QuotientGroup.eq_one_iff,hZeq]
    exact ⟨fun hx => by
      obtain ⟨z,hz,he⟩ := hx
      exact (Subtype.ext he : z = x) ▸ hz,
      fun hx => mem_map_of_mem Q.subtype hx⟩
  let c : Q →* V := FivePointQuotient.coordinates.comp eQ.toMonoidHom
  have hc : Function.Surjective c := FivePointQuotient.coordinates_surjective.comp eQ.surjective
  have hcker : c.ker = center Q := by
    ext x
    change FivePointQuotient.coordinates (eQ x) = 1 ↔ x ∈ center Q
    change eQ x ∈ FivePointQuotient.coordinates.ker ↔ x ∈ center Q
    rw [FivePointQuotient.coordinates_kernel]
    exact MulEquivClass.apply_mem_center_iff eQ
  let e : p.ker ≃* V := (QuotientGroup.quotientKerEquivOfSurjective b hb).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hbker.trans hcker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective c hc))
  have he (x : Q) : e (b x) = c x := by
    have hbq : (QuotientGroup.quotientKerEquivOfSurjective b hb).symm (b x) =
        QuotientGroup.mk' b.ker x := by
      apply (QuotientGroup.quotientKerEquivOfSurjective b hb).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change (QuotientGroup.quotientKerEquivOfSurjective c hc)
      (QuotientGroup.quotientMulEquivOfEq (hbker.trans hcker.symm)
        ((QuotientGroup.quotientKerEquivOfSurjective b hb).symm (b x))) = _
    rw [hbq]
    rfl
  refine ⟨d,p,hp,fun _ => rfl,hpker,e,?_,?_⟩
  · intro x hx
    exact he x
  · intro w v
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (center H) w
    obtain ⟨x,rfl⟩ := hb v
    have hbconj : MulAut.conjNormal (q h) (b x) = b (MulAut.conjNormal h x) := by
      apply Subtype.ext
      change q h * q (x : H) * (q h)⁻¹ = q (h * (x : H) * h⁻¹)
      rw [map_mul,map_mul,map_inv]
    rw [hbconj,he,he]
    have hh := FivePointQuotient.coordinates_equivariant (coreAction Q eQ h) (eQ x)
    rw [coreAction_apply,←hd] at hh
    exact hh

end MinusExtraspecial.AlternatingCentralModule
