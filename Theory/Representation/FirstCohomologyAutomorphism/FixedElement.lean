module
public import Theory.Representation.FirstCohomologyAutomorphism.Subkernel
/-!
# Displacement splitting from a fixed quotient element

An automorphism with displacement in an abelian module gives a cocycle on
the actual action quotient when it fixes the quotient kernel. If it also
fixes an element whose cyclic restriction detects first cohomology, the
cocycle is principal and the automorphism is inner by the module.

Source application: Aschbacher--Smith 12.2.25, printed p.805, the binary
SL3 indecomposable exclusion. The quotient kernel can properly contain N.
-/
public section
open Subgroup
namespace Representation.OneCohomology
variable {k E A V : Type*} [Field k] [Group E] [Group A] [AddCommGroup V] [Module k V]

theorem automorphism_inner_of_fixed_element_of_subkernel
    (N : Subgroup E) (f : E →* A) (hf : Function.Surjective f)
    (e : N ≃* Multiplicative V) (ρ : Representation k A V)
    (he : ∀ (g : E) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : E) =
        g * (e.symm (Multiplicative.ofAdd v) : E) * g⁻¹)
    (a : E)
    (hprincipal : ∀ z : cocycles ρ, z.val (f a) = 0 →
      ∃ w, principal ρ w = z)
    (α : MulAut E) (hdis : ∀ g, α g * g⁻¹ ∈ N)
    (hfix : ∀ n ∈ f.ker, α n = n) (ha : α a = a) :
    ∃ n : N, ∀ g, α g = (n : E)⁻¹ * g * n := by
  classical
  have hd (g : E) : α g * g⁻¹ ∈ N := hdis g
  let d (g : E) : N := ⟨α g * g⁻¹,hd g⟩
  let c (g : E) : V := (e (d g)).toAdd
  have hc_eq (g : E) : (e.symm (Multiplicative.ofAdd (c g)) : E) = α g * g⁻¹ := by
    exact congrArg Subtype.val (e.symm_apply_apply (d g))
  have hd_eq {g t : E} (hgt : f g = f t) : c g = c t := by
    have hn : t⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hgt,inv_mul_cancel]
    have ha := hfix _ hn
    rw [map_mul,map_inv] at ha
    have hd' : α g * g⁻¹ = α t * t⁻¹ := by
      calc
        α g * g⁻¹ = α t * ((α t)⁻¹ * α g) * g⁻¹ := by group
        _ = α t * (t⁻¹ * g) * g⁻¹ := by rw [ha]
        _ = α t * t⁻¹ := by group
    exact congrArg (fun n : N => (e n).toAdd) (Subtype.ext hd')
  have hcocycle (g t : E) : c (g*t) = ρ (f g) (c t) + c g := by
    apply Multiplicative.ofAdd.injective
    apply e.symm.injective
    apply Subtype.ext
    rw [hc_eq]
    change α (g*t) * (g*t)⁻¹ =
      (e.symm (Multiplicative.ofAdd (ρ (f g) (c t)) * Multiplicative.ofAdd (c g)) : E)
    rw [map_mul e.symm]
    change α (g*t) * (g*t)⁻¹ =
      (e.symm (Multiplicative.ofAdd (ρ (f g) (c t))) : E) *
        (e.symm (Multiplicative.ofAdd (c g)) : E)
    rw [he,hc_eq,hc_eq]
    have hncomm : Commute (g * (α t * t⁻¹) * g⁻¹) (α g * g⁻¹) := by
      have hNcomm : ∀ a b : N, a*b=b*a := fun a b => e.injective (by simp only [map_mul]; exact mul_comm _ _)
      have hh := congrArg Subtype.val (hNcomm (e.symm (Multiplicative.ofAdd (ρ (f g) (c t)))) (d g))
      change _ * _ = _ * _
      simpa only [coe_mul,he,hc_eq,d] using hh
    rw [hncomm.eq]
    simp only [map_mul,mul_inv_rev]
    group
  let b (a : A) : E := (hf a).choose
  have hb (a : A) : f (b a) = a := (hf a).choose_spec
  let z : cocycles ρ := ⟨fun a => c (b a),by
    intro a t
    have hz := hd_eq (show f (b (a*t)) = f (b a * b t) by rw [map_mul,hb,hb,hb])
    exact hz.trans (by rw [hcocycle,hb])⟩
  have hza : z.val (f a) = 0 := by
    change c (b (f a)) = 0
    rw [hd_eq (hb (f a))]
    simp [c,d,ha]
  obtain ⟨w,hw⟩ := hprincipal z hza
  have hcw (g : E) : c g = ρ (f g) w - w := by
    have heq := congrArg (fun z : cocycles ρ => z.val (f g)) hw
    exact (hd_eq (hb (f g)).symm).trans heq.symm
  refine ⟨e.symm (Multiplicative.ofAdd w),?_⟩
  intro g
  have hh := hc_eq g
  rw [hcw] at hh
  rw [sub_eq_add_neg] at hh
  change (e.symm (Multiplicative.ofAdd (ρ (f g) w) * (Multiplicative.ofAdd w)⁻¹) : E) = α g * g⁻¹ at hh
  rw [map_mul,map_inv] at hh
  change (e.symm (Multiplicative.ofAdd (ρ (f g) w)) : E) * (e.symm (Multiplicative.ofAdd w) : E)⁻¹ = α g * g⁻¹ at hh
  rw [he] at hh
  have hncomm : Commute (g * (e.symm (Multiplicative.ofAdd w) : E) * g⁻¹)
      (e.symm (Multiplicative.ofAdd w) : E)⁻¹ := by
    have hNcomm : ∀ a b : N, a*b=b*a := fun a b => e.injective (by simp only [map_mul]; exact mul_comm _ _)
    have hh := congrArg Subtype.val (hNcomm (e.symm (Multiplicative.ofAdd (ρ (f g) w)))
      (e.symm (Multiplicative.ofAdd w))⁻¹)
    change _ * _ = _ * _
    simpa only [coe_mul,coe_inv,he] using hh
  rw [hncomm.eq] at hh
  calc
    α g = (α g * g⁻¹) * g := by group
    _ = ((e.symm (Multiplicative.ofAdd w) : E)⁻¹ * (g * (e.symm (Multiplicative.ofAdd w) : E) * g⁻¹)) * g := by rw [hh]
    _ = (e.symm (Multiplicative.ofAdd w) : E)⁻¹ * g * e.symm (Multiplicative.ofAdd w) := by group
end Representation.OneCohomology
