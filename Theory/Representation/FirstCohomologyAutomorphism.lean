module
public import Theory.Representation.FirstCohomology
public import Mathlib.Tactic.Group
/-!
# Automorphisms detected by first cohomology

An automorphism fixing an abelian kernel pointwise and inducing the identity
on its quotient defines a crossed homomorphism on that literal quotient.
Vanishing first cohomology makes the displacement principal, so the original
automorphism is conjugation by an element of the kernel. The specified
coordinates intertwine the actual conjugation action.

Source application: Aschbacher–Smith C.1.13(c), used in C.5.6(7), p.159.
-/

public section
open Subgroup
namespace Representation.OneCohomology
variable {k E A V : Type*} [Field k] [Group E] [Group A] [AddCommGroup V] [Module k V]

theorem automorphism_inner_of_H1_zero
    (N : Subgroup E) (f : E →* A) (hf : Function.Surjective f) (hker : f.ker = N)
    (e : N ≃* Multiplicative V) (ρ : Representation k A V)
    (he : ∀ (g : E) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : E) =
        g * (e.symm (Multiplicative.ofAdd v) : E) * g⁻¹)
    [Subsingleton (H1 ρ)]
    (α : MulAut E) (hα : ∀ g, f (α g) = f g) (hfix : ∀ n ∈ N, α n = n) :
    ∃ n : N, ∀ g, α g = (n : E)⁻¹ * g * n := by
  classical
  have hd (g : E) : α g * g⁻¹ ∈ N := by
    rw [← hker,MonoidHom.mem_ker,map_mul,map_inv,hα,mul_inv_cancel]
  let d (g : E) : N := ⟨α g * g⁻¹,hd g⟩
  let c (g : E) : V := (e (d g)).toAdd
  have hc_eq (g : E) : (e.symm (Multiplicative.ofAdd (c g)) : E) = α g * g⁻¹ := by
    exact congrArg Subtype.val (e.symm_apply_apply (d g))
  have hd_eq {g t : E} (hgt : f g = f t) : c g = c t := by
    have hn : t⁻¹ * g ∈ N := by
      rw [← hker,MonoidHom.mem_ker,map_mul,map_inv,hgt,inv_mul_cancel]
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
  obtain ⟨w,hw⟩ := (classMap_eq_zero_iff ρ z).mp (Subsingleton.elim _ _)
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
