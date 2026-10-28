module
public import Theory.Representation.FirstCohomologyAutomorphism.Subkernel

/-!
# The displacement cocycle of an automorphism fixing a quotient kernel

Suppose an automorphism has all displacements in an abelian module N and
fixes the kernel of a specified surjection E → A. Its displacement is
constant on the fibers, so it defines an actual cocycle for the given
A-action on N. The evaluation identity retains the original automorphism,
quotient map and module coordinates.

Source application: Aschbacher–Smith C.1.13(b), applied in 13.5.15 on
printed p.920. For the original A₅ pair inside the A₆ block, elements of
C_T(K) give cocycles vanishing on its point stabilizer. The normalized
natural-module calculation then bounds the original centralizer's order.
-/

public section
open Subgroup
namespace Representation.OneCohomology
variable {k E A V : Type*} [Field k] [Group E] [Group A]
  [AddCommGroup V] [Module k V]

/-- The literal displacement of an automorphism descends to the specified
quotient action when the automorphism fixes its kernel pointwise. -/
theorem exists_automorphism_cocycle_of_subkernel
    (N : Subgroup E) (f : E →* A) (hf : Function.Surjective f)
    (e : N ≃* Multiplicative V) (ρ : Representation k A V)
    (he : ∀ (g : E) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : E) =
        g * (e.symm (Multiplicative.ofAdd v) : E) * g⁻¹)
    (α : MulAut E) (hdis : ∀ g, α g * g⁻¹ ∈ N)
    (hfix : ∀ n ∈ f.ker, α n = n) :
    ∃ z : cocycles ρ, ∀ g : E,
      z.val (f g) = (e ⟨α g * g⁻¹, hdis g⟩).toAdd := by
  classical
  let d (g : E) : N := ⟨α g * g⁻¹, hdis g⟩
  let c (g : E) : V := (e (d g)).toAdd
  have hc_eq (g : E) : (e.symm (Multiplicative.ofAdd (c g)) : E) = α g * g⁻¹ := by
    exact congrArg Subtype.val (e.symm_apply_apply (d g))
  have hd_eq {g t : E} (hgt : f g = f t) : c g = c t := by
    have hn : t⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgt, inv_mul_cancel]
    have ha := hfix _ hn
    rw [map_mul, map_inv] at ha
    have hd' : α g * g⁻¹ = α t * t⁻¹ := by
      calc
        α g * g⁻¹ = α t * ((α t)⁻¹ * α g) * g⁻¹ := by group
        _ = α t * (t⁻¹ * g) * g⁻¹ := by rw [ha]
        _ = α t * t⁻¹ := by group
    exact congrArg (fun n : N => (e n).toAdd) (Subtype.ext hd')
  have hcocycle (g t : E) : c (g * t) = ρ (f g) (c t) + c g := by
    apply Multiplicative.ofAdd.injective
    apply e.symm.injective
    apply Subtype.ext
    rw [hc_eq]
    change α (g * t) * (g * t)⁻¹ =
      (e.symm (Multiplicative.ofAdd (ρ (f g) (c t)) * Multiplicative.ofAdd (c g)) : E)
    rw [map_mul e.symm]
    change α (g * t) * (g * t)⁻¹ =
      (e.symm (Multiplicative.ofAdd (ρ (f g) (c t))) : E) *
        (e.symm (Multiplicative.ofAdd (c g)) : E)
    rw [he, hc_eq, hc_eq]
    have hncomm : Commute (g * (α t * t⁻¹) * g⁻¹) (α g * g⁻¹) := by
      have hNcomm : ∀ a b : N, a * b = b * a := fun a b =>
        e.injective (by simp only [map_mul]; exact mul_comm _ _)
      have hh := congrArg Subtype.val
        (hNcomm (e.symm (Multiplicative.ofAdd (ρ (f g) (c t)))) (d g))
      change _ * _ = _ * _
      simpa only [coe_mul, he, hc_eq, d] using hh
    rw [hncomm.eq]
    simp only [map_mul, mul_inv_rev]
    group
  let b (a : A) : E := (hf a).choose
  have hb (a : A) : f (b a) = a := (hf a).choose_spec
  let z : cocycles ρ := ⟨fun a => c (b a), by
    intro a t
    have hz := hd_eq (show f (b (a * t)) = f (b a * b t) by rw [map_mul, hb, hb, hb])
    exact hz.trans (by rw [hcocycle, hb])⟩
  refine ⟨z, ?_⟩
  intro g
  change c (b (f g)) = c g
  exact hd_eq (hb (f g))

end Representation.OneCohomology
