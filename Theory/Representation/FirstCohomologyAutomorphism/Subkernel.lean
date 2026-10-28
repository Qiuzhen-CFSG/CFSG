module
public import Theory.Representation.FirstCohomology
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Cohomological displacement inside a proper subgroup of the kernel

An automorphism can have its displacements in an abelian module N while
the quotient representation has a larger kernel M. If it fixes M, its
crossed homomorphism still descends to the quotient and vanishing H¹ makes
it conjugation by N. The second theorem supplies fixation of M when
[M,E] lies in N, M centralizes N, and N has no ambient central elements.
It compares the actual conjugations before killing the fixed displacement.

This retains the possible central two-core factor in the A₅ block argument
of Aschbacher–Smith C.1.13(c), printed pp.124–125. No equality M=N is used.
-/

public section
open Subgroup
namespace Representation.OneCohomology
variable {k E A V : Type*} [Field k] [Group E] [Group A] [AddCommGroup V] [Module k V]

theorem automorphism_inner_of_H1_zero_of_subkernel
    (N : Subgroup E) (f : E →* A) (hf : Function.Surjective f)
    (e : N ≃* Multiplicative V) (ρ : Representation k A V)
    (he : ∀ (g : E) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : E) =
        g * (e.symm (Multiplicative.ofAdd v) : E) * g⁻¹)
    [Subsingleton (H1 ρ)]
    (α : MulAut E) (hdis : ∀ g, α g * g⁻¹ ∈ N)
    (hfix : ∀ n ∈ f.ker, α n = n) :
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

namespace Representation.OneCohomology
open scoped commutatorElement IsMulCommutative
variable {E : Type*} [Group E]

theorem automorphism_fixes_centralizing_layer
    (N M : Subgroup E) [IsMulCommutative N]
    (hMC : M ≤ centralizer (N : Set E))
    (hMN : ⁅M, (⊤ : Subgroup E)⁆ ≤ N)
    (hZ : N ⊓ center E = ⊥)
    (α : MulAut E) (hd : ∀ x, α x * x⁻¹ ∈ N)
    (hf : ∀ x ∈ N, α x = x) : ∀ m ∈ M, α m = m := by
  intro m hm
  have hconj (x : E) : α m * α x * (α m)⁻¹ = m * α x * m⁻¹ := by
    have hcx : ⁅m,x⁆ ∈ N := hMN (commutator_mem_commutator hm (mem_top x))
    have hcomm : Commute (α x * x⁻¹) ⁅m,x⁆ := by
      exact Subtype.ext_iff.mp (mul_comm (⟨_,hd x⟩ : N) ⟨_,hcx⟩)
    have hmx : m * (α x * x⁻¹) = (α x * x⁻¹) * m :=
      (hMC hm _ (hd x)).symm
    calc
      α m * α x * (α m)⁻¹ = α (m*x*m⁻¹) := by simp only [map_mul,map_inv]
      _ = α (⁅m,x⁆ * x) := by congr 1; simp only [commutatorElement_def]; group
      _ = ⁅m,x⁆ * α x := by rw [map_mul,hf _ hcx]
      _ = ⁅m,x⁆ * ((α x*x⁻¹)*x) := by group
      _ = (α x*x⁻¹) * (⁅m,x⁆*x) := by rw [←mul_assoc,←hcomm.eq,mul_assoc]
      _ = (α x*x⁻¹) * (m*x*m⁻¹) := by simp only [commutatorElement_def]; group
      _ = m * α x * m⁻¹ := by rw [←mul_assoc,←mul_assoc,←hmx]; group
  have hc : α m * m⁻¹ ∈ center E := by
    apply mem_center_iff.mpr
    intro x
    have hh := hconj (α.symm (m⁻¹*x*m))
    rw [α.apply_symm_apply] at hh
    have hh' : (α m * m⁻¹) * x * (α m * m⁻¹)⁻¹ = x := by
      calc
        _ = α m * (m⁻¹*x*m) * (α m)⁻¹ := by group
        _ = m * (m⁻¹*x*m) * m⁻¹ := hh
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  have hz : α m * m⁻¹ = 1 := by
    have he : α m * m⁻¹ ∈ N ⊓ center E := ⟨hd m,hc⟩
    simpa only [hZ,mem_bot] using he
  exact mul_inv_eq_one.mp hz
end Representation.OneCohomology
