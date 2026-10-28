module
public import Theory.Representation.SL3.NaturalDualElementaryLift
import Mathlib.Tactic.Group

/-!
# Automorphism rigidity for a natural-by-dual extension

An automorphism fixing the natural kernel and acting trivially on the dual
quotient has displacement in the natural module. Commutation with the actual
SL₃ action makes that displacement fixed by each quotient-vector stabilizer.
Such a stabilizer fixes no natural vector, so every displacement vanishes.
The argument retains the literal action and quotient map, and does not assume
that an additive map between the modules is linear over the defining field.

Source: Aschbacher–Smith C.1.35, printed p.138, the trivial-centralizer step
in the action-normalizer argument. The original invariant-lift application is
in NonblockMSLiftAction.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
variable {F A E : Type*} [Field F] [Group A] [Group E]
  [MulDistribMulAction A E]

/-- Rigidity of an equivariant automorphism of a natural-by-dual extension. -/
theorem natural_dual_automorphism_eq_one
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : E →* Multiplicative (Module.Dual F (Fin 3 → F)))
    (u : p.ker ≃* Multiplicative (Fin 3 → F))
    (hp : ∀ a q, (p (a • q)).toAdd =
      (specialLinearNatural 3).dual (α a) (p q).toAdd)
    (hu : ∀ (a : A) (x y : p.ker), (y : E) = a • (x : E) →
      (u y).toAdd = specialLinearNatural 3 (α a) (u x).toAdd)
    (τ : MulAut E) (hquot : ∀ q, p (τ q) = p q)
    (hfix : ∀ q ∈ p.ker, τ q = q)
    (hcomm : ∀ (a : A) (q : E), τ (a • q) = a • τ q) : τ = 1 := by
  have hd (q : E) : τ q * q⁻¹ ∈ p.ker := by
    change p (τ q * q⁻¹) = 1
    rw [map_mul,map_inv,hquot,mul_inv_cancel]
  let d (q : E) : p.ker := ⟨τ q * q⁻¹,hd q⟩
  have hdesc {q r : E} (he : p q = p r) : d q = d r := by
    have hk : q⁻¹*r ∈ p.ker := by
      change p (q⁻¹*r) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hh := hfix _ hk
    rw [map_mul,map_inv] at hh
    apply Subtype.ext
    change τ q * q⁻¹ = τ r * r⁻¹
    calc
      τ q * q⁻¹ = τ q * ((τ q)⁻¹ * τ r) * r⁻¹ := by rw [hh]; group
      _ = τ r * r⁻¹ := by group
  ext q
  by_cases hz : (p q).toAdd = 0
  · exact hfix q (Multiplicative.toAdd.injective hz)
  have hd0 : (u (d q)).toAdd = 0 := by
    apply dual_stabilizer_fixed_zero (p q).toAdd hz
    intro g hg
    obtain ⟨a,rfl⟩ := hα g
    have he : p (a • q) = p q := Multiplicative.toAdd.injective ((hp a q).trans hg)
    have hdact : (d (a • q) : E) = a • (d q : E) := by
      change τ (a • q) * (a • q)⁻¹ = a • (τ q * q⁻¹)
      rw [hcomm,smul_mul',smul_inv']
    have hh := hu a (d q) (d (a • q)) hdact
    rw [hdesc he] at hh
    exact hh.symm
  have he : d q = 1 := u.injective ((Multiplicative.toAdd.injective hd0).trans u.map_one.symm)
  have hh := congrArg Subtype.val he
  change τ q * q⁻¹ = 1 at hh
  exact mul_inv_eq_one.mp hh

end Representation.SL3ParabolicNatural
