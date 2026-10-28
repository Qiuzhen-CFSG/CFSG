module
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Fixed-free quotient displacements generate across the Frattini subgroup

An automorphism without fixed points on an abelian quotient has a bijective
displacement homomorphism. Hence its displacements generate that quotient.
When the kernel lies in the Frattini subgroup, every subgroup containing
the original displacements is the whole group.

Source application: the quaternion pair lift in Aschbacher–Smith13.5.15, p.920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {Q : Type*} [Group Q] [Finite Q]

theorem eq_top_of_fixedFree_quotient_displacements
    (N : Subgroup Q) [N.Characteristic] [IsMulCommutative (Q⧸N)]
    (hN : N≤frattini Q) (a : MulAut Q)
    (hfix : ∀x:Q⧸N,quotientAut N a x=x→x=1)
    (K : Subgroup Q) (hd : ∀x:Q,a x*x⁻¹∈K) : K=⊤ := by
  let δ : (Q⧸N)→*(Q⧸N) := {
    toFun := fun x=>quotientAut N a x*x⁻¹
    map_one' := by simp
    map_mul' := fun x y=>by
      simp only [map_mul,mul_inv_rev]
      ac_rfl }
  have hi : Function.Injective δ := by
    apply (MonoidHom.ker_eq_bot_iff δ).mp
    ext x
    change quotientAut N a x*x⁻¹=1↔x=1
    constructor
    · intro hx
      exact hfix x (mul_inv_eq_one.mp hx)
    · rintro rfl
      simp
  have hs := Finite.surjective_of_injective hi
  apply frattini_nongenerating
  apply top_unique
  intro x _
  obtain ⟨y,hy⟩ := hs (QuotientGroup.mk' N x)
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N y
  have he : QuotientGroup.mk' N (a u*u⁻¹)=QuotientGroup.mk' N x := by
    change quotientAut N a (QuotientGroup.mk' N u)*(QuotientGroup.mk' N u)⁻¹=_ at hy
    simpa only [quotientAut_apply_mk,map_mul,map_inv] using hy
  have hn : (a u*u⁻¹)⁻¹*x∈N := QuotientGroup.eq.mp he
  have hm := (K⊔frattini Q).mul_mem ((show K≤K⊔frattini Q from le_sup_left) (hd u)) ((show frattini Q≤K⊔frattini Q from le_sup_right) (hN hn))
  simpa only [mul_inv_cancel_left] using hm

end Subgroup
end
