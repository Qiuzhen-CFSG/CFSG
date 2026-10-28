module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Prime elements fixed by an exchange involution

In a direct square, an involution exchanging the factors fixes the product
of a first-coordinate element with its image. If its displacement on a
prime element lies in a coordinate-closed subgroup U contained in A, this
product remains in A and has the same prime order. This retains the actual
subgroup A, rather than constructing an element only in the ambient square.

Source application: the original point-residual cubic in Aschbacher–Smith,
proof of 14.7.32, printed p.1058, refs/quasithin.pdf.
-/

public section
open Subgroup

namespace Theory.GroupTheory
theorem exists_fixed_prime_element_of_exchange
    {X : Type*} [Group X] (A U₁ : Subgroup (X × X))
    (hU : ∀ g ∈ U₁, (1,g.2) ∈ U₁)
    (hUA : U₁ ≤ A)
    (α : MulAut (X × X)) (hα : ∀ g, α (α g) = g)
    (hleft : ∀ x : X, (α (x,1)).1 = 1)
    (hright : ∀ x : X, (α (1,x)).2 = 1)
    (a : X × X) (ha : a ∈ A) (haU : a ∉ U₁)
    (p : ℕ) (hp : p.Prime) (hap : a^p=1)
    (hdisp : α a*a⁻¹ ∈ U₁) :
    ∃ b ∈ A, orderOf b = p ∧ α b = b := by
  let x : X × X := (a.1,1)
  let y : X × X := (1,a.2)
  have hxy : x*y=a := by ext <;> simp [x,y]
  have hc : Commute x (α x) := by
    change x * α x = α x * x
    apply Prod.ext
    · change a.1 * (α x).1 = (α x).1 * a.1
      rw [hleft]
      simp
    · change 1 * (α x).2 = (α x).2 * 1
      simp
  let b := x*α x
  have hbα : α b = b := by
    dsimp only [b]
    rw [map_mul,hα,hc.eq]
  have hproj : (α x).2 = (α a).2 := by
    rw [←hxy,map_mul,Prod.snd_mul,hright,mul_one]
  have hba : b*a⁻¹ = (1,(α a*a⁻¹).2) := by
    apply Prod.ext
    · change (a.1*(α x).1)*a.1⁻¹=1
      rw [hleft,mul_one,mul_inv_cancel]
    · change (1*(α x).2)*a.2⁻¹=(α a).2*a.2⁻¹
      rw [one_mul,hproj]
  have hbU : b*a⁻¹ ∈ U₁ := hba ▸ hU _ hdisp
  have hbA : b ∈ A := by
    simpa only [inv_mul_cancel_right] using A.mul_mem (hUA hbU) ha
  have hbp : b^p=1 := by
    have hx : x^p=1 := by
      apply Prod.ext
      · change a.1^p=1
        exact congrArg (fun q : X × X => q.1) hap
      · simp [x]
    dsimp only [b]
    rw [hc.mul_pow,←map_pow,hx,map_one,mul_one]
  have hb1 : b ≠ 1 := by
    intro he
    apply haU
    have hh := U₁.inv_mem hbU
    simpa [he] using hh
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨b,hbA,(orderOf_eq_prime_iff).mpr ⟨hbp,hb1⟩,hbα⟩
end Theory.GroupTheory

