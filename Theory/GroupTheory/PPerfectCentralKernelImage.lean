module

public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A central kernel image disappears under a coprime residual action

Let a p-perfect group map to an abelian group of exponent coprime to p.
A second homomorphism sending the first kernel to a central p-group
kills that kernel and has abelian image of the same exponent. Commutator
and power maps into the actual kernel image prove this directly; neither
homomorphism is assumed faithful or factored through the other.

Source application: the scalar action on the exact commutator layer in
Aschbacher--Smith12.7.19, printed p.846.
-/

public section
open Subgroup
open scoped commutatorElement
namespace MonoidHom
variable {E A B : Type*} [Group E] [Group A] [Group B]
variable {p n : ℕ} [Fact p.Prime]

/-- Centralizing the actual kernel image forces the action to factor through
the coprime abelian quotient of a p-perfect group. -/
theorem coprime_abelian_image_of_central_kernel_image
    (hE : IsPPerfect p E) (f : E →* B) (ρ : E →* A)
    (hp : IsPGroup p f.ker)
    (hcentral : ∀ x ∈ f.ker, ∀ y : E, Commute (ρ x) (ρ y))
    (hcomm : ∀ x y : E, Commute (f x) (f y))
    (hn : Nat.Coprime p n) (hexp : ∀ x : E, f x ^ n = 1) :
    (∀ x y : E, Commute (ρ x) (ρ y)) ∧
      (∀ x : E, ρ x ^ n = 1) ∧ f.ker ≤ ρ.ker := by
  let C := f.ker.map ρ
  have hC : IsPGroup p C := hp.map ρ
  have hmem (x y : E) : ⁅x,y⁆ ∈ f.ker := by
    rw [mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x y)
  have hρcomm (x y : E) : Commute (ρ x) (ρ y) := by
    let d : E →* C :=
      { toFun := fun z => ⟨ρ ⁅z,y⁆,mem_map_of_mem ρ (hmem z y)⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by
          intro z w
          apply Subtype.ext
          change ρ ⁅z*w,y⁆ = ρ ⁅z,y⁆ * ρ ⁅w,y⁆
          rw [commutatorElement_mul_left_eq_conj_mul,map_mul,map_mul,map_mul,map_inv,
            ← (hcentral ⁅w,y⁆ (hmem w y) z).eq,mul_inv_cancel_right]
          exact (hcentral ⁅w,y⁆ (hmem w y) ⁅z,y⁆).eq }
    have hd := hE.hom_eq_one_of_isPGroup hC d
    have hx := congrArg (fun k : E →* C => (k x : A)) hd
    change ρ ⁅x,y⁆ = 1 at hx
    rw [map_commutatorElement] at hx
    exact commutatorElement_eq_one_iff_mul_comm.mp hx
  let d : E →* C :=
    { toFun := fun x => ⟨ρ x ^ n,by
        rw [←map_pow]
        exact mem_map_of_mem ρ (show x^n ∈ f.ker from by
          rw [mem_ker,map_pow,hexp])⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change ρ (x*y)^n = ρ x^n * ρ y^n
        rw [map_mul,(hρcomm x y).mul_pow] }
  have hd := hE.hom_eq_one_of_isPGroup hC d
  have hpow (x : E) : ρ x^n=1 :=
    congrArg (fun k : E →* C => (k x : A)) hd
  refine ⟨hρcomm,hpow,?_⟩
  intro x hx
  let c : C := ⟨ρ x,mem_map_of_mem ρ hx⟩
  have hc : c=1 := (hC.powEquiv hn).injective (Subtype.ext (by simpa using hpow x))
  exact congrArg Subtype.val hc

end MonoidHom
