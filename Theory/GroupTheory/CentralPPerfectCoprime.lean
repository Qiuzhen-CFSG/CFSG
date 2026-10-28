module

public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Coprime abelian images of p-perfect central extensions

Suppose a p-perfect group maps to an abelian group of exponent prime to p,
with central p-group kernel. Each commutator map lands in that kernel, so
p-perfectness makes the domain abelian. The coprime power map then also
lands in the kernel and is trivial. Its restriction to the kernel is
bijective, forcing the kernel to be trivial.

This elementary argument supplies the splitting needed for the elementary
nine-group residual in Aschbacher--Smith 15.3.38, printed p.1137. It uses
neither a Schur multiplier calculation nor an assumed complement.
-/

public section

open Subgroup
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

/-- A central p-extension of an abelian coprime-exponent image has no
kernel when its domain is p-perfect. -/
theorem MonoidHom.injective_of_isPPerfect_of_coprime_abelian_image (hG : IsPPerfect p G) (f : G →* H)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker)
    (hcomm : ∀ x y, Commute (f x) (f y))
    {n : ℕ} (hn : Nat.Coprime p n) (hexp : ∀ x, f x ^ n = 1) :
    Function.Injective f := by
  have hmem (x y : G) : ⁅x, y⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x y)
  have hcommG (x y : G) : x * y = y * x := by
    let d : G →* f.ker := {
      toFun z := ⟨⁅z, y⁆, hmem z y⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro z w
        apply Subtype.ext
        change ⁅z * w, y⁆ = ⁅z, y⁆ * ⁅w, y⁆
        have hz := mem_center_iff.mp (hc (hmem w y)) z
        rw [commutatorElement_mul_left_eq_conj_mul, hz, mul_inv_cancel_right]
        exact mem_center_iff.mp (hc (hmem z y)) ⁅w, y⁆ }
    have hd := hG.hom_eq_one_of_isPGroup hp d
    have hx := congrArg (fun k : G →* f.ker => (k x : G)) hd
    exact commutatorElement_eq_one_iff_mul_comm.mp hx
  let : CommGroup G := { ‹Group G› with mul_comm := hcommG }
  let d : G →* f.ker := {
    toFun x := ⟨x ^ n, by rw [MonoidHom.mem_ker, map_pow, hexp]⟩
    map_one' := by apply Subtype.ext; exact one_pow n
    map_mul' x y := by apply Subtype.ext; exact mul_pow x y n }
  have hd := hG.hom_eq_one_of_isPGroup hp d
  have hpow (x : G) : x ^ n = 1 :=
    congrArg (fun k : G →* f.ker => (k x : G)) hd
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have he : (⟨x, hx⟩ : f.ker) = 1 := by
    apply (hp.powEquiv hn).injective
    apply Subtype.ext
    simpa using hpow x
  exact congrArg Subtype.val he
