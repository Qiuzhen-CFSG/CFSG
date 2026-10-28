module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularInvolutionPairs
import Mathlib.Tactic.NormNum
/-!
# Fixed-point-free cubics from singular involution pairs

A pair of involutions with singular displacement generates a two-group or
S₃ in the binary four-dimensional plus action. In the latter case their
product has order three and fixes no nonzero vector. Each nonidentity
singular actor swaps the anisotropic planes; its involution relation makes
the two coordinates of the cubic product conjugate nonidentity cubics.
Such a permutation cycles the three nonzero vectors of its binary plane.
The plane-action argument uses the public nonzero-vector formula, while
all finite checks involve only wreath and permutation coordinates.

Source: Aschbacher–Smith, Lemma 13.5.15, printed p.920, the selected
I*=<V*,(V*)^g> congruent to S₃. This supplies its fixed-point-free cubic
action on U_H/Φ(U_H), which the original commutator and Frattini argument
uses to prove U_H<=I. That group-theoretic lifting is a separate consumer.
-/

open Subgroup
namespace BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath := Fintype.ofEquiv _
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm

private theorem plane_cubic_fixed (p : Equiv.Perm (Fin 3))
    (hp : p^3=1) (hp1 : p≠1) (v : Plane) (hv : planeLinear p v=v) : v=0 := by
  have hf : ∀ p : Equiv.Perm (Fin 3), p^3=1 → p≠1 → ∀ i, p i≠i := by decide +kernel
  have hc : ∀ v : Plane, v=0 ∨ ∃ i, v=nonzeroVector i := by decide +kernel
  rcases hc v with h | ⟨i,rfl⟩
  · exact h
  · rw [planeLinear_nonzeroVector] at hv
    exact (hf p hp hp1 i (nonzeroVector_injective hv)).elim

private theorem swapping_cubic_fixed (a b : Wreath) (ha : a^2=1) (hb : b^2=1)
    (har : a.right ≠ 1) (hbr : b.right ≠ 1)
    (hab : (a*b)^3=1) (hab1 : a*b≠1) (v : V)
    (hv : (wreathToIsometry (a*b)).val v=v) : v=0 := by
  have h : ∀ (a b : Wreath), a^2=1 → b^2=1 → a.right≠1 → b.right≠1 →
      (a*b)^3=1 → a*b≠1 → (a*b).right=1 ∧
      ∀ i : C2, ((a*b).left i)^3=1 ∧ (a*b).left i≠1 := by decide +kernel
  obtain ⟨hr,hp⟩ := h a b ha hb har hbr hab hab1
  rw [wreathToIsometry_apply,if_pos hr] at hv
  apply Prod.ext
  · exact plane_cubic_fixed _ (hp 1).1 (hp 1).2 v.1 (congrArg Prod.fst hv)
  · exact plane_cubic_fixed _ (hp swapIndex).1 (hp swapIndex).2 v.2 (congrArg Prod.snd hv)

/-- The product of a non-two-group singular involution pair has order three
and fixes no nonzero vector in the literal binary plus-space action. -/
public theorem singular_pair_cubic_fixed_free (a b : Wreath)
    (ha : a^2=1) (hb : b^2=1)
    (hsa : SingularDisplacements a) (hsb : SingularDisplacements b)
    (hn : ¬ IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup Wreath)) :
    orderOf (a*b)=3 ∧ ∀ v : V, (wreathToIsometry (a*b)).val v=v → v=0 := by
  obtain ⟨e⟩ := symmetricThree_of_singular_involutions a b ha hb hsa hsb hn
  have h6 : Nat.card (zpowers a ⊔ zpowers b : Subgroup Wreath)=6 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hcl : closure ({b,a}:Set Wreath) = zpowers a ⊔ zpowers b := by
    rw [zpowers_eq_closure,zpowers_eq_closure,←closure_union]
    congr 1
    exact Set.pair_comm b a
  have hnot2 : (a*b)^2≠1 := by
    intro hh
    have hc := (closure_pair_finite_card_le_of_involutions (by decide : 0<2) b a hb ha hh).2
    rw [hcl,h6] at hc
    omega
  have h3 := (singular_involutions_product_relation a b ha hb hsa hsb).resolve_left hnot2
  have hne : a*b≠1 := fun h => hnot2 (by rw [h,one_pow])
  have har : a.right≠1 := by
    intro h
    have he := eq_one_of_singular_preserving a hsa h
    exact hnot2 (by simpa only [he,one_mul] using hb)
  have hbr : b.right≠1 := by
    intro h
    have he := eq_one_of_singular_preserving b hsb h
    exact hnot2 (by simpa only [he,mul_one] using ha)
  exact ⟨orderOf_eq_prime h3 hne,fun v hv => swapping_cubic_fixed a b ha hb har hbr h3 hne v hv⟩
end BinaryFourPlus
