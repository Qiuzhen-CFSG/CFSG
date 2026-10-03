module
public import Theory.LinearAlgebra.OrderFifteenRecurrence
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Vanishing of invariant trilinear forms for an order-fifteen binary automorphism

An actual linear automorphism of order fifteen on a binary vector space of
cardinality sixteen preserves only the zero trilinear form. The statement
keeps the supplied operator and form and assumes no chosen basis or
field diagonalization.

The characteristic-polynomial theorem `LinearEquiv.order_fifteen_recurrence`
supplies one of the two primitive quartic recurrences. For a^4=a+I, apply
invariance to thirty-nine triples of iterates whose exponents lie between
zero and three. Coordinatewise additivity expands every fourth iterate;
a checked linear combination of these equalities gives F(x,y,z)=0 in
characteristic two. For a^4=a^3+I, the inverse automorphism satisfies the
first recurrence, and the same form is invariant under the inverse.
Currying is used only to expose the original form's separate additivity.

This is source-independent finite linear algebra used to exclude an
order-fifteen action preserving a nonzero third-commutator form. The finite
linear identity is proved directly in the kernel; its coefficients are
explicit in the proof and require no external certificate at build time.
-/

namespace LinearEquiv

private abbrev Tri {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :=
  MultilinearMap (ZMod 2) (fun _ : Fin 3 => V) (ZMod 2)

private def tri {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (F : Tri (V := V)) (x y z : V) : ZMod 2 := F ![x, y, z]

private theorem tri_add_left {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (F : Tri (V := V)) (x x' y z : V) :
    tri F (x + x') y z = tri F x y z + tri F x' y z := by
  change F.curryLeft (x + x') ![y, z] = _
  rw [map_add]
  rfl

private theorem tri_add_mid {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (F : Tri (V := V)) (x y y' z : V) :
    tri F x (y + y') z = tri F x y z + tri F x y' z := by
  change (F.curryLeft x).curryLeft (y + y') ![z] = _
  rw [map_add]
  rfl

private theorem tri_add_right {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (F : Tri (V := V)) (x y z z' : V) :
    tri F x y (z + z') = tri F x y z + tri F x y z' := by
  change ((F.curryLeft x).curryLeft y).curryLeft (z + z') ![] = _
  rw [map_add]
  rfl

private theorem trilinear_zero_recurrence_1
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a : V → V) (hrec : ∀ x, a (a (a (a x))) = (a x) + x)
    (F : Tri (V := V))
    (hinv : ∀ x y z, tri F (a x) (a y) (a z) = tri F x y z)
    (x y z : V) : tri F x y z = 0 := by
  have h001 := hinv x y (a z)
  have h002 := hinv x y (a (a z))
  have h010 := hinv x (a y) z
  have h011 := hinv x (a y) (a z)
  have h013 := hinv x (a y) (a (a (a z)))
  simp only [hrec, tri_add_right] at h013
  have h020 := hinv x (a (a y)) z
  have h022 := hinv x (a (a y)) (a (a z))
  have h023 := hinv x (a (a y)) (a (a (a z)))
  simp only [hrec, tri_add_right] at h023
  have h031 := hinv x (a (a (a y))) (a z)
  simp only [hrec, tri_add_mid] at h031
  have h032 := hinv x (a (a (a y))) (a (a z))
  simp only [hrec, tri_add_mid] at h032
  have h100 := hinv (a x) y z
  have h101 := hinv (a x) y (a z)
  have h103 := hinv (a x) y (a (a (a z)))
  simp only [hrec, tri_add_right] at h103
  have h110 := hinv (a x) (a y) z
  have h111 := hinv (a x) (a y) (a z)
  have h113 := hinv (a x) (a y) (a (a (a z)))
  simp only [hrec, tri_add_right] at h113
  have h123 := hinv (a x) (a (a y)) (a (a (a z)))
  simp only [hrec, tri_add_right] at h123
  have h130 := hinv (a x) (a (a (a y))) z
  simp only [hrec, tri_add_mid] at h130
  have h131 := hinv (a x) (a (a (a y))) (a z)
  simp only [hrec, tri_add_mid] at h131
  have h132 := hinv (a x) (a (a (a y))) (a (a z))
  simp only [hrec, tri_add_mid] at h132
  have h133 := hinv (a x) (a (a (a y))) (a (a (a z)))
  simp only [hrec, tri_add_mid, tri_add_right] at h133
  have h200 := hinv (a (a x)) y z
  have h202 := hinv (a (a x)) y (a (a z))
  have h203 := hinv (a (a x)) y (a (a (a z)))
  simp only [hrec, tri_add_right] at h203
  have h213 := hinv (a (a x)) (a y) (a (a (a z)))
  simp only [hrec, tri_add_right] at h213
  have h220 := hinv (a (a x)) (a (a y)) z
  have h222 := hinv (a (a x)) (a (a y)) (a (a z))
  have h230 := hinv (a (a x)) (a (a (a y))) z
  simp only [hrec, tri_add_mid] at h230
  have h231 := hinv (a (a x)) (a (a (a y))) (a z)
  simp only [hrec, tri_add_mid] at h231
  have h301 := hinv (a (a (a x))) y (a z)
  simp only [hrec, tri_add_left] at h301
  have h302 := hinv (a (a (a x))) y (a (a z))
  simp only [hrec, tri_add_left] at h302
  have h310 := hinv (a (a (a x))) (a y) z
  simp only [hrec, tri_add_left] at h310
  have h311 := hinv (a (a (a x))) (a y) (a z)
  simp only [hrec, tri_add_left] at h311
  have h312 := hinv (a (a (a x))) (a y) (a (a z))
  simp only [hrec, tri_add_left] at h312
  have h313 := hinv (a (a (a x))) (a y) (a (a (a z)))
  simp only [hrec, tri_add_left, tri_add_right] at h313
  have h320 := hinv (a (a (a x))) (a (a y)) z
  simp only [hrec, tri_add_left] at h320
  have h321 := hinv (a (a (a x))) (a (a y)) (a z)
  simp only [hrec, tri_add_left] at h321
  have h331 := hinv (a (a (a x))) (a (a (a y))) (a z)
  simp only [hrec, tri_add_left, tri_add_mid] at h331
  have h333 := hinv (a (a (a x))) (a (a (a y))) (a (a (a z)))
  simp only [hrec, tri_add_left, tri_add_mid, tri_add_right] at h333
  linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide])) h001 + h002 + h010 + h011 + h013 + h020 + h022 + h023 + h031 + h032 + h100 + h101 + h103 + h110 + h111 + h113 + h123 + h130 + h131 + h132 + h133 + h200 + h202 + h203 + h213 + h220 + h222 + h230 + h231 + h301 + h302 + h310 + h311 + h312 + h313 + h320 + h321 + h331 + h333

private theorem trilinear_eq_zero_of_first_recurrence
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a : V → V)
    (hrec : ∀ x : V, a (a (a (a x))) = a x + x)
    (F : MultilinearMap (ZMod 2) (fun _ : Fin 3 => V) (ZMod 2))
    (hF : ∀ v, F (fun i => a (v i)) = F v) : F = 0 := by
  have hinv (x y z : V) : tri F (a x) (a y) (a z) = tri F x y z := by
    have he : (fun i : Fin 3 => a (![x, y, z] i)) = ![a x, a y, a z] := by
      ext i
      fin_cases i <;> rfl
    simpa only [he, tri] using hF ![x, y, z]
  ext v
  change F v = 0
  have hv : v = ![v 0, v 1, v 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact trilinear_zero_recurrence_1 a hrec F hinv (v 0) (v 1) (v 2)

private theorem trilinear_eq_zero_of_recurrence
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a : V ≃ₗ[ZMod 2] V)
    (hrec : (∀ x : V, a (a (a (a x))) = a x + x) ∨
      (∀ x : V, a (a (a (a x))) = a (a (a x)) + x))
    (F : MultilinearMap (ZMod 2) (fun _ : Fin 3 => V) (ZMod 2))
    (hF : ∀ v, F (fun i => a (v i)) = F v) : F = 0 := by
  rcases hrec with hrec | hrec
  · exact trilinear_eq_zero_of_first_recurrence a hrec F hF
  have htwo (z : V) : z + z = 0 := by
    simpa only [two_smul, zero_smul] using
      congrArg (fun r : ZMod 2 => r • z) (show (2 : ZMod 2) = 0 by decide)
  have hinverse (x : V) :
      a.symm (a.symm (a.symm (a.symm x))) = a.symm x + x := by
    have h := hrec (a.symm (a.symm (a.symm (a.symm x))))
    simp only [a.apply_symm_apply] at h
    have he := congrArg (fun y => a.symm x + y) h
    simpa only [← add_assoc, htwo, zero_add] using he.symm
  apply trilinear_eq_zero_of_first_recurrence a.symm hinverse F
  intro v
  have h := hF (fun i => a.symm (v i))
  simpa only [a.apply_symm_apply] using h.symm

/-- An actual order-fifteen automorphism of binary four-space has no nonzero invariant trilinear form. -/
public theorem invariant_trilinear_eq_zero_of_order_fifteen
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Nat.card V = 16) (a : V ≃ₗ[ZMod 2] V) (ha : orderOf a = 15)
    (F : MultilinearMap (ZMod 2) (fun _ : Fin 3 => V) (ZMod 2))
    (hF : ∀ v, F (fun i => a (v i)) = F v) : F = 0 :=
  trilinear_eq_zero_of_recurrence a (order_fifteen_recurrence hV a ha) F hF

end LinearEquiv
