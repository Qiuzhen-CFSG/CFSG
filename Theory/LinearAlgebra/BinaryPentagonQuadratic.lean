module
public import Theory.LinearAlgebra.BinaryPentagon
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Field.ZMod

/-!
# Cyclic binary pentagon quadratic forms

A quadratic form vanishing on five coordinate vectors and invariant under
their cyclic rotation has one coefficient on adjacent pairs and one on
diagonal pairs. The checked singular-subspace calculation then forces
the form to vanish if a totally singular subspace has codimension at
most two. A surjective orbit map transports this conclusion to the
original quotient space, without requiring independence of orbit vectors.

Source application: Aschbacher–Smith 14.2.20(1), printed p.987.
-/

public section
namespace BinaryPentagon
open QuadraticMap
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

@[expose] def vertex (i : Fin 5) : Space := Pi.single i 1

@[expose] def rotate (v : Space) : Space := ![v 4, v 0, v 1, v 2, v 3]

private theorem rotate_vertex (i : Fin 5) : rotate (vertex i) = vertex (i + 1) := by
  ext j
  fin_cases i <;> fin_cases j <;> decide

private theorem rotate_add (x y : Space) : rotate (x + y) = rotate x + rotate y := by
  ext i
  fin_cases i <;> rfl

theorem invariant_polynomial (Q : QuadraticForm (ZMod 2) Space)
    (hv : ∀ i, Q (vertex i) = 0) (hr : ∀ v, Q (rotate v) = Q v) :
    ∀ v, Q v = polynomial (polar Q (vertex 0) (vertex 1))
      (polar Q (vertex 0) (vertex 2)) v := by
  let B := polar Q
  have hrot (i j : Fin 5) : B (vertex (i + 1)) (vertex (j + 1)) = B (vertex i) (vertex j) := by
    change polar Q _ _ = polar Q _ _
    rw [← rotate_vertex i, ← rotate_vertex j, polar, polar, ← rotate_add, hr, hr, hr]
  have h12 : B (vertex 1) (vertex 2) = B (vertex 0) (vertex 1) := hrot 0 1
  have h23 : B (vertex 2) (vertex 3) = B (vertex 0) (vertex 1) := (hrot 1 2).trans h12
  have h34 : B (vertex 3) (vertex 4) = B (vertex 0) (vertex 1) := (hrot 2 3).trans h23
  have h40 : B (vertex 4) (vertex 0) = B (vertex 0) (vertex 1) := (hrot 3 4).trans h34
  have h13 : B (vertex 1) (vertex 3) = B (vertex 0) (vertex 2) := hrot 0 2
  have h24 : B (vertex 2) (vertex 4) = B (vertex 0) (vertex 2) := (hrot 1 3).trans h13
  have h30 : B (vertex 3) (vertex 0) = B (vertex 0) (vertex 2) := (hrot 2 4).trans h24
  have h41 : B (vertex 4) (vertex 1) = B (vertex 0) (vertex 2) := (hrot 3 0).trans h30
  have h04 : B (vertex 0) (vertex 4) = B (vertex 0) (vertex 1) :=
    (polar_comm Q _ _).trans h40
  have h03 : B (vertex 0) (vertex 3) = B (vertex 0) (vertex 2) :=
    (polar_comm Q _ _).trans h30
  have h14 : B (vertex 1) (vertex 4) = B (vertex 0) (vertex 2) :=
    (polar_comm Q _ _).trans h41
  intro v
  have hexp : v = v 0 • vertex 0 + v 1 • vertex 1 + v 2 • vertex 2 +
      v 3 • vertex 3 + v 4 • vertex 4 := by
    ext i
    fin_cases i <;> simp [vertex]
  conv_lhs => rw [hexp]
  rw [QuadraticMap.map_add Q
    (v 0 • vertex 0 + v 1 • vertex 1 + v 2 • vertex 2 + v 3 • vertex 3),
    QuadraticMap.map_add Q (v 0 • vertex 0 + v 1 • vertex 1 + v 2 • vertex 2),
    QuadraticMap.map_add Q (v 0 • vertex 0 + v 1 • vertex 1),
    QuadraticMap.map_add Q (v 0 • vertex 0)]
  simp only [Q.map_smul, polar_add_left,
    polar_smul_left, polar_smul_right, hv, smul_eq_mul]
  change _ = polynomial (B (vertex 0) (vertex 1)) (B (vertex 0) (vertex 2)) v
  dsimp only [B] at h12 h23 h34 h13 h24 h04 h03 h14 ⊢
  rw [h12,h23,h34,h13,h24,h04,h03,h14]
  simp only [polynomial]
  ring

theorem eq_zero_of_invariant_singular_submodule
    (Q : QuadraticForm (ZMod 2) Space)
    (hv : ∀ i, Q (vertex i) = 0) (hr : ∀ v, Q (rotate v) = Q v)
    (S : Submodule (ZMod 2) Space) (hS : ∀ x ∈ S, Q x = 0)
    (hdim : 3 ≤ Module.finrank (ZMod 2) S) : Q = 0 := by
  let a := polar Q (vertex 0) (vertex 1)
  let b := polar Q (vertex 0) (vertex 2)
  have hp : ∀ v, Q v = polynomial a b v := invariant_polynomial Q hv hr
  have hab : a = 0 ∧ b = 0 := by
    by_contra hn
    have hn' : a ≠ 0 ∨ b ≠ 0 := by tauto
    have hcard := polynomial_singular_submodule_card_lt_eight a b hn' S
      (fun x hx => (hp x).symm.trans (hS x hx))
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
    simp only [Nat.card_zmod] at hc
    have hbound := Nat.pow_le_pow_right (by decide : 0 < 2) hdim
    rw [←hc] at hbound
    norm_num at hbound
    omega
  ext v
  rw [hp v,hab.1,hab.2]
  simp [polynomial]

theorem eq_zero_of_spanning_invariant_pentagon
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W)
    (f : Space →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hv : ∀ i, Q (f (vertex i)) = 0)
    (hr : ∀ v, Q (f (rotate v)) = Q (f v))
    (E : Submodule (ZMod 2) W) (hE : ∀ x ∈ E, Q x = 0)
    (hcodim : Module.finrank (ZMod 2) (W ⧸ E) ≤ 2) : Q = 0 := by
  let g := E.mkQ.comp f
  have hk : LinearMap.ker g = E.comap f := by
    ext x
    simp [g]
  have hd := g.finrank_range_add_finrank_ker
  have hrange : Module.finrank (ZMod 2) g.range ≤
      Module.finrank (ZMod 2) (W ⧸ E) := Submodule.finrank_le _
  have hspace : Module.finrank (ZMod 2) Space = 5 := by simp [Space]
  rw [hk,hspace] at hd
  have hz : Q.comp f = 0 := eq_zero_of_invariant_singular_submodule
    (Q.comp f) hv hr (E.comap f) (fun x hx => hE (f x) hx) (by omega)
  ext x
  obtain ⟨v,rfl⟩ := hf x
  exact congrArg (fun P : QuadraticForm (ZMod 2) Space => P v) hz

end BinaryPentagon
