module
public import Theory.Representation.UniformBinaryQuadraticRadical
public import Theory.LinearAlgebra.BinaryPentagon
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The singular-subspace bound for the uniform binary five-point space

The coordinate-singular quadratic form with uniform off-diagonal polar
is the complete pentagon polynomial. The existing small certificate
therefore bounds every singular subspace by dimension two. Pulling back
a subspace along its literal orbit map gives codimension at least three.
This is the five-point input to elementary-center containment in the
normal row of Aschbacher–Smith 14.2.16/F.1.12.
-/

public section
namespace UniformBinaryPolar
open QuadraticMap Module

private theorem five_polynomial
    (Q : QuadraticForm (ZMod 2) (V 5))
    (hB : Q.polarBilin = form 5) (hQ : ∀ i, Q (Pi.single i 1) = 0) :
    ∀ v, Q v = BinaryPentagon.polynomial 1 1 v := by
  classical
  have hp (i j : Fin 5) :
      polar Q (Pi.single i 1) (Pi.single j 1) = if i = j then 0 else 1 := by
    rw [←polarBilin_apply_apply,hB,form_apply_basis]
    by_cases he : i = j
    · subst j
      simp [Pi.single_apply,CharTwo.add_self_eq_zero]
    · simp [Pi.single_apply,he]
  intro v
  have hexp : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 +
      v 3 • Pi.single 3 1 + v 4 • Pi.single 4 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hexp]
  rw [QuadraticMap.map_add Q
    (v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 + v 3 • Pi.single 3 1),
    QuadraticMap.map_add Q (v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1),
    QuadraticMap.map_add Q (v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1),
    QuadraticMap.map_add Q (v 0 • Pi.single 0 1)]
  simp only [Q.map_smul,polar_add_left,polar_smul_left,polar_smul_right,hQ,smul_eq_mul,hp]
  norm_num [BinaryPentagon.polynomial]
  simp only [if_neg (by decide : (0 : Fin 5) ≠ 2),
    if_neg (by decide : (1 : Fin 5) ≠ 2),
    if_neg (by decide : (0 : Fin 5) ≠ 3),
    if_neg (by decide : (1 : Fin 5) ≠ 3),
    if_neg (by decide : (2 : Fin 5) ≠ 3),
    if_neg (by decide : (0 : Fin 5) ≠ 4),
    if_neg (by decide : (1 : Fin 5) ≠ 4),
    if_neg (by decide : (2 : Fin 5) ≠ 4),
    if_neg (by decide : (3 : Fin 5) ≠ 4)]
  ring

/-- The binary five-point uniform quadratic space has no singular
three-dimensional subspace, including its singular constant radical. -/
theorem five_singular_submodule_finrank_le_two
    (Q : QuadraticForm (ZMod 2) (V 5))
    (hB : Q.polarBilin = form 5) (hQ : ∀ i, Q (Pi.single i 1) = 0)
    (S : Submodule (ZMod 2) (V 5)) (hS : ∀ x ∈ S, Q x = 0) :
    finrank (ZMod 2) S ≤ 2 := by
  have hc := BinaryPentagon.polynomial_singular_submodule_card_lt_eight
    1 1 (Or.inl (by decide)) S
    (fun x hx => (five_polynomial Q hB hQ x).symm.trans (hS x hx))
  have hs := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
  rw [Nat.card_zmod] at hs
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ finrank (ZMod 2) S by omega)
  rw [←hs] at hh
  norm_num at hh
  exact Nat.not_le_of_gt hc hh

/-- A singular subspace in a surjective five-point quadratic realization
has codimension at least three. -/
theorem five_orbit_singular_codimension_ge_three
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W)
    (f : V 5 →ₗ[ZMod 2] W)
    (hB : Q.polarBilin.compl₁₂ f f = form 5)
    (hQ : ∀ i, Q (f (Pi.single i 1)) = 0)
    (E : Submodule (ZMod 2) W) (hE : ∀ x ∈ E, Q x = 0) :
    3 ≤ finrank (ZMod 2) (W ⧸ E) := by
  let g := E.mkQ.comp f
  have hk : LinearMap.ker g = E.comap f := by
    ext x
    simp [g]
  have hd := g.finrank_range_add_finrank_ker
  have hr : finrank (ZMod 2) g.range ≤ finrank (ZMod 2) (W ⧸ E) :=
    Submodule.finrank_le _
  have hs := five_singular_submodule_finrank_le_two (Q.comp f)
    ((QuadraticMap.polarBilin_comp Q f).trans hB) hQ (E.comap f)
    (fun x hx => hE (f x) hx)
  have hn : finrank (ZMod 2) (V 5) = 5 := by simp [V]
  rw [hk,hn] at hd
  omega
end UniformBinaryPolar
