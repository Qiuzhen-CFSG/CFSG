module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Model
public import Theory.FieldTheory.Nine
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.GroupTheory.Coset.Card

/-!
# The ordinary centralizer of a nonsplit involution lift in SL₄(3)

If the lift squares to -I, the quadratic-algebra universal property makes
its action multiplication by i on a vector space over F₉ = F₃[i]. The
underlying space has 81 elements, so its dimension over F₉ is two.
Every commuting matrix is F₉-linear, giving a faithful centralizer action
and the order bound |GL₂(9)| = 5760.

The scalar action is constructed from the actual matrix, without a choice
of conjugacy representative or any involution-classification hypothesis.
Passage to the full projective centralizer is handled in the parent module.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

open Matrix Module Submodule Subgroup
noncomputable section
namespace Matrix.PSL4Three.LocalThree.InvolutionCentralizer
private abbrev V := Fin 4 → ZMod 3
private abbrev C (g : SL) := centralizer ({g} : Set SL)
private def act (g : SL) : V ≃ₗ[ZMod 3] V := SpecialLinearGroup.toLin' g

private def nineAction (g : SL) (hsq : (g : Mat) * (g : Mat) = -1) :
    FiniteField.Nine →ₐ[ZMod 3] Module.End (ZMod 3) V :=
  QuadraticAlgebra.lift ⟨Matrix.toLin' (g : Mat), by
    change Matrix.toLin' (g : Mat) ∘ₗ Matrix.toLin' (g : Mat) = _
    rw [← Matrix.toLin'_mul, hsq]
    simp
    rfl⟩

/-- The quadratic-field action bounds the ordinary centralizer order. -/
public theorem nonsplit_card_dvd (g : SL) (hsq : (g : Mat) * (g : Mat) = -1) :
    Nat.card (centralizer ({g} : Set SL)) ∣ 5760 := by
  let : Module FiniteField.Nine V := Module.compHom V (nineAction g hsq).toRingHom
  have smul_eq (z : FiniteField.Nine) (v : V) :
      z • v = z.re • v + z.im • act g v := rfl
  have hd : finrank FiniteField.Nine V = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := FiniteField.Nine) (V := V)
    have hV : Nat.card V = 81 := by
      simp [V]
    rw [hV, FiniteField.Nine.natCard] at h
    have hh : (9 : ℕ) ^ 2 = 9 ^ finrank FiniteField.Nine V := h
    exact (Nat.pow_right_injective (by decide : 1 < (9 : ℕ)) hh).symm
  let l (x : C g) : V →ₗ[FiniteField.Nine] V :=
    { toFun := act x.val
      map_add' := map_add _
      map_smul' := by
        intro z v
        simp only [smul_eq, map_add, map_smul, RingHom.id_apply]
        congr 1
        congr 1
        have he := congrArg (fun t : SL => act t v) (x.property g (by simp))
        simpa only [act, map_mul, LinearEquiv.mul_apply] using he.symm }
  let f : C g →* (V ≃ₗ[FiniteField.Nine] V) :=
    { toFun := fun x => LinearEquiv.ofInjectiveEndo (l x) (act x.val).injective
      map_one' := by
        apply LinearEquiv.ext
        intro v
        change act 1 v = v
        simp [act]
      map_mul' := by
        intro x y
        apply LinearEquiv.ext
        intro v
        change act (x.val * y.val) v = act x.val (act y.val v)
        simp only [act, map_mul, LinearEquiv.mul_apply] }
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun t : V ≃ₗ[FiniteField.Nine] V => t v) h
  have hc := Subgroup.card_dvd_of_injective f hinj
  let b := Module.finBasisOfFinrankEq FiniteField.Nine V hd
  let e := (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv FiniteField.Nine V)
  have hcard : Nat.card (V ≃ₗ[FiniteField.Nine] V) = 5760 := by
    rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    simp [Fin.prod_univ_two]
  rwa [hcard] at hc
end Matrix.PSL4Three.LocalThree.InvolutionCentralizer
