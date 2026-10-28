module

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.ConjFinite

/-!
# Characteristic-polynomial parameters for the actual G₂ model

The action here is the defining action of the full split-octonion automorphism
group. Its characteristic polynomial, and hence its coefficients of degrees
seven and six, are invariant under conjugation in that group. Odd-order
elements act semisimply in characteristic two, also after extending scalars:
their actions are annihilated by the separable polynomial `X^m - 1`.

`classPolynomial a b` records the degree-eight polynomial expected from the
rank-two torus. This module proves that its two parameters can be recovered
and transported along field maps. It does not assert that every odd-order
element has this polynomial or that the parameters separate classes.

Source context: the rank-two semisimple class count underlying Steinberg's
theorem, GLS III, 2.8.2 (`refs/KGroup/GLS3/chapter2.tex`), used for G₂ in
Aschbacher--Smith, G.9.3, printed pp.356--357 of `refs/quasithin.pdf`.
The octonion conventions are those of the licensed ATLAS port; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

namespace Atlas.G2.PRegularClasses

open Polynomial

variable {F : Type*} [Field F]

/-- The defining octonion action as a linear endomorphism. -/
def action (g : Model F) : Module.End F (Atlas.SplitOctonion.Carrier F) :=
  g.val.toLinearMap

theorem action_pow_orderOf (g : Model F) : action g ^ orderOf g = 1 := by
  let ρ : Model F →* Module.End F (Atlas.SplitOctonion.Carrier F) :=
    { toFun := action, map_one' := rfl, map_mul' := fun _ _ => rfl }
  change ρ g ^ orderOf g = 1
  rw [← map_pow, pow_orderOf_eq_one, map_one]

/-- The actual degree-eight characteristic polynomial. -/
noncomputable def charpoly (g : Model F) : F[X] := (action g).charpoly

theorem charpoly_eq_matrix (g : Model F) :
    charpoly g = (LinearMap.toMatrix (Pi.basisFun F (Fin 8))
      (Pi.basisFun F (Fin 8)) (action g)).charpoly :=
  (LinearMap.charpoly_toMatrix (action g) (Pi.basisFun F (Fin 8))).symm

theorem charpoly_eq_of_isConj (g h : Model F) (hc : IsConj g h) :
    charpoly g = charpoly h := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  exact (c.val.charpoly_conj (action g)).symm

/-- Semisimplicity of the defining action of an odd-order element. -/
theorem isSemisimple_action [CharP F 2] (g : Model F) (hg : ¬ 2 ∣ orderOf g) :
    (action g).IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C' 2 (orderOf g) (1 : F) hg one_ne_zero).squarefree
  simp [action_pow_orderOf]

/-- The same semisimplicity statement over a characteristic-two extension. -/
theorem isSemisimple_baseChange {K : Type*} [Field K] [Algebra F K] [CharP K 2]
    (g : Model F) (hg : ¬ 2 ∣ orderOf g) :
    Module.End.IsSemisimple ((action g).baseChange K) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C' 2 (orderOf g) (1 : K) hg one_ne_zero).squarefree
  simp only [map_sub, Polynomial.aeval_X_pow, map_one]
  rw [← LinearMap.baseChange_pow, action_pow_orderOf, LinearMap.baseChange_one, sub_self]

/-- The two-parameter polynomial of the eight-dimensional torus action in
characteristic two. The missing degree-four term is intentional. -/
noncomputable def classPolynomial (a b : F) : F[X] :=
  X ^ 8 + C a * X ^ 7 + C b * X ^ 6 + C (a ^ 2 + a) * X ^ 5 +
    C (a ^ 2 + a) * X ^ 3 + C b * X ^ 2 + C a * X + 1

@[simp] theorem classPolynomial_coeff_seven (a b : F) :
    (classPolynomial a b).coeff 7 = a := by
  simp only [classPolynomial, coeff_add, coeff_C_mul_X_pow, coeff_X_pow,
    coeff_C_mul_X, coeff_one]
  norm_num

@[simp] theorem classPolynomial_coeff_six (a b : F) :
    (classPolynomial a b).coeff 6 = b := by
  simp only [classPolynomial, coeff_add, coeff_C_mul_X_pow, coeff_X_pow,
    coeff_C_mul_X, coeff_one]
  norm_num

theorem classPolynomial_injective :
    Function.Injective (fun p : F × F => classPolynomial p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · simpa only [classPolynomial_coeff_seven] using congrArg (fun f : F[X] => f.coeff 7) h
  · simpa only [classPolynomial_coeff_six] using congrArg (fun f : F[X] => f.coeff 6) h

@[simp] theorem classPolynomial_map {K : Type*} [Field K] (f : F →+* K) (a b : F) :
    (classPolynomial a b).map f = classPolynomial (f a) (f b) := by
  simp only [classPolynomial, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, map_X, map_C, Polynomial.map_one, map_add, map_pow]

/-- A two-parameter polynomial identity over an extension descends to the
original field; its parameters must be the original coefficients. -/
theorem eq_classPolynomial_of_map_eq {K : Type*} [Field K]
    (f : F →+* K) (p : F[X]) (a b : K) (hp : p.map f = classPolynomial a b) :
    p = classPolynomial (p.coeff 7) (p.coeff 6) := by
  have h₁ : f (p.coeff 7) = a := by
    simpa only [coeff_map, classPolynomial_coeff_seven] using
      congrArg (fun r : K[X] => r.coeff 7) hp
  have h₂ : f (p.coeff 6) = b := by
    simpa only [coeff_map, classPolynomial_coeff_six] using
      congrArg (fun r : K[X] => r.coeff 6) hp
  apply Polynomial.map_injective f f.injective
  rw [classPolynomial_map, h₁, h₂]
  exact hp

/-- The two actual coefficients used to encode a conjugacy class. -/
noncomputable def parameters (g : Model F) : F × F :=
  ((charpoly g).coeff 7, (charpoly g).coeff 6)

/-- The coefficient invariant on the actual conjugacy-class quotient. -/
noncomputable def classParameters : ConjClasses (Model F) → F × F :=
  Quotient.lift parameters (fun g h hc => by
    simp only [parameters, charpoly_eq_of_isConj g h hc])

@[simp] theorem classParameters_mk (g : Model F) :
    classParameters (ConjClasses.mk g) = parameters g := rfl

end Atlas.G2.PRegularClasses
