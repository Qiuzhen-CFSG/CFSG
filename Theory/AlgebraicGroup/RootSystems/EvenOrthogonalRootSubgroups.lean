module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinIsogeny
public import Theory.AlgebraicGroup.RootSystems.Classical
public import Theory.AlgebraicGroup.RootSystems.HyperbolicStandardSplitForm
public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Representations.Matrix
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit root subgroups for the split even orthogonal group

This module constructs the four elementary orthogonal curves indexed by a
standard type-D root `s e_i + t e_j`: upper and transposed-upper curves for the
two mixed signs, and the two skew curves for the equal signs.  Their coordinate
formulas preserve `hyperbolicForm` over every field, including characteristic
two, and make the parameter additive and recoverable from one matrix
coefficient.

Over an algebraically closed field and in hyperbolic rank at least four, each
elementary point is a single commutator with a diagonal isometry.  The split
Spin image carrier theorem therefore places the whole curve exactly in
`evenSpinActionImageClosedSubgroup`.  Affine matrix and inverse-matrix
coefficients give a regular morphism from `KPlus`; parameter recovery makes it
an isomorphism onto its closed image and hence a one-parameter subgroup.

The final conjugation theorem records the characteristic associated to
`typeDRootEmbedding`: inverse conjugation by the general hyperbolic diagonal
with entries `d` scales the parameter by `d_i^{-s} d_j^{-t}`.  Membership of
that diagonal in a chosen Omega torus and exhaustiveness of all torus roots are
deliberately left to the later root-realization module.  The elementary
commutator argument is the one formerly embedded in the natural
irreducibility proof.  It is the elementary-matrix construction underlying
the standard root subgroups in GLS, Part I, Chapter A, Sections 1.9--1.10; no
type-D classification result is used here.
-/

universe u

open scoped BigOperators commutatorElement

namespace Theory.AlgebraicGroup

open StandardRootSystem

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] public def hyperbolicUpperRootLinearEquiv (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n where
  toFun z :=
    (z.1 + (a * z.1 j) • Pi.single i 1,
      z.2 - (a * z.2 i) • Pi.single j 1)
  invFun z :=
    (z.1 + ((-a) * z.1 j) • Pi.single i 1,
      z.2 - ((-a) * z.2 i) • Pi.single j 1)
  left_inv z := by
    classical
    apply Prod.ext <;> funext p
    · by_cases hp : p = i
      · subst p
        simp [Pi.single_apply, hij]
      · simp [Pi.single_apply, hp, hij]
    · by_cases hp : p = j
      · subst p
        simp [Pi.single_apply, hij]
      · simp [Pi.single_apply, hp, hij]
  right_inv z := by
    classical
    apply Prod.ext <;> funext p
    · by_cases hp : p = i
      · subst p
        simp [Pi.single_apply, hij]
      · simp [Pi.single_apply, hp, hij]
    · by_cases hp : p = j
      · subst p
        simp [Pi.single_apply, hij]
      · simp [Pi.single_apply, hp, hij]
  map_add' x y := by
    apply Prod.ext <;> funext p
    · simp [mul_add]
      ring
    · simp [mul_add]
      ring
  map_smul' c x := by
    apply Prod.ext <;> funext p
    · simp [mul_assoc]
      ring
    · simp [mul_assoc]
      ring

@[expose] public noncomputable def hyperbolicUpperRoot (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    (hyperbolicForm (k := k) n).IsometryEquiv (hyperbolicForm n) where
  toLinearEquiv := hyperbolicUpperRootLinearEquiv n i j hij a
  map_app' z := by
    classical
    simp only [hyperbolicForm_apply, hyperbolicUpperRootLinearEquiv,
      Prod.fst_add, Prod.snd_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [Pi.single_apply, hij]
    simp only [add_mul, Finset.sum_add_distrib]
    simp [hij, Ne.symm hij]
    ring

@[expose] public def hyperbolicLowerRootLinearEquiv (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n where
  toFun z :=
    (z.1, z.2 + (a * z.1 j) • Pi.single i 1 -
      (a * z.1 i) • Pi.single j 1)
  invFun z :=
    (z.1, z.2 + ((-a) * z.1 j) • Pi.single i 1 -
      ((-a) * z.1 i) • Pi.single j 1)
  left_inv z := by
    classical
    apply Prod.ext <;> funext p
    · rfl
    · simp [Pi.single_apply]
      ring
  right_inv z := by
    classical
    apply Prod.ext <;> funext p
    · rfl
    · simp [Pi.single_apply]
      ring
  map_add' x y := by
    apply Prod.ext <;> funext p
    · rfl
    · simp [mul_add]
      ring
  map_smul' c x := by
    apply Prod.ext <;> funext p
    · rfl
    · simp [mul_assoc]
      ring

@[expose] public noncomputable def hyperbolicLowerRoot (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    (hyperbolicForm (k := k) n).IsometryEquiv (hyperbolicForm n) where
  toLinearEquiv := hyperbolicLowerRootLinearEquiv n i j hij a
  map_app' z := by
    classical
    simp only [hyperbolicForm_apply, hyperbolicLowerRootLinearEquiv,
      Prod.fst, Prod.snd_sub, Prod.snd_add, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [Pi.single_apply, hij]
    ring

@[expose] public def hyperbolicSkewUpperRootLinearEquiv (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n where
  toFun z :=
    (z.1 + (a * z.2 j) • Pi.single i 1 -
      (a * z.2 i) • Pi.single j 1, z.2)
  invFun z :=
    (z.1 + ((-a) * z.2 j) • Pi.single i 1 -
      ((-a) * z.2 i) • Pi.single j 1, z.2)
  left_inv z := by
    classical
    apply Prod.ext <;> funext p
    · simp [Pi.single_apply]
      ring
    · rfl
  right_inv z := by
    classical
    apply Prod.ext <;> funext p
    · simp [Pi.single_apply]
      ring
    · rfl
  map_add' x y := by
    apply Prod.ext <;> funext p
    · simp [mul_add]
      ring
    · rfl
  map_smul' c x := by
    apply Prod.ext <;> funext p
    · simp [mul_assoc]
      ring
    · rfl

@[expose] public noncomputable def hyperbolicSkewUpperRoot (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    (hyperbolicForm (k := k) n).IsometryEquiv (hyperbolicForm n) where
  toLinearEquiv := hyperbolicSkewUpperRootLinearEquiv n i j hij a
  map_app' z := by
    classical
    simp only [hyperbolicForm_apply, hyperbolicSkewUpperRootLinearEquiv,
      Prod.fst_sub, Prod.fst_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [Pi.single_apply, hij]
    ring

@[expose] public def hyperbolicScaleLinearEquiv (n : Nat) (i : Fin n) (t : kˣ) :
    HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n where
  toFun z :=
    (fun p => if p = i then (t : k) * z.1 p else z.1 p,
      fun p => if p = i then (↑(t⁻¹) : k) * z.2 p else z.2 p)
  invFun z :=
    (fun p => if p = i then (↑(t⁻¹) : k) * z.1 p else z.1 p,
      fun p => if p = i then (t : k) * z.2 p else z.2 p)
  left_inv z := by
    apply Prod.ext <;> funext p <;> by_cases hp : p = i
    · simp [hp]
    · simp [hp]
    · simp [hp]
    · simp [hp]
  right_inv z := by
    apply Prod.ext <;> funext p <;> by_cases hp : p = i
    · simp [hp]
    · simp [hp]
    · simp [hp]
    · simp [hp]
  map_add' x y := by
    apply Prod.ext <;> funext p <;> by_cases hp : p = i
    · simp [hp, mul_add]
    · simp [hp]
    · simp [hp, mul_add]
    · simp [hp]
  map_smul' c x := by
    apply Prod.ext <;> funext p <;> by_cases hp : p = i
    · simp [hp, mul_assoc, mul_left_comm]
    · simp [hp]
    · simp [hp, mul_assoc, mul_left_comm]
    · simp [hp]

@[expose] public noncomputable def hyperbolicScale (n : Nat) (i : Fin n) (t : kˣ) :
    (hyperbolicForm (k := k) n).IsometryEquiv (hyperbolicForm n) where
  toLinearEquiv := hyperbolicScaleLinearEquiv n i t
  map_app' z := by
    rw [hyperbolicForm_apply, hyperbolicForm_apply]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpi : p = i
    · simp [hyperbolicScaleLinearEquiv, hpi]
      field_simp
    · simp [hyperbolicScaleLinearEquiv, hpi]

@[expose] public noncomputable def hyperbolicUpperRootPoint (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) n) :=
  ⟨(hyperbolicUpperRoot n i j hij a).toLinearEquiv,
    (mem_quadraticIsometrySubgroup _ _).2
      (hyperbolicUpperRoot n i j hij a).map_app⟩

@[expose] public noncomputable def hyperbolicLowerRootPoint (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) n) :=
  ⟨(hyperbolicLowerRoot n i j hij a).toLinearEquiv,
    (mem_quadraticIsometrySubgroup _ _).2
      (hyperbolicLowerRoot n i j hij a).map_app⟩

@[expose] public noncomputable def hyperbolicSkewUpperRootPoint (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) n) :=
  ⟨(hyperbolicSkewUpperRoot n i j hij a).toLinearEquiv,
    (mem_quadraticIsometrySubgroup _ _).2
      (hyperbolicSkewUpperRoot n i j hij a).map_app⟩

@[expose] public noncomputable def hyperbolicScalePoint (n : Nat) (i : Fin n) (t : kˣ) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) n) :=
  ⟨(hyperbolicScale n i t).toLinearEquiv,
    (mem_quadraticIsometrySubgroup _ _).2 (hyperbolicScale n i t).map_app⟩

public lemma hyperbolicUpperRootPoint_commutator (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (t : kˣ) (b : k) :
    ⁅hyperbolicScalePoint n i t, hyperbolicUpperRootPoint n i j hij b⁆ =
      hyperbolicUpperRootPoint n i j hij (((t : k) - 1) * b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · by_cases hpi : p = i
    · subst p
      simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicUpperRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicUpperRoot,
        hyperbolicUpperRootLinearEquiv, hij, Ne.symm hij]
      field_simp
      ring
    · simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicUpperRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicUpperRoot,
        hyperbolicUpperRootLinearEquiv, hpi, hij, Ne.symm hij]
  · by_cases hpj : p = j
    · subst p
      simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicUpperRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicUpperRoot,
        hyperbolicUpperRootLinearEquiv, hij, Ne.symm hij]
      field_simp
      ring
    · by_cases hpi : p = i
      · subst p
        simp [commutatorElement_def, hyperbolicScalePoint,
          hyperbolicUpperRootPoint, hyperbolicScale,
          hyperbolicScaleLinearEquiv, hyperbolicUpperRoot,
          hyperbolicUpperRootLinearEquiv, hpj, hij, Ne.symm hij]
      · simp [commutatorElement_def, hyperbolicScalePoint,
          hyperbolicUpperRootPoint, hyperbolicScale,
          hyperbolicScaleLinearEquiv, hyperbolicUpperRoot,
          hyperbolicUpperRootLinearEquiv, hpi, hpj, hij, Ne.symm hij]

public lemma hyperbolicLowerRootPoint_commutator (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (t : kˣ) (b : k) :
    ⁅hyperbolicScalePoint n i t, hyperbolicLowerRootPoint n i j hij b⁆ =
      hyperbolicLowerRootPoint n i j hij (((↑(t⁻¹) : k) - 1) * b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · by_cases hpi : p = i
    · subst p
      simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicLowerRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicLowerRoot,
        hyperbolicLowerRootLinearEquiv, hij, Ne.symm hij]
    · simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicLowerRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicLowerRoot,
        hyperbolicLowerRootLinearEquiv, hpi, hij, Ne.symm hij]
  · by_cases hpi : p = i
    · subst p
      simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicLowerRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicLowerRoot,
        hyperbolicLowerRootLinearEquiv, hij, Ne.symm hij]
      field_simp
      ring
    · by_cases hpj : p = j
      · subst p
        simp [commutatorElement_def, hyperbolicScalePoint,
          hyperbolicLowerRootPoint, hyperbolicScale,
          hyperbolicScaleLinearEquiv, hyperbolicLowerRoot,
          hyperbolicLowerRootLinearEquiv, hij, Ne.symm hij]
        field_simp
        ring
      · simp [commutatorElement_def, hyperbolicScalePoint,
          hyperbolicLowerRootPoint, hyperbolicScale,
          hyperbolicScaleLinearEquiv, hyperbolicLowerRoot,
          hyperbolicLowerRootLinearEquiv, hpi, hpj, hij, Ne.symm hij]

public lemma hyperbolicSkewUpperRootPoint_commutator (n : Nat)
    (i j : Fin n) (hij : i ≠ j) (t : kˣ) (b : k) :
    ⁅hyperbolicScalePoint n i t, hyperbolicSkewUpperRootPoint n i j hij b⁆ =
      hyperbolicSkewUpperRootPoint n i j hij (((t : k) - 1) * b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · by_cases hpi : p = i
    · subst p
      simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicSkewUpperRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicSkewUpperRoot,
        hyperbolicSkewUpperRootLinearEquiv, hij, Ne.symm hij]
      field_simp
      ring
    · by_cases hpj : p = j
      · subst p
        simp [commutatorElement_def, hyperbolicScalePoint,
          hyperbolicSkewUpperRootPoint, hyperbolicScale,
          hyperbolicScaleLinearEquiv, hyperbolicSkewUpperRoot,
          hyperbolicSkewUpperRootLinearEquiv, hij, Ne.symm hij]
        field_simp
        ring
      · simp [commutatorElement_def, hyperbolicScalePoint,
          hyperbolicSkewUpperRootPoint, hyperbolicScale,
          hyperbolicScaleLinearEquiv, hyperbolicSkewUpperRoot,
          hyperbolicSkewUpperRootLinearEquiv, hpi, hpj, hij, Ne.symm hij]
  · by_cases hpi : p = i
    · subst p
      simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicSkewUpperRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicSkewUpperRoot,
        hyperbolicSkewUpperRootLinearEquiv, hij, Ne.symm hij]
    · simp [commutatorElement_def, hyperbolicScalePoint,
        hyperbolicSkewUpperRootPoint, hyperbolicScale,
        hyperbolicScaleLinearEquiv, hyperbolicSkewUpperRoot,
        hyperbolicSkewUpperRootLinearEquiv, hpi, hij, Ne.symm hij]

public lemma hyperbolicUpperRootPoint_is_commutator (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    ∃ g h : quadraticIsometrySubgroup (hyperbolicForm (k := k) n),
      hyperbolicUpperRootPoint n i j hij a = ⁅g, h⁆ := by
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ht0 : t ≠ 0 := by simpa using fun h => ht (by simp [h])
  have ht1 : t ≠ 1 := by simpa using fun h => ht (by simp [h])
  let u : kˣ := Units.mk0 t ht0
  let b : k := (t - 1)⁻¹ * a
  refine ⟨hyperbolicScalePoint n i u,
    hyperbolicUpperRootPoint n i j hij b, ?_⟩
  rw [hyperbolicUpperRootPoint_commutator]
  congr 1
  dsimp [u, b]
  field_simp [sub_ne_zero.mpr ht1]

public lemma hyperbolicLowerRootPoint_is_commutator (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) :
    ∃ g h : quadraticIsometrySubgroup (hyperbolicForm (k := k) n),
      hyperbolicLowerRootPoint n i j hij a = ⁅g, h⁆ := by
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ht0 : t ≠ 0 := by simpa using fun h => ht (by simp [h])
  have ht1 : t ≠ 1 := by simpa using fun h => ht (by simp [h])
  let u : kˣ := Units.mk0 t ht0
  have hu1 : (↑(u⁻¹) : k) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact inv_ne_one.mpr ht1
  let b : k := ((↑(u⁻¹) : k) - 1)⁻¹ * a
  refine ⟨hyperbolicScalePoint n i u,
    hyperbolicLowerRootPoint n i j hij b, ?_⟩
  rw [hyperbolicLowerRootPoint_commutator]
  congr 1
  dsimp [b]
  field_simp [hu1]

public lemma hyperbolicSkewUpperRootPoint_is_commutator
    (n : Nat) (i j : Fin n) (hij : i ≠ j) (a : k) :
    ∃ g h : quadraticIsometrySubgroup (hyperbolicForm (k := k) n),
      hyperbolicSkewUpperRootPoint n i j hij a = ⁅g, h⁆ := by
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ht0 : t ≠ 0 := by simpa using fun h => ht (by simp [h])
  have ht1 : t ≠ 1 := by simpa using fun h => ht (by simp [h])
  let u : kˣ := Units.mk0 t ht0
  let b : k := (t - 1)⁻¹ * a
  refine ⟨hyperbolicScalePoint n i u,
    hyperbolicSkewUpperRootPoint n i j hij b, ?_⟩
  rw [hyperbolicSkewUpperRootPoint_commutator]
  congr 1
  dsimp [u, b]
  field_simp [sub_ne_zero.mpr ht1]

private lemma hyperbolicUpperRootPoint_zero (n : Nat) (i j : Fin n)
    (hij : i ≠ j) :
    hyperbolicUpperRootPoint (k := k) n i j hij 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p <;>
    simp [hyperbolicUpperRootPoint, hyperbolicUpperRoot,
      hyperbolicUpperRootLinearEquiv]

private lemma hyperbolicUpperRootPoint_add (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a b : k) :
    hyperbolicUpperRootPoint n i j hij (a + b) =
      hyperbolicUpperRootPoint n i j hij a *
        hyperbolicUpperRootPoint n i j hij b := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · by_cases hp : p = i <;> simp [LinearEquiv.mul_apply, hyperbolicUpperRootPoint,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv, mul_add,
      Pi.single_apply, hp, hij, Ne.symm hij]
    all_goals ring
  · by_cases hp : p = j <;> simp [LinearEquiv.mul_apply, hyperbolicUpperRootPoint,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv, mul_add,
      Pi.single_apply, hp, hij, Ne.symm hij]
    all_goals ring

private lemma hyperbolicLowerRootPoint_zero (n : Nat) (i j : Fin n)
    (hij : i ≠ j) :
    hyperbolicLowerRootPoint (k := k) n i j hij 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p <;>
    simp [hyperbolicLowerRootPoint, hyperbolicLowerRoot,
      hyperbolicLowerRootLinearEquiv]

private lemma hyperbolicLowerRootPoint_add (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a b : k) :
    hyperbolicLowerRootPoint n i j hij (a + b) =
      hyperbolicLowerRootPoint n i j hij a *
        hyperbolicLowerRootPoint n i j hij b := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · rfl
  · by_cases hpi : p = i
    · subst p
      simp [LinearEquiv.mul_apply, hyperbolicLowerRootPoint,
        hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv, mul_add,
        Pi.single_apply, hij, Ne.symm hij]
      ring
    · by_cases hpj : p = j <;>
        simp [LinearEquiv.mul_apply, hyperbolicLowerRootPoint,
          hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv, mul_add,
          Pi.single_apply, hpi, hpj, hij, Ne.symm hij]
      all_goals ring

private lemma hyperbolicSkewUpperRootPoint_zero (n : Nat) (i j : Fin n)
    (hij : i ≠ j) :
    hyperbolicSkewUpperRootPoint (k := k) n i j hij 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p <;>
    simp [hyperbolicSkewUpperRootPoint, hyperbolicSkewUpperRoot,
      hyperbolicSkewUpperRootLinearEquiv]

private lemma hyperbolicSkewUpperRootPoint_add (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a b : k) :
    hyperbolicSkewUpperRootPoint n i j hij (a + b) =
      hyperbolicSkewUpperRootPoint n i j hij a *
        hyperbolicSkewUpperRootPoint n i j hij b := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · by_cases hpi : p = i
    · subst p
      simp [LinearEquiv.mul_apply, hyperbolicSkewUpperRootPoint,
        hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv, mul_add,
        Pi.single_apply, hij, Ne.symm hij]
      ring
    · by_cases hpj : p = j <;>
        simp [LinearEquiv.mul_apply, hyperbolicSkewUpperRootPoint,
          hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv, mul_add,
          Pi.single_apply, hpi, hpj, hij, Ne.symm hij]
      all_goals ring
  · rfl

@[expose] public noncomputable def evenOrthogonalRootIsometry (n : Nat) :
    TypeDRootIndex n → k →
      (hyperbolicForm (k := k) n).IsometryEquiv (hyperbolicForm n)
  | ⟨⟨⟨i, j⟩, hij⟩, s, t⟩, a =>
      if hs : s.1 = 1 then
        if ht : t.1 = 1 then
          hyperbolicSkewUpperRoot n i j hij.ne a
        else
          hyperbolicUpperRoot n i j hij.ne a
      else if ht : t.1 = 1 then
        hyperbolicUpperRoot n j i hij.ne' a
      else
        hyperbolicLowerRoot n i j hij.ne a

@[expose] public noncomputable def evenOrthogonalRootQuadraticPoint (n : Nat)
    (r : TypeDRootIndex n) (a : k) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) n) :=
  ⟨(evenOrthogonalRootIsometry n r a).toLinearEquiv,
    (mem_quadraticIsometrySubgroup _ _).2
      (evenOrthogonalRootIsometry n r a).map_app⟩

public lemma evenOrthogonalRoot_preserves_hyperbolicForm (n : Nat)
    (r : TypeDRootIndex n) (a : k) (z : HyperbolicSpace k n) :
    hyperbolicForm n (evenOrthogonalRootIsometry n r a z) =
      hyperbolicForm n z :=
  (evenOrthogonalRootIsometry n r a).map_app z

public lemma evenOrthogonalRootQuadraticPoint_zero (n : Nat)
    (r : TypeDRootIndex n) :
    evenOrthogonalRootQuadraticPoint (k := k) n r 0 = 1 := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t <;>
    norm_num [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry]
  all_goals
    apply LinearEquiv.ext
    intro z
    apply Prod.ext <;> funext p <;>
      simp [hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
        hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
        hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv]

public lemma evenOrthogonalRootQuadraticPoint_add (n : Nat)
    (r : TypeDRootIndex n) (a b : k) :
    evenOrthogonalRootQuadraticPoint n r (a + b) =
      evenOrthogonalRootQuadraticPoint n r a *
        evenOrthogonalRootQuadraticPoint n r b := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t <;>
    norm_num only [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      reduceDIte]
  · exact hyperbolicLowerRootPoint_add n i j hij.ne a b
  · exact hyperbolicUpperRootPoint_add n j i hij.ne' a b
  · exact hyperbolicUpperRootPoint_add n i j hij.ne a b
  · exact hyperbolicSkewUpperRootPoint_add n i j hij.ne a b

public lemma evenOrthogonalRootQuadraticPoint_is_commutator (n : Nat)
    (r : TypeDRootIndex n) (a : k) :
    ∃ g h : quadraticIsometrySubgroup (hyperbolicForm (k := k) n),
      evenOrthogonalRootQuadraticPoint n r a = ⁅g, h⁆ := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t <;>
    norm_num only [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      reduceDIte]
  · exact hyperbolicLowerRootPoint_is_commutator n i j hij.ne a
  · exact hyperbolicUpperRootPoint_is_commutator n j i hij.ne' a
  · exact hyperbolicUpperRootPoint_is_commutator n i j hij.ne a
  · exact hyperbolicSkewUpperRootPoint_is_commutator n i j hij.ne a

@[expose] public noncomputable def evenOrthogonalRootSource (n : Nat) :
    TypeDRootIndex n → HyperbolicSpace k n
  | ⟨⟨⟨i, j⟩, _⟩, s, t⟩ =>
      if s.1 = 1 then
        if t.1 = 1 then (0, Pi.single j 1)
        else (Pi.single j 1, 0)
      else if t.1 = 1 then (Pi.single i 1, 0)
      else (Pi.single j 1, 0)

@[expose] public noncomputable def evenOrthogonalRootCoordinate (n : Nat) :
    TypeDRootIndex n → Module.Dual k (HyperbolicSpace k n)
  | ⟨⟨⟨i, j⟩, _⟩, s, t⟩ =>
      if s.1 = 1 then
        if t.1 = 1 then LinearMap.proj i ∘ₗ
          LinearMap.fst k (Fin n → k) (Fin n → k)
        else LinearMap.proj i ∘ₗ
          LinearMap.fst k (Fin n → k) (Fin n → k)
      else if t.1 = 1 then LinearMap.proj j ∘ₗ
        LinearMap.fst k (Fin n → k) (Fin n → k)
      else LinearMap.proj i ∘ₗ
        LinearMap.snd k (Fin n → k) (Fin n → k)

public lemma evenOrthogonalRoot_parameter_recovery (n : Nat)
    (r : TypeDRootIndex n) (a : k) :
    evenOrthogonalRootCoordinate n r
        ((evenOrthogonalRootQuadraticPoint n r a).1
          (evenOrthogonalRootSource n r)) = a := by
  classical
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t <;>
    norm_num [evenOrthogonalRootCoordinate, evenOrthogonalRootSource,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, hij.ne, hij.ne']

@[expose] public noncomputable def hyperbolicDiagonalLinearEquiv (n : Nat)
    (d : Fin n → kˣ) : HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n where
  toFun z :=
    (fun p => (d p : k) * z.1 p,
      fun p => (↑((d p)⁻¹) : k) * z.2 p)
  invFun z :=
    (fun p => (↑((d p)⁻¹) : k) * z.1 p,
      fun p => (d p : k) * z.2 p)
  left_inv z := by
    apply Prod.ext <;> funext p <;> simp
  right_inv z := by
    apply Prod.ext <;> funext p <;> simp
  map_add' x y := by
    apply Prod.ext <;> funext p <;> simp [mul_add]
  map_smul' c x := by
    apply Prod.ext <;> funext p <;> simp [mul_assoc, mul_left_comm]

@[expose] public noncomputable def hyperbolicDiagonalIsometry (n : Nat)
    (d : Fin n → kˣ) :
    (hyperbolicForm (k := k) n).IsometryEquiv (hyperbolicForm n) where
  toLinearEquiv := hyperbolicDiagonalLinearEquiv n d
  map_app' z := by
    rw [hyperbolicForm_apply, hyperbolicForm_apply]
    apply Finset.sum_congr rfl
    intro p hp
    simp [hyperbolicDiagonalLinearEquiv]
    field_simp

@[expose] public noncomputable def hyperbolicDiagonalPoint (n : Nat)
    (d : Fin n → kˣ) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) n) :=
  ⟨(hyperbolicDiagonalIsometry n d).toLinearEquiv,
    (mem_quadraticIsometrySubgroup _ _).2
      (hyperbolicDiagonalIsometry n d).map_app⟩

@[expose] public noncomputable def evenOrthogonalRootScale (n : Nat) :
    TypeDRootIndex n → (Fin n → kˣ) → k
  | ⟨⟨⟨i, j⟩, _⟩, s, t⟩, d =>
      (if s.1 = 1 then (↑((d i)⁻¹) : k) else d i) *
        (if t.1 = 1 then (↑((d j)⁻¹) : k) else d j)

private lemma hyperbolicDiagonal_upper_conjugation (n : Nat)
    (i j : Fin n) (hij : i ≠ j) (d : Fin n → kˣ) (a : k) :
    (hyperbolicDiagonalPoint n d)⁻¹ *
        hyperbolicUpperRootPoint n i j hij a * hyperbolicDiagonalPoint n d =
      hyperbolicUpperRootPoint n i j hij
        (((↑((d i)⁻¹) : k) * d j) * a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · by_cases hpi : p = i
    · subst p
      simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
        hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
        hyperbolicUpperRootPoint, hyperbolicUpperRoot,
        hyperbolicUpperRootLinearEquiv, hij, Ne.symm hij]
      field_simp
    · simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
        hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
        hyperbolicUpperRootPoint, hyperbolicUpperRoot,
        hyperbolicUpperRootLinearEquiv, hpi, hij, Ne.symm hij]
  · by_cases hpj : p = j
    · subst p
      simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
        hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
        hyperbolicUpperRootPoint, hyperbolicUpperRoot,
        hyperbolicUpperRootLinearEquiv, hij, Ne.symm hij]
      field_simp
    · simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
        hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
        hyperbolicUpperRootPoint, hyperbolicUpperRoot,
        hyperbolicUpperRootLinearEquiv, hpj, hij, Ne.symm hij]

private lemma hyperbolicDiagonal_lower_conjugation (n : Nat)
    (i j : Fin n) (hij : i ≠ j) (d : Fin n → kˣ) (a : k) :
    (hyperbolicDiagonalPoint n d)⁻¹ *
        hyperbolicLowerRootPoint n i j hij a * hyperbolicDiagonalPoint n d =
      hyperbolicLowerRootPoint n i j hij (((d i : k) * d j) * a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
      hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
      hyperbolicLowerRootPoint, hyperbolicLowerRoot,
      hyperbolicLowerRootLinearEquiv]
  · by_cases hpi : p = i
    · subst p
      simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
        hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
        hyperbolicLowerRootPoint, hyperbolicLowerRoot,
        hyperbolicLowerRootLinearEquiv, hij, Ne.symm hij]
      field_simp
    · by_cases hpj : p = j
      · subst p
        simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
          hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
          hyperbolicLowerRootPoint, hyperbolicLowerRoot,
          hyperbolicLowerRootLinearEquiv, hij, Ne.symm hij]
        field_simp
      · simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
          hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
          hyperbolicLowerRootPoint, hyperbolicLowerRoot,
          hyperbolicLowerRootLinearEquiv, hpi, hpj, hij, Ne.symm hij]

private lemma hyperbolicDiagonal_skewUpper_conjugation (n : Nat)
    (i j : Fin n) (hij : i ≠ j) (d : Fin n → kˣ) (a : k) :
    (hyperbolicDiagonalPoint n d)⁻¹ *
        hyperbolicSkewUpperRootPoint n i j hij a * hyperbolicDiagonalPoint n d =
      hyperbolicSkewUpperRootPoint n i j hij
        (((↑((d i)⁻¹) : k) * ↑((d j)⁻¹)) * a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext p
  · by_cases hpi : p = i
    · subst p
      simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
        hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
        hyperbolicSkewUpperRootPoint, hyperbolicSkewUpperRoot,
        hyperbolicSkewUpperRootLinearEquiv, hij, Ne.symm hij]
      field_simp
    · by_cases hpj : p = j
      · subst p
        simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
          hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
          hyperbolicSkewUpperRootPoint, hyperbolicSkewUpperRoot,
          hyperbolicSkewUpperRootLinearEquiv, hij, Ne.symm hij]
        field_simp
      · simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
          hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
          hyperbolicSkewUpperRootPoint, hyperbolicSkewUpperRoot,
          hyperbolicSkewUpperRootLinearEquiv, hpi, hpj, hij, Ne.symm hij]
  · simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
      hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
      hyperbolicSkewUpperRootPoint, hyperbolicSkewUpperRoot,
      hyperbolicSkewUpperRootLinearEquiv]

public lemma evenOrthogonalRoot_diagonal_conjugation (n : Nat)
    (r : TypeDRootIndex n) (d : Fin n → kˣ) (a : k) :
    (hyperbolicDiagonalPoint n d)⁻¹ *
        evenOrthogonalRootQuadraticPoint n r a * hyperbolicDiagonalPoint n d =
      evenOrthogonalRootQuadraticPoint n r
        (evenOrthogonalRootScale n r d * a) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t <;>
    norm_num only [evenOrthogonalRootQuadraticPoint,
      evenOrthogonalRootIsometry, evenOrthogonalRootScale, reduceDIte]
  all_goals simp only [if_false, if_true]
  · change (hyperbolicDiagonalPoint n d)⁻¹ *
        hyperbolicLowerRootPoint n i j hij.ne a * hyperbolicDiagonalPoint n d =
      hyperbolicLowerRootPoint n i j hij.ne (((d i : k) * d j) * a)
    exact hyperbolicDiagonal_lower_conjugation n i j hij.ne d a
  · change (hyperbolicDiagonalPoint n d)⁻¹ *
        hyperbolicUpperRootPoint n j i hij.ne' a * hyperbolicDiagonalPoint n d =
      hyperbolicUpperRootPoint n j i hij.ne'
        (((d i : k) * ↑((d j)⁻¹)) * a)
    simpa [mul_comm] using
      hyperbolicDiagonal_upper_conjugation n j i hij.ne' d a
  · change (hyperbolicDiagonalPoint n d)⁻¹ *
        hyperbolicUpperRootPoint n i j hij.ne a * hyperbolicDiagonalPoint n d =
      hyperbolicUpperRootPoint n i j hij.ne
        (((↑((d i)⁻¹) : k) * d j) * a)
    exact hyperbolicDiagonal_upper_conjugation n i j hij.ne d a
  · change (hyperbolicDiagonalPoint n d)⁻¹ *
        hyperbolicSkewUpperRootPoint n i j hij.ne a * hyperbolicDiagonalPoint n d =
      hyperbolicSkewUpperRootPoint n i j hij.ne
        (((↑((d i)⁻¹) : k) * ↑((d j)⁻¹)) * a)
    exact hyperbolicDiagonal_skewUpper_conjugation n i j hij.ne d a

private lemma hyperbolicUpperRoot_affine (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) (z : HyperbolicSpace k n) :
    hyperbolicUpperRoot n i j hij a z =
      z + a • (hyperbolicUpperRoot n i j hij 1 z - z) := by
  apply Prod.ext
  · funext p
    change z.1 p + a * z.1 j * (Pi.single i (1 : k) : Fin n → k) p =
      z.1 p + a * ((z.1 p + 1 * z.1 j *
        (Pi.single i (1 : k) : Fin n → k) p) - z.1 p)
    ring
  · funext p
    change z.2 p - a * z.2 i * (Pi.single j (1 : k) : Fin n → k) p =
      z.2 p + a * ((z.2 p - 1 * z.2 i *
        (Pi.single j (1 : k) : Fin n → k) p) - z.2 p)
    ring

private lemma hyperbolicLowerRoot_affine (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) (z : HyperbolicSpace k n) :
    hyperbolicLowerRoot n i j hij a z =
      z + a • (hyperbolicLowerRoot n i j hij 1 z - z) := by
  apply Prod.ext
  · funext p
    change z.1 p = z.1 p + a * (z.1 p - z.1 p)
    ring
  · funext p
    change z.2 p + a * z.1 j * (Pi.single i (1 : k) : Fin n → k) p -
        a * z.1 i * (Pi.single j (1 : k) : Fin n → k) p =
      z.2 p + a * ((z.2 p + 1 * z.1 j *
        (Pi.single i (1 : k) : Fin n → k) p -
        1 * z.1 i * (Pi.single j (1 : k) : Fin n → k) p) - z.2 p)
    ring

private lemma hyperbolicSkewUpperRoot_affine (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) (z : HyperbolicSpace k n) :
    hyperbolicSkewUpperRoot n i j hij a z =
      z + a • (hyperbolicSkewUpperRoot n i j hij 1 z - z) := by
  apply Prod.ext
  · funext p
    change z.1 p + a * z.2 j * (Pi.single i (1 : k) : Fin n → k) p -
        a * z.2 i * (Pi.single j (1 : k) : Fin n → k) p =
      z.1 p + a * ((z.1 p + 1 * z.2 j *
        (Pi.single i (1 : k) : Fin n → k) p -
        1 * z.2 i * (Pi.single j (1 : k) : Fin n → k) p) - z.1 p)
    ring
  · funext p
    change z.2 p = z.2 p + a * (z.2 p - z.2 p)
    ring

public lemma evenOrthogonalRoot_affine (n : Nat) (r : TypeDRootIndex n)
    (a : k) (z : HyperbolicSpace k n) :
    evenOrthogonalRootIsometry n r a z =
      z + a • (evenOrthogonalRootIsometry n r 1 z - z) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t <;>
    norm_num only [evenOrthogonalRootIsometry, reduceDIte]
  · exact hyperbolicLowerRoot_affine n i j hij.ne a z
  · exact hyperbolicUpperRoot_affine n j i hij.ne' a z
  · exact hyperbolicUpperRoot_affine n i j hij.ne a z
  · exact hyperbolicSkewUpperRoot_affine n i j hij.ne a z

noncomputable def evenOrthogonalRootGeneralLinearPoint (n : Nat)
    (r : TypeDRootIndex n) (a : k) :
    LinearMap.GeneralLinearGroup k (HyperbolicSpace k n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k
      (HyperbolicSpace k n)).symm
    (evenOrthogonalRootQuadraticPoint n r a).1

lemma evenOrthogonalRootGeneralLinearPoint_zero (n : Nat)
    (r : TypeDRootIndex n) :
    evenOrthogonalRootGeneralLinearPoint (k := k) n r 0 = 1 := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (HyperbolicSpace k n)).injective
  simp only [evenOrthogonalRootGeneralLinearPoint, Equiv.apply_symm_apply,
    map_one]
  exact congrArg Subtype.val
    (evenOrthogonalRootQuadraticPoint_zero (k := k) n r)

lemma evenOrthogonalRootGeneralLinearPoint_add (n : Nat)
    (r : TypeDRootIndex n) (a b : k) :
    evenOrthogonalRootGeneralLinearPoint n r (a + b) =
      evenOrthogonalRootGeneralLinearPoint n r a *
        evenOrthogonalRootGeneralLinearPoint n r b := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (HyperbolicSpace k n)).injective
  simp only [evenOrthogonalRootGeneralLinearPoint, Equiv.apply_symm_apply,
    map_mul]
  exact congrArg Subtype.val
    (evenOrthogonalRootQuadraticPoint_add n r a b)

public noncomputable def evenOrthogonalRootPointRepresentation (n : Nat)
    (r : TypeDRootIndex n) :
    Variety.Point (KPlus k) →*
      LinearMap.GeneralLinearGroup k (HyperbolicSpace k n) where
  toFun x := evenOrthogonalRootGeneralLinearPoint n r (x.val PUnit.unit)
  map_one' := by
    rw [show ((1 : Variety.Point (KPlus k)).val PUnit.unit) = 0 by
      rw [← kPlusPoint_coordinate (k := k) (1 : Variety.Point (KPlus k))]
      rfl]
    exact evenOrthogonalRootGeneralLinearPoint_zero n r
  map_mul' x y := by
    rw [kPlusPoint_coordinate_mul]
    exact evenOrthogonalRootGeneralLinearPoint_add n r _ _

private noncomputable def evenOrthogonalRootMatrixCoefficient (n : Nat)
    (r : TypeDRootIndex n)
    (row column : Fin (Module.finrank k (HyperbolicSpace k n))) :
    (KPlus k).PolynomialFunction :=
  let b := Module.finBasis k (HyperbolicSpace k n)
  Variety.PolynomialFunction.ofPolynomial (KPlus k)
    (MvPolynomial.C (b.repr (b column) row) +
      MvPolynomial.X PUnit.unit *
        MvPolynomial.C
          (b.repr (evenOrthogonalRootIsometry n r 1 (b column) - b column) row))

private noncomputable def evenOrthogonalRootInverseMatrixCoefficient (n : Nat)
    (r : TypeDRootIndex n)
    (row column : Fin (Module.finrank k (HyperbolicSpace k n))) :
    (KPlus k).PolynomialFunction :=
  let b := Module.finBasis k (HyperbolicSpace k n)
  Variety.PolynomialFunction.ofPolynomial (KPlus k)
    (MvPolynomial.C (b.repr (b column) row) -
      MvPolynomial.X PUnit.unit *
        MvPolynomial.C
          (b.repr (evenOrthogonalRootIsometry n r 1 (b column) - b column) row))

private lemma evenOrthogonalRootMatrixCoefficient_apply (n : Nat)
    (r : TypeDRootIndex n)
    (row column : Fin (Module.finrank k (HyperbolicSpace k n)))
    (x : Variety.Point (KPlus k)) :
    evenOrthogonalRootMatrixCoefficient n r row column x =
      (Module.finBasis k (HyperbolicSpace k n)).repr
        (((evenOrthogonalRootPointRepresentation n r x :
            LinearMap.GeneralLinearGroup k (HyperbolicSpace k n)) :
          Module.End k (HyperbolicSpace k n))
          ((Module.finBasis k (HyperbolicSpace k n)) column)) row := by
  simp only [evenOrthogonalRootMatrixCoefficient,
    Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun]
  change evalPolynomial x.val _ =
    (Module.finBasis k (HyperbolicSpace k n)).repr
      (evenOrthogonalRootIsometry n r (x.val PUnit.unit)
        ((Module.finBasis k (HyperbolicSpace k n)) column)) row
  simp [evalPolynomial]
  have h := congrArg
    (fun v : HyperbolicSpace k n =>
      (Module.finBasis k (HyperbolicSpace k n)).repr v row)
    (evenOrthogonalRoot_affine n r (x.val PUnit.unit)
      ((Module.finBasis k (HyperbolicSpace k n)) column))
  rw [h]
  by_cases hrow : row = column <;>
    simp [map_add, map_sub, map_smul, Finsupp.single_apply, hrow]

private lemma evenOrthogonalRootGeneralLinearPoint_inv (n : Nat)
    (r : TypeDRootIndex n) (a : k) :
    (evenOrthogonalRootGeneralLinearPoint n r a)⁻¹ =
      evenOrthogonalRootGeneralLinearPoint n r (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← evenOrthogonalRootGeneralLinearPoint_add]
  simp [evenOrthogonalRootGeneralLinearPoint_zero]

private lemma evenOrthogonalRootInverseMatrixCoefficient_apply (n : Nat)
    (r : TypeDRootIndex n)
    (row column : Fin (Module.finrank k (HyperbolicSpace k n)))
    (x : Variety.Point (KPlus k)) :
    evenOrthogonalRootInverseMatrixCoefficient n r row column x =
      (Module.finBasis k (HyperbolicSpace k n)).repr
        (((((evenOrthogonalRootPointRepresentation n r x)⁻¹ :
            LinearMap.GeneralLinearGroup k (HyperbolicSpace k n)) :
          Module.End k (HyperbolicSpace k n))
          ((Module.finBasis k (HyperbolicSpace k n)) column))) row := by
  simp only [evenOrthogonalRootInverseMatrixCoefficient,
    Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun]
  change evalPolynomial x.val _ =
    (Module.finBasis k (HyperbolicSpace k n)).repr
      ((↑((evenOrthogonalRootGeneralLinearPoint n r
          (x.val PUnit.unit))⁻¹) : Module.End k (HyperbolicSpace k n))
        ((Module.finBasis k (HyperbolicSpace k n)) column)) row
  simp [evalPolynomial]
  rw [evenOrthogonalRootGeneralLinearPoint_inv]
  change _ = (Module.finBasis k (HyperbolicSpace k n)).repr
    (evenOrthogonalRootIsometry n r (-x.val PUnit.unit)
      ((Module.finBasis k (HyperbolicSpace k n)) column)) row
  have h := congrArg
    (fun v : HyperbolicSpace k n =>
      (Module.finBasis k (HyperbolicSpace k n)).repr v row)
    (evenOrthogonalRoot_affine n r (-x.val PUnit.unit)
      ((Module.finBasis k (HyperbolicSpace k n)) column))
  rw [h]
  by_cases hrow : row = column <;>
    simp [map_add, map_sub, map_smul, Finsupp.single_apply, hrow]
  all_goals ring

public noncomputable def evenOrthogonalRootAmbientMorphism (n : Nat)
    (r : TypeDRootIndex n) :
    AlgebraicGroup.Morphism (KPlus k) (glVarietyOf k (HyperbolicSpace k n)) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    (Module.finBasis k (HyperbolicSpace k n))
    (evenOrthogonalRootPointRepresentation n r)
    (evenOrthogonalRootMatrixCoefficient n r)
    (evenOrthogonalRootInverseMatrixCoefficient n r)
    (evenOrthogonalRootMatrixCoefficient_apply n r)
    (evenOrthogonalRootInverseMatrixCoefficient_apply n r)

@[simp] public lemma evenOrthogonalRootAmbientMorphism_apply (n : Nat)
    (r : TypeDRootIndex n) (x : Variety.Point (KPlus k)) :
    (evenOrthogonalRootAmbientMorphism n r).onPoints x =
      generalLinearRepresentationPoint
        (Module.finBasis k (HyperbolicSpace k n))
        (evenOrthogonalRootPointRepresentation n r x) := by
  exact generalLinearRepresentationMorphismOfInverseMatrixCoefficient_apply
    (Module.finBasis k (HyperbolicSpace k n))
    (evenOrthogonalRootPointRepresentation n r)
    (evenOrthogonalRootMatrixCoefficient n r)
    (evenOrthogonalRootInverseMatrixCoefficient n r)
    (evenOrthogonalRootMatrixCoefficient_apply n r)
    (evenOrthogonalRootInverseMatrixCoefficient_apply n r) x

/-- The regular root morphism has the explicit elementary quadratic-isometry point. -/
public lemma evenOrthogonalRootAmbientMorphism_linear_points (n : Nat)
    (r : TypeDRootIndex n) (x : Variety.Point (KPlus k)) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
        (glPointEquivOf k (HyperbolicSpace k n)
          (Module.finBasis k (HyperbolicSpace k n))
          ((evenOrthogonalRootAmbientMorphism n r).onPoints x)) =
      (evenOrthogonalRootQuadraticPoint n r (x.val PUnit.unit)).1 := by
  rw [evenOrthogonalRootAmbientMorphism_apply,
    glPointEquivOf_generalLinearRepresentationPoint]
  change LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k
        (HyperbolicSpace k n)).symm
          (evenOrthogonalRootQuadraticPoint n r (x.val PUnit.unit)).1) = _
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (HyperbolicSpace k n)).apply_symm_apply _

public lemma evenOrthogonalRootAmbientMorphism_mem (n : Nat) (hn : 4 ≤ n)
    (r : TypeDRootIndex n) (x : Variety.Point (KPlus k)) :
    (evenOrthogonalRootAmbientMorphism n r).onPoints x ∈
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).toSubgroup := by
  have hrank : 4 ≤ (standardHyperbolicSplit (k := k) n).rank := by
    simpa using hn
  rw [evenSpinActionImageClosedSubgroup_commutator_carrier
    (hyperbolicForm (k := k) n) (standardHyperbolicSplit n) hrank]
  obtain ⟨g, h, hgh⟩ := evenOrthogonalRootQuadraticPoint_is_commutator
    n r (x.val PUnit.unit)
  refine ⟨⟨⁅g, h⁆, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top g) (Subgroup.mem_top h)⟩, ?_⟩
  rw [evenOrthogonalRootAmbientMorphism_apply,
    glPointEquivOf_generalLinearRepresentationPoint]
  simp only [evenOrthogonalRootPointRepresentation,
    evenOrthogonalRootGeneralLinearPoint, Equiv.apply_symm_apply]
  exact (congrArg Subtype.val hgh).symm

@[expose] public noncomputable def evenOrthogonalRootMorphism (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    AlgebraicGroup.Morphism (KPlus k)
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety :=
  (evenOrthogonalRootAmbientMorphism n r).codRestrictClosedSubgroup
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
      (standardHyperbolicSplit n))
    (evenOrthogonalRootAmbientMorphism_mem n hn r)

@[simp] public lemma evenOrthogonalRootMorphism_include_apply (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) (x : Variety.Point (KPlus k)) :
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).includePoint
      ((evenOrthogonalRootMorphism n hn r).onPoints x) =
        (evenOrthogonalRootAmbientMorphism n r).onPoints x :=
  (evenOrthogonalRootAmbientMorphism n r).codRestrictClosedSubgroup_inclusion_apply
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
      (standardHyperbolicSplit n))
    (evenOrthogonalRootAmbientMorphism_mem n hn r) x

public lemma evenOrthogonalRootMorphism_injective (n : Nat) (hn : 4 ≤ n)
    (r : TypeDRootIndex n) :
    Function.Injective (evenOrthogonalRootMorphism (k := k) n hn r).onPoints := by
  intro x y hxy
  apply (additiveGroupPointEquiv k).injective
  change x.val PUnit.unit = y.val PUnit.unit
  have hambient := congrArg
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
      (standardHyperbolicSplit n)).includePoint hxy
  rw [evenOrthogonalRootMorphism_include_apply,
    evenOrthogonalRootMorphism_include_apply,
    evenOrthogonalRootAmbientMorphism_apply,
    evenOrthogonalRootAmbientMorphism_apply] at hambient
  have hgl := congrArg
    (glPointEquivOf k (HyperbolicSpace k n)
      (Module.finBasis k (HyperbolicSpace k n))) hambient
  simp only [glPointEquivOf_generalLinearRepresentationPoint,
    evenOrthogonalRootPointRepresentation] at hgl
  have hlinear := congrArg
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)) hgl
  simp only [evenOrthogonalRootGeneralLinearPoint, Equiv.apply_symm_apply] at hlinear
  change (evenOrthogonalRootQuadraticPoint n r (x.val PUnit.unit)).1 =
    (evenOrthogonalRootQuadraticPoint n r (y.val PUnit.unit)).1 at hlinear
  have hvalue := congrArg
    (fun f : HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n =>
      evenOrthogonalRootCoordinate n r (f (evenOrthogonalRootSource n r))) hlinear
  simpa only [evenOrthogonalRoot_parameter_recovery] using hvalue

private noncomputable def evenOrthogonalRootAmbientMatrixCoordinate (n : Nat)
    (i j : Fin (Module.finrank k (HyperbolicSpace k n))) :
    Variety.PolynomialFunction (glVarietyOf k (HyperbolicSpace k n)) := by
  change Variety.PolynomialFunction
    (glVariety (Module.finrank k (HyperbolicSpace k n)) : Variety k)
  exact generalLinearMatrixCoordinate
    (Module.finrank k (HyperbolicSpace k n)) i j

private noncomputable def evenOrthogonalRootAmbientRecovery (n : Nat)
    (r : TypeDRootIndex n) :
    Variety.PolynomialFunction (glVarietyOf k (HyperbolicSpace k n)) :=
  let b := Module.finBasis k (HyperbolicSpace k n)
  ∑ i, ∑ j,
    algebraMap k
      (Variety.PolynomialFunction (glVarietyOf k (HyperbolicSpace k n)))
      (evenOrthogonalRootCoordinate n r (b i) *
        b.repr (evenOrthogonalRootSource n r) j) *
      evenOrthogonalRootAmbientMatrixCoordinate n i j

private lemma evenOrthogonalRootAmbientRecovery_apply (n : Nat)
    (r : TypeDRootIndex n) (x : Variety.Point (KPlus k)) :
    evenOrthogonalRootAmbientRecovery n r
        ((evenOrthogonalRootAmbientMorphism n r).onPoints x) =
      evenOrthogonalRootCoordinate n r
        (evenOrthogonalRootIsometry n r (x.val PUnit.unit)
          (evenOrthogonalRootSource n r)) := by
  classical
  rw [evenOrthogonalRootAmbientRecovery]
  change polynomialFunctionEvalAddHom
      (glVarietyOf k (HyperbolicSpace k n))
      ((evenOrthogonalRootAmbientMorphism n r).onPoints x)
      (∑ i, ∑ j,
        algebraMap k
          (Variety.PolynomialFunction (glVarietyOf k (HyperbolicSpace k n)))
          (evenOrthogonalRootCoordinate n r
              ((Module.finBasis k (HyperbolicSpace k n)) i) *
            (Module.finBasis k (HyperbolicSpace k n)).repr
              (evenOrthogonalRootSource n r) j) *
          evenOrthogonalRootAmbientMatrixCoordinate n i j) = _
  rw [map_sum]
  simp only [map_sum, polynomialFunctionEvalAddHom_apply,
    polynomialFunction_mul_apply, polynomialFunction_algebraMap_apply]
  have hcoord (i j : Fin (Module.finrank k (HyperbolicSpace k n))) :
      evenOrthogonalRootAmbientMatrixCoordinate n i j
          ((evenOrthogonalRootAmbientMorphism n r).onPoints x) =
        (Module.finBasis k (HyperbolicSpace k n)).repr
          (evenOrthogonalRootIsometry n r (x.val PUnit.unit)
            ((Module.finBasis k (HyperbolicSpace k n)) j)) i := by
    rw [evenOrthogonalRootAmbientMatrixCoordinate]
    change generalLinearMatrixCoordinate
        (Module.finrank k (HyperbolicSpace k n)) i j
          ((evenOrthogonalRootAmbientMorphism n r).onPoints x) = _
    rw [generalLinearMatrixCoordinate_apply,
      evenOrthogonalRootAmbientMorphism_apply,
      generalLinearRepresentationPoint_matrix]
    rfl
  simp_rw [hcoord]
  simpa [LinearMap.toMatrix_apply, mul_assoc] using
    LinearMap.dual_apply_eq_sum_toMatrix
      (Module.finBasis k (HyperbolicSpace k n))
      (evenOrthogonalRootCoordinate n r)
      ((evenOrthogonalRootIsometry n r (x.val PUnit.unit)).toLinearMap)
      (evenOrthogonalRootSource n r)

private noncomputable def evenOrthogonalRootRecovery (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    Variety.PolynomialFunction
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety :=
  Variety.PolynomialFunction.pullback
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
      (standardHyperbolicSplit n)).inclusion.toVariety
    (evenOrthogonalRootAmbientRecovery n r)

public lemma evenOrthogonalRootMorphism_coordinate_preimage (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    ∀ c : (KPlus k).Coordinates,
      ∃ q : Variety.PolynomialFunction
          (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
            (standardHyperbolicSplit n)).carrierVariety,
        Variety.PolynomialFunction.pullback
            (evenOrthogonalRootMorphism n hn r).toVariety q =
          Variety.PolynomialFunction.ofPolynomial (KPlus k)
            (MvPolynomial.X c) := by
  intro c
  rcases c with ⟨⟩
  refine ⟨evenOrthogonalRootRecovery n hn r, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  simp only [Variety.PolynomialFunction.pullback,
    Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun]
  change evenOrthogonalRootRecovery n hn r
      ((evenOrthogonalRootMorphism n hn r).onPoints x) =
    evalPolynomial x.val (MvPolynomial.X PUnit.unit)
  rw [evenOrthogonalRootRecovery]
  change evenOrthogonalRootAmbientRecovery n r
      ((evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).includePoint
          ((evenOrthogonalRootMorphism n hn r).onPoints x)) = _
  rw [evenOrthogonalRootMorphism_include_apply,
    evenOrthogonalRootAmbientRecovery_apply]
  have h := evenOrthogonalRoot_parameter_recovery n r (x.val PUnit.unit)
  change evenOrthogonalRootCoordinate n r
      (evenOrthogonalRootIsometry n r (x.val PUnit.unit)
        (evenOrthogonalRootSource n r)) = x.val PUnit.unit at h
  rw [h]
  simp [evalPolynomial]

@[expose] public noncomputable def evenOrthogonalRootSubgroup (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    ClosedSubgroup
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety :=
  (evenOrthogonalRootMorphism n hn r).imageClosedSubgroup

public noncomputable def evenOrthogonalRootParametrization (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    @OneParameterParametrization k _
      (evenOrthogonalRootSubgroup (k := k) n hn r).carrierVariety
      (evenOrthogonalRootSubgroup (k := k) n hn r).carrierAlgebraicGroup :=
  Classical.choose
    ((evenOrthogonalRootMorphism n hn r).iso_imageClosedSubgroup_of_coordinate_preimage
      (evenOrthogonalRootMorphism_injective n hn r)
      (evenOrthogonalRootMorphism_coordinate_preimage n hn r))

public lemma evenOrthogonalRootSubgroup_isOneParameter (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    @IsOneParameterGroup k _
      (evenOrthogonalRootSubgroup (k := k) n hn r).carrierVariety
      (evenOrthogonalRootSubgroup (k := k) n hn r).carrierAlgebraicGroup :=
  ⟨evenOrthogonalRootParametrization n hn r⟩

public lemma evenOrthogonalRootParametrization_hom (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    @AlgebraicGroup.Iso.hom k _ (KPlus k)
        (evenOrthogonalRootSubgroup (k := k) n hn r).carrierVariety
        (inferInstance : AlgebraicGroup (KPlus k))
        (evenOrthogonalRootSubgroup (k := k) n hn r).carrierAlgebraicGroup
        (evenOrthogonalRootParametrization (k := k) n hn r) =
      (evenOrthogonalRootMorphism n hn r).codRestrictClosedSubgroup
        (evenOrthogonalRootSubgroup (k := k) n hn r)
        (fun y => ⟨y, rfl⟩) :=
  Classical.choose_spec
    ((evenOrthogonalRootMorphism n hn r).iso_imageClosedSubgroup_of_coordinate_preimage
      (evenOrthogonalRootMorphism_injective n hn r)
      (evenOrthogonalRootMorphism_coordinate_preimage n hn r))

end Theory.AlgebraicGroup
