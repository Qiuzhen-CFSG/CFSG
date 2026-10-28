module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Finite reflection seeds

This module turns finite reflection data with integral Cartan pairings into Mathlib's
`RootPairing`.  A seed consists of injective roots and coroots in perfectly paired finite free
modules, a permutation for each reflection satisfying the root and coroot reflection formulas,
spanning hypotheses, and the reduced scalar-multiple condition.

The resulting pairing is a finite reduced crystallographic root system.  Base existence then
supplies a compatible choice of positive and simple roots.  Partial addition is defined exactly
when a sum of root vectors is again a root, and the integral base height proves the negation,
addition, positivity, and indecomposability clauses used by root-group realizations.  The pairing
and addition specifications also give the pure combinatorial input needed by torus root-system
identifications; no algebraic-group geometry is used here.

The reflection construction follows Mathlib's `RootPairing` convention.  The base and height
arguments use `RootPairing.nonempty_base` and the base induction API.
-/

@[expose] public section

noncomputable section

open Function Set Submodule

namespace Theory.AlgebraicGroup

universe u v w z

/-- Finite crystallographic reflection data in a pair of perfectly paired finite free modules.

The integer `cartan i j` is the value of `root i` on `coroot j`.  The final hypothesis is the
usual reducedness condition: two roots on the same scalar line differ only by sign. -/
public structure FiniteReflectionSeed
    (ι : Type u) (R : Type v) (X : Type w) (Y : Type z)
    [Finite ι] [Field R] [CharZero R]
    [AddCommGroup X] [Module R X] [Module.Free R X] [Module.Finite R X]
    [AddCommGroup Y] [Module R Y] [Module.Free R Y] [Module.Finite R Y] where
  pairing : X →ₗ[R] Y →ₗ[R] R
  pairing_isPerfPair : pairing.IsPerfPair
  root : ι ↪ X
  coroot : ι ↪ Y
  cartan : ι → ι → ℤ
  pairing_eq_cartan (i j : ι) : pairing (root i) (coroot j) = cartan i j
  cartan_self (i : ι) : cartan i i = 2
  reflectionPerm : ι → (ι ≃ ι)
  reflection_root (i j : ι) :
    root j - (cartan j i : R) • root i = root (reflectionPerm i j)
  reflection_coroot (i j : ι) :
    coroot j - (cartan i j : R) • coroot i = coroot (reflectionPerm i j)
  span_root : span R (range root) = ⊤
  span_coroot : span R (range coroot) = ⊤
  reduced_scalar_multiple (i j : ι)
      (h : ¬ LinearIndependent R ![root i, root j]) :
    root i = root j ∨ root i = -root j

namespace FiniteReflectionSeed

variable {ι : Type u} {R : Type v} {X : Type w} {Y : Type z}
  [Finite ι] [Field R] [CharZero R]
  [AddCommGroup X] [Module R X] [Module.Free R X] [Module.Finite R X]
  [AddCommGroup Y] [Module R Y] [Module.Free R Y] [Module.Finite R Y]
  (S : FiniteReflectionSeed ι R X Y)

/-- The root pairing determined by a finite reflection seed. -/
public noncomputable def toRootPairing : RootPairing ι R X Y := by
  letI : S.pairing.IsPerfPair := S.pairing_isPerfPair
  exact
    { toLinearMap := S.pairing
      root := S.root
      coroot := S.coroot
      root_coroot_two := fun i => by rw [S.pairing_eq_cartan, S.cartan_self]; norm_num
      reflectionPerm := S.reflectionPerm
      reflectionPerm_root := fun i j => by
        simpa [S.pairing_eq_cartan] using S.reflection_root i j
      reflectionPerm_coroot := fun i j => by
        simpa [S.pairing_eq_cartan] using S.reflection_coroot i j }

@[simp] public lemma toRootPairing_root (i : ι) : S.toRootPairing.root i = S.root i := rfl

@[simp] public lemma toRootPairing_coroot (i : ι) : S.toRootPairing.coroot i = S.coroot i := rfl

@[simp] public lemma toRootPairing_pairing (i j : ι) :
    S.toRootPairing.pairing i j = (S.cartan i j : R) := by
  exact S.pairing_eq_cartan i j

@[simp] public lemma toRootPairing_reflectionPerm (i j : ι) :
    S.toRootPairing.reflectionPerm i j = S.reflectionPerm i j := rfl

public instance : S.toRootPairing.IsRootSystem where
  span_root_eq_top := S.span_root
  span_coroot_eq_top := S.span_coroot

public instance : S.toRootPairing.IsCrystallographic where
  exists_value i j := ⟨S.cartan i j, by simp⟩

public instance : S.toRootPairing.IsReduced where
  eq_or_eq_neg := S.reduced_scalar_multiple

/-- A compatible base, chosen using finite reduced crystallographic base existence. -/
public noncomputable def base : S.toRootPairing.Base :=
  Classical.choice S.toRootPairing.nonempty_base

/-- The opposite-root index. -/
public def neg (i : ι) : ι := S.reflectionPerm i i

/-- Partial root addition. It is defined exactly when the vector sum is a root. -/
public noncomputable def add (i j : ι) : Option ι := by
  classical
  exact if h : ∃ k, S.root k = S.root i + S.root j then some h.choose else none

/-- Positive roots relative to the chosen base. -/
public def positive : Set ι := {i | S.base.IsPos i}

/-- Simple roots relative to the chosen base. -/
public def simple : Set ι := S.base.support

/-- Integral height relative to the chosen base. -/
public def height (i : ι) : ℤ := S.base.height i

@[simp] public lemma root_neg (i : ι) : S.root (S.neg i) = -S.root i := by
  simpa [neg, S.cartan_self, two_smul] using (S.reflection_root i i).symm

@[simp] public lemma coroot_neg (i : ι) : S.coroot (S.neg i) = -S.coroot i := by
  simpa [neg, S.cartan_self, two_smul] using (S.reflection_coroot i i).symm

@[simp] public lemma neg_neg (i : ι) : S.neg (S.neg i) = i := by
  apply S.root.injective
  simp

public lemma add_eq_some_iff {i j k : ι} :
    S.add i j = some k ↔ S.root k = S.root i + S.root j := by
  classical
  simp only [add]
  split_ifs with h
  · constructor
    · intro hEq
      cases Option.some.inj hEq
      exact h.choose_spec
    · intro hk
      apply congrArg some
      exact S.root.injective (h.choose_spec.trans hk.symm)
  · constructor
    · intro hEq
      cases hEq
    · intro hk
      exact (h ⟨k, hk⟩).elim

@[simp] public lemma height_neg (i : ι) : S.height (S.neg i) = -S.height i := by
  let _ := S.toRootPairing.indexNeg
  exact S.base.height_reflectionPerm_self i

public lemma height_add {i j k : ι} (h : S.add i j = some k) :
    S.height k = S.height i + S.height j :=
  S.base.height_add (S.add_eq_some_iff.mp h)

@[simp] public lemma mem_positive_iff (i : ι) : i ∈ S.positive ↔ 0 < S.height i := Iff.rfl

public lemma mem_simple_iff (i : ι) :
    i ∈ S.simple ↔ i ∈ S.positive ∧
      ∀ j k, S.add j k = some i → ¬(j ∈ S.positive ∧ k ∈ S.positive) := by
  constructor
  · intro hi
    have hiBase : i ∈ S.base.support := hi
    refine ⟨S.base.isPos_of_mem_support hiBase, ?_⟩
    intro j k hjk ⟨hj, hk⟩
    have hHeight := S.height_add hjk
    have hiHeight := S.base.height_one_of_mem_support hiBase
    change 0 < S.height j at hj
    change 0 < S.height k at hk
    change S.height i = 1 at hiHeight
    lia
  · rintro ⟨hi, hindecomp⟩
    change S.base.IsPos i at hi
    suffices i ∈ S.base.support ∨ ∃ j k, S.base.IsPos j ∧ S.base.IsPos k ∧
        S.toRootPairing.root i = S.toRootPairing.root j + S.toRootPairing.root k by
      rcases this with hiBase | ⟨j, k, hj, hk, hjk⟩
      · exact hiBase
      · exact False.elim <| hindecomp j k
          ((S.add_eq_some_iff).mpr hjk) ⟨hj, hk⟩
    let p : ι → Prop := fun l => S.base.IsPos l →
      l ∈ S.base.support ∨ ∃ j k, S.base.IsPos j ∧ S.base.IsPos k ∧
        S.toRootPairing.root l = S.toRootPairing.root j + S.toRootPairing.root k
    have hp : p i := hi.induction_on_add
      (fun j hj _ => Or.inl hj)
      (fun j k l hl _ hk hlPos => by
        have hjPos : S.base.IsPos j := by
          rw [RootPairing.Base.isPos_iff']
          have hHeight := S.base.height_add hl
          have hkHeight := S.base.height_one_of_mem_support hk
          rw [hkHeight] at hHeight
          rw [RootPairing.Base.isPos_iff] at hlPos
          have hjNe := S.base.height_ne_zero j
          lia
        exact Or.inr ⟨j, k, hjPos, S.base.isPos_of_mem_support hk, hl⟩)
    exact hp hi

/-- All root-system and base data constructed from a finite reflection seed.

Its fields are deliberately aligned with the combinatorial clauses of root-group realizations.
The fixed pairing `S.toRootPairing`, together with `root_add_iff`, supplies the corresponding
root-system-identification clauses. -/
public structure Realization where
  base : S.toRootPairing.Base
  neg : ι → ι
  add : ι → ι → Option ι
  pairing : ι → ι → ℤ
  reflect : ι → ι → ι
  positive : Set ι
  simple : Set ι
  height : ι → ℤ
  pairing_self (i : ι) : pairing i i = 2
  pairing_eq (i j : ι) : S.toRootPairing.pairing i j = (pairing i j : R)
  root_reflect (i j : ι) :
    S.root (reflect i j) = S.root j - (pairing j i : R) • S.root i
  coroot_reflect (i j : ι) :
    S.coroot (reflect i j) = S.coroot j - (pairing i j : R) • S.coroot i
  root_neg (i : ι) : S.root (neg i) = -S.root i
  coroot_neg (i : ι) : S.coroot (neg i) = -S.coroot i
  root_add_iff (i j k : ι) : add i j = some k ↔ S.root k = S.root i + S.root j
  height_neg (i : ι) : height (neg i) = -height i
  height_add (i j k : ι) : add i j = some k → height k = height i + height j
  positive_iff (i : ι) : i ∈ positive ↔ 0 < height i
  simple_iff (i : ι) : i ∈ simple ↔ i ∈ positive ∧
    ∀ j k, add j k = some i → ¬(j ∈ positive ∧ k ∈ positive)

/-- Construct the combinatorial realization attached to a finite reflection seed. -/
public noncomputable def realization : S.Realization where
  base := S.base
  neg := S.neg
  add := S.add
  pairing := S.cartan
  reflect := fun i j => S.reflectionPerm i j
  positive := S.positive
  simple := S.simple
  height := S.height
  pairing_self := S.cartan_self
  pairing_eq := S.toRootPairing_pairing
  root_reflect := fun i j => (S.reflection_root i j).symm
  coroot_reflect := fun i j => (S.reflection_coroot i j).symm
  root_neg := S.root_neg
  coroot_neg := S.coroot_neg
  root_add_iff := fun _ _ _ => S.add_eq_some_iff
  height_neg := S.height_neg
  height_add := fun _ _ _ => S.height_add
  positive_iff := S.mem_positive_iff
  simple_iff := S.mem_simple_iff

end FiniteReflectionSeed

end Theory.AlgebraicGroup
