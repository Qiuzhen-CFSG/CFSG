module

public import Theory.AtlasPort.LinearGroups.ReeG2.Generators
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.NormNum

/-!
# Marked generators for the ternary Ree comparison

The two permutations below provide a common, concrete interface for the
nine-point PSL₂(8) action and the seven-dimensional Ree matrices. Their
identification with either group is a separate obligation: no identification
or order is part of these definitions. The matrix elements are literally
`gamma 0 1` and `upsilon` in the generated Ree subgroup.

The intended comparison is GLS III §2.2, the displayed exceptional
isomorphism A₁(8) ≅ ²G₂(3)′ (also used in the proof of Theorem 2.5.15).
The cycle choices were found by the action on the nine Sylow two-subgroups;
all uses must prove the corresponding maps, independently of that search.
-/

@[expose] public section

namespace Atlas.ReeG2.TernaryDerived

/-- `(0 1 4)(2 3 7)(5 8 6)`, in Lean's left-action convention. -/
def gammaPerm : Equiv.Perm (Fin 9) where
  toFun := ![1, 4, 3, 7, 0, 8, 5, 2, 6]
  invFun := ![4, 0, 7, 2, 1, 6, 8, 3, 5]
  left_inv := by decide
  right_inv := by decide

/-- `(0 8)(1 3)(2 7)(5 6)`, fixing the point `4`. -/
def weylPerm : Equiv.Perm (Fin 9) where
  toFun := ![8, 3, 7, 1, 4, 6, 5, 2, 0]
  invFun := ![8, 3, 7, 1, 4, 6, 5, 2, 0]
  left_inv := by decide
  right_inv := by decide


open scoped commutatorElement

theorem gammaPerm_order : orderOf gammaPerm = 3 :=
  orderOf_eq_prime (by decide) (by decide)

theorem weylPerm_order : orderOf weylPerm = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem product_order : orderOf (gammaPerm * weylPerm) = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide) (by decide)

private def commutatorPerm : Equiv.Perm (Fin 9) where
  toFun := ![5, 2, 4, 6, 7, 1, 8, 3, 0]
  invFun := ![8, 5, 1, 7, 2, 0, 3, 4, 6]
  left_inv := by decide
  right_inv := by decide

private theorem commutatorPerm_eq : ⁅gammaPerm, weylPerm⁆ = commutatorPerm := by decide

theorem commutator_order : orderOf ⁅gammaPerm, weylPerm⁆ = 9 := by
  rw [commutatorPerm_eq]
  exact orderOf_eq_prime_pow (p := 3) (n := 1) (by decide) (by decide)

/-- A literal subgroup of the symmetric group, with no recognition assumptions. -/
def permutationSubgroup : Subgroup (Equiv.Perm (Fin 9)) :=
  Subgroup.closure {gammaPerm, weylPerm}

abbrev PermutationModel := ↥permutationSubgroup

def gammaGenerator : PermutationModel :=
  ⟨gammaPerm, Subgroup.subset_closure (by simp)⟩

def weylGenerator : PermutationModel :=
  ⟨weylPerm, Subgroup.subset_closure (by simp)⟩

/-- The root element in the original seven-dimensional matrix carrier. -/
noncomputable def reeGamma : Model (ZMod 3) 0 :=
  ⟨gamma 0 1, Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨1, rfl⟩)))⟩

/-- The Weyl element in the original seven-dimensional matrix carrier. -/
noncomputable def reeWeyl : Model (ZMod 3) 0 :=
  ⟨upsilon, Subgroup.subset_closure (Or.inr rfl)⟩

theorem reeWeyl_ne_one : reeWeyl ≠ 1 := by
  intro h
  have he := congrArg (fun g : Model (ZMod 3) 0 => g.val.val 0 0) h
  norm_num [reeWeyl, upsilon, upsilonMatrix] at he

/-- The marked Weyl image certifies that a matrix homomorphism is nontrivial. -/
theorem hom_ne_one_of_weyl
    (f : PermutationModel →* Model (ZMod 3) 0)
    (hf : f weylGenerator = reeWeyl) : f ≠ 1 := by
  intro h
  apply reeWeyl_ne_one
  rw [← hf, h, MonoidHom.one_apply]

end Atlas.ReeG2.TernaryDerived
