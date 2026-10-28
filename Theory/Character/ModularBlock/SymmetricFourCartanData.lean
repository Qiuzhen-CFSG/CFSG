module

public import Theory.Character.ModularBlock.Cartan
public import Theory.Representation.PRegularSimpleCount
public import Mathlib.Data.Fin.VecNotation
public import Theory.SpecificGroups.SymmetricFourConjugacy

/-!
# Assembly of characteristic-two Cartan data for the symmetric group on four letters

This module separates two concrete computations: the ordinary character table
and its congruence block, and the classification and lifted eigenvalue sums of
the simple modular representations. From proofs of those computations it
constructs genuine decomposition data, using the actual principal selector.
The resulting Gram matrix is `[[4,2],[2,3]]` and its degree quadratic form is 24.
Existence of the two input computations is not asserted in this module.

The rows are ordered as trivial, sign, degree two, standard, and sign-standard.
Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967),
printed p. 71, equations (6)–(7), before the central cyclic extension.
-/

public section
noncomputable section

namespace ModularBlock.SymmetricFourCartan

open scoped BigOperators
open PrincipalBlockConstruction BrauerCoefficientExtension Cartan
open SymmetricFourConjugacy

abbrev Group := Equiv.Perm (Fin 4)

/-- Dimensions of the two simple modules, in trivial-first order. -/
@[expose] def modularDegree : Fin 2 → ℕ := ![1, 2]

/-- The claimed ordinary degrees, to be verified by the ordinary computation. -/
@[expose] def ordinaryDegree : Fin 5 → ℕ := ![1, 1, 2, 3, 3]

/-- Ordinary character values on the nonidentity two-regular class. -/
@[expose] def ordinaryThreeValue : Fin 5 → ℂ := ![1, 1, -1, 0, 0]

/-- Candidate decomposition rows. Their character meaning is proved below
from the ordinary and modular computations, rather than included as input. -/
@[expose] def decompositionRow : Fin 5 → Fin 2 → ℕ :=
  ![![1, 0], ![1, 0], ![0, 1], ![1, 1], ![1, 1]]

/-- The ordinary computation must enumerate the actual complete family of
the prescribed data and prove membership in its actual congruence block. -/
structure OrdinaryCharacterData (d : PrincipalCongruenceBlockData Group) where
  index : Fin 5 ≃ d.I
  block_eq_univ : d.block = Finset.univ
  value : ∀ i g, Odd (orderOf g) →
    d.chi (index i) (ConjClasses.mk g) =
      if g = 1 then (ordinaryDegree i : ℂ) else ordinaryThreeValue i

/-- Two actual simple modules together with their lifted eigenvalue sums.
Completeness is proved below from the two-regular class count; no ordinary
characters or selector hypotheses enter this computation. -/
structure SimpleModuleData (d : PrincipalCongruenceBlockData Group) where
  rep : (j : Fin 2) → Representation (splittingField d) Group
    (Fin (modularDegree j) → splittingField d)
  irreducible : ∀ j, Representation.IsIrreducible (rep j)
  value_zero : ∀ g, Odd (orderOf g) → BrauerCharacter.value d (rep 0) g = 1
  value_one : ∀ g, Odd (orderOf g) →
    BrauerCharacter.value d (rep 1) g = if g = 1 then 2 else -1

variable {d : PrincipalCongruenceBlockData Group}

/-- The degree-one and degree-two simples exhaust all simple modules: a
third inequivalent simple would exceed the two-regular conjugacy-class count. -/
theorem SimpleModuleData.complete (s : SimpleModuleData d) (m : ℕ)
    (ρ : Representation (splittingField d) Group (Fin m → splittingField d))
    (hρ : Representation.IsIrreducible ρ) :
    ∃ j, Nonempty (ρ.Equiv (s.rep j)) := by
  classical
  by_contra! hnone
  let M : Option (Fin 2) → Type _ := fun i =>
    match i with
    | none => Fin m → splittingField d
    | some j => Fin (modularDegree j) → splittingField d
  let addM : ∀ i, AddCommGroup (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module (splittingField d) (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation (splittingField d) Group (M i) := fun i =>
    match i with
    | none => ρ
    | some j => s.rep j
  have finM : ∀ i, FiniteDimensional (splittingField d) (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, Representation.IsIrreducible (rep i) := by
    intro i
    cases i with
    | none => exact hρ
    | some j => exact s.irreducible j
  have hne : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro φ
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some k => exact (hnone k).false φ
    | some k =>
      cases j with
      | none => exact (hnone k).false φ.symm
      | some l =>
        have hd : modularDegree k = modularDegree l := by
          simpa only [M, Module.finrank_fin_fun] using φ.toLinearEquiv.finrank_eq
        have hkl : k = l := by
          fin_cases k <;> fin_cases l <;> simp_all [modularDegree]
        exact hij (congrArg some hkl)
  have hbound := Representation.irreducible_family_card_le_pRegularConjClasses M rep 2 hne
  rw [card_twoRegularClasses] at hbound
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hbound
  omega

/-- The two independently defined Brauer characters are linearly independent:
their values at the identity and a three-cycle form a matrix of determinant -3. -/
theorem SimpleModuleData.independent (s : SimpleModuleData d) :
    LinearIndependent ℂ (fun j => BrauerCharacter.character d (s.rep j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hidentity := congrFun hc (BrauerCharacter.twoRegularClass (1 : Group) (by simp))
  have hthree := congrFun hc (BrauerCharacter.twoRegularClass threeCycle threeCycle_odd)
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    BrauerCharacter.character_apply, smul_eq_mul, Pi.zero_apply] at hidentity hthree
  rw [s.value_zero 1 (by simp), s.value_one 1 (by simp), if_pos rfl] at hidentity
  rw [s.value_zero _ threeCycle_odd, s.value_one _ threeCycle_odd,
    if_neg threeCycle_ne_one] at hthree
  have hzero : c 0 = 0 := by linear_combination (hidentity + 2 * hthree) / 3
  have hone : c 1 = 0 := by linear_combination (hidentity - hthree) / 3
  intro j
  fin_cases j <;> assumption

/-- All modular simples are in the principal block because the proved
ordinary block computation makes the actual splitting selector equal to one. -/
def principalBrauerFamily (o : OrdinaryCharacterData d) (s : SimpleModuleData d) :
    PrincipalBrauerFamily d 2 where
  degree := modularDegree
  rep := s.rep
  irreducible := s.irreducible
  inBlock j := inPrincipalBlock_of_block_eq_univ d o.block_eq_univ (s.rep j)
  complete m ρ hρ _ := s.complete m ρ hρ
  independent := s.independent

/-- Assemble genuine decomposition data from the two character computations. -/
def decompositionData (o : OrdinaryCharacterData d) (s : SimpleModuleData d) :
    PrincipalDecompositionData d 2 where
  family := principalBrauerFamily o s
  decomposition i := decompositionRow (o.index.symm i)
  restriction i _ g hg := by
    obtain ⟨r, rfl⟩ := o.index.surjective i
    simp only [Equiv.symm_apply_apply, Fin.sum_univ_two]
    change d.chi (o.index r) (ConjClasses.mk g) =
      (decompositionRow r 0 : ℂ) * BrauerCharacter.value d (s.rep 0) g +
      (decompositionRow r 1 : ℂ) * BrauerCharacter.value d (s.rep 1) g
    rw [o.value r g hg, s.value_zero g hg, s.value_one g hg]
    fin_cases r <;> by_cases h : g = 1 <;>
      norm_num [h, decompositionRow, ordinaryDegree, ordinaryThreeValue]

/-- The assembled family retains the dimensions of the two simple modules. -/
@[simp] theorem decompositionData_degree (o : OrdinaryCharacterData d)
    (s : SimpleModuleData d) (j : Fin 2) :
    (decompositionData o s).family.degree j = modularDegree j := by
  simp only [decompositionData, principalBrauerFamily]

private theorem cartan_eq_sum (o : OrdinaryCharacterData d) (s : SimpleModuleData d)
    (j k : Fin 2) :
    (decompositionData o s).cartan j k =
      ∑ r : Fin 5, decompositionRow r j * decompositionRow r k := by
  simp only [PrincipalDecompositionData.cartan, decompositionData, o.block_eq_univ]
  exact (o.index.symm.sum_comp (fun r => decompositionRow r j * decompositionRow r k))

@[simp] theorem cartan_zero_zero (o : OrdinaryCharacterData d) (s : SimpleModuleData d) :
    (decompositionData o s).cartan 0 0 = 4 := by
  rw [cartan_eq_sum]
  norm_num [decompositionRow, Fin.sum_univ_succ]

@[simp] theorem cartan_zero_one (o : OrdinaryCharacterData d) (s : SimpleModuleData d) :
    (decompositionData o s).cartan 0 1 = 2 := by
  rw [cartan_eq_sum]
  norm_num [decompositionRow, Fin.sum_univ_succ]

@[simp] theorem cartan_one_zero (o : OrdinaryCharacterData d) (s : SimpleModuleData d) :
    (decompositionData o s).cartan 1 0 = 2 := by
  rw [PrincipalDecompositionData.cartan_symmetric, cartan_zero_one]

@[simp] theorem cartan_one_one (o : OrdinaryCharacterData d) (s : SimpleModuleData d) :
    (decompositionData o s).cartan 1 1 = 3 := by
  rw [cartan_eq_sum]
  norm_num [decompositionRow, Fin.sum_univ_succ]

/-- The principal-block degree-square sum follows already from the proved
ordinary-character computation. -/
theorem sum_degree_sq_of_ordinaryData (o : OrdinaryCharacterData d) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk 1) ^ 2 = (24 : ℂ) := by
  rw [o.block_eq_univ, ← o.index.sum_comp (fun i => d.chi i (ConjClasses.mk 1) ^ 2)]
  simp only [o.value _ 1 (by simp)]
  norm_num [ordinaryDegree, Fin.sum_univ_succ]

/-- Final assembly interface; existence of its two inputs is a separate task. -/
theorem exists_decompositionData_of_computations
    (o : OrdinaryCharacterData d) (s : SimpleModuleData d) :
    ∃ a : PrincipalDecompositionData d 2,
      a.family.degree 0 = 1 ∧ a.family.degree 1 = 2 ∧
      a.cartan 0 0 = 4 ∧ a.cartan 0 1 = 2 ∧
      a.cartan 1 0 = 2 ∧ a.cartan 1 1 = 3 :=
  ⟨decompositionData o s, rfl, rfl, cartan_zero_zero o s, cartan_zero_one o s,
    cartan_one_zero o s, cartan_one_one o s⟩

end ModularBlock.SymmetricFourCartan
