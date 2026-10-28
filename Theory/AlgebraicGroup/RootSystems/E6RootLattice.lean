module

public import Theory.AlgebraicGroup.RootSystems.Exceptional
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The integral E6 root--weight lattice quotient

The standard E6 Cartan datum, in the source numbering
`0—1—2—3` with branch `2—4—5`, has character (weight) lattice `ℤ^6`, with its
simple roots represented by the columns of `typeE6CartanMatrix`.  This module
records that inclusion directly as the range of the Cartan map.  The displayed
adjugate has product `3 • 1`, and its rows reduce modulo three to
`(1, 2, 0, 0, 1, 2)` and twice that row.  Consequently the quotient is detected
by the single mod-three character
`x₀ + 2 x₁ + x₄ + 2 x₅`; an explicit divisibility argument using the adjugate
proves that this character has precisely the root-lattice kernel.  The resulting
quotient equivalence with `ZMod 3` is the integral character/cocharacter datum
underlying the simply connected to adjoint E6 central quotient in GLS3,
Chapter 1.  Since the displayed E6 Cartan matrix is symmetric, the same
coordinate calculation is exported on the cocharacter side.  No algebraic
group classification, center theorem, or version-existence result is used.
-/

namespace Theory.AlgebraicGroup.StandardRootSystem

open Matrix Set AddSubgroup QuotientAddGroup
open scoped BigOperators

/-- The rank-six integral weight module for the standard E6 Cartan datum. -/
public abbrev typeE6WeightModule := Fin 6 → ℤ

/-- The Cartan map sends coefficient vectors to the corresponding root-lattice
combination (the Cartan matrix acts by its columns). -/
@[expose] public noncomputable def typeE6CartanMap :
    typeE6WeightModule →+ typeE6WeightModule where
  toFun x := typeE6CartanMatrix *ᵥ x
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The simple root corresponding to column `j` in fundamental-weight coordinates. -/
@[expose] public noncomputable def typeE6SimpleRootWeight (j : Fin 6) :
    typeE6WeightModule := fun i => typeE6CartanMatrix i j

/-- The integral root lattice inside the weight module. -/
@[expose] public noncomputable def typeE6RootLattice :
    AddSubgroup typeE6WeightModule := typeE6CartanMap.range

public lemma typeE6SimpleRootWeight_mem_rootLattice (j : Fin 6) :
    typeE6SimpleRootWeight j ∈ typeE6RootLattice := by
  rw [typeE6RootLattice, AddMonoidHom.mem_range]
  refine ⟨Pi.single j 1, ?_⟩
  change typeE6CartanMatrix *ᵥ Pi.single j 1 = fun i => typeE6CartanMatrix i j
  have h := typeE6CartanMatrix.mulVec_single_one j
  change typeE6CartanMatrix *ᵥ Pi.single j 1 = fun i => typeE6CartanMatrix i j at h
  exact h

/-- The full integral weight lattice. -/
@[expose] public noncomputable def typeE6WeightLattice :
    AddSubgroup typeE6WeightModule := ⊤

/-- The quotient of the weight lattice by the E6 root lattice. -/
public abbrev typeE6WeightLatticeQuotient :=
  typeE6WeightModule ⧸ typeE6RootLattice

/-- The coweight coordinate module.  For simply laced E6 the symmetric Cartan
matrix identifies it with the weight coordinate module. -/
public abbrev typeE6CoweightModule := typeE6WeightModule

/-- The E6 coroot lattice in coweight coordinates.  Symmetry of the standard
Cartan matrix identifies this inclusion with the root-lattice inclusion. -/
@[expose] public noncomputable def typeE6CorootLattice :
    AddSubgroup typeE6CoweightModule := typeE6RootLattice

/-- The full integral coweight lattice. -/
@[expose] public noncomputable def typeE6CoweightLattice :
    AddSubgroup typeE6CoweightModule := ⊤

/-- The quotient of the coweight lattice by the E6 coroot lattice. -/
public abbrev typeE6CoweightLatticeQuotient :=
    typeE6CoweightModule ⧸ typeE6CorootLattice

/-- An integral adjugate of the E6 Cartan matrix. -/
@[expose] public noncomputable def typeE6CartanAdjugate : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4, 5, 6, 3, 4, 2;
     5, 10, 12, 6, 8, 4;
     6, 12, 18, 9, 12, 6;
     3, 6, 9, 6, 6, 3;
     4, 8, 12, 6, 10, 5;
     2, 4, 6, 3, 5, 4]

/-- The adjugate identity is the integral Smith-normal-form calculation behind
the index three. -/
public lemma typeE6CartanMatrix_mul_adjugate :
    typeE6CartanMatrix * typeE6CartanAdjugate =
      (3 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeE6CartanAdjugate, typeE6CartanMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The mod-three invariant which detects the nontrivial fundamental-weight
class in the E6 quotient. -/
@[expose] public noncomputable def typeE6WeightLatticeQuotientMap :
    typeE6WeightModule →+ ZMod 3 where
  toFun x := ((x 0 + 2 * x 1 + x 4 + 2 * x 5 : ℤ) : ZMod 3)
  map_zero' := by simp
  map_add' x y := by
    change ((x 0 + y 0 + 2 * (x 1 + y 1) + (x 4 + y 4) +
      2 * (x 5 + y 5) : ℤ) : ZMod 3) =
      ((x 0 + 2 * x 1 + x 4 + 2 * x 5 : ℤ) : ZMod 3) +
        ((y 0 + 2 * y 1 + y 4 + 2 * y 5 : ℤ) : ZMod 3)
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring

private lemma typeE6WeightLatticeQuotientMap_eq_cast (x : typeE6WeightModule) :
    typeE6WeightLatticeQuotientMap x =
      ((x 0 + 2 * x 1 + x 4 + 2 * x 5 : ℤ) : ZMod 3) := rfl

private lemma typeE6WeightLatticeQuotientMap_cartan (x : typeE6WeightModule) :
    typeE6WeightLatticeQuotientMap (typeE6CartanMap x) = 0 := by
  change (((typeE6CartanMatrix *ᵥ x) 0 + 2 * (typeE6CartanMatrix *ᵥ x) 1 +
      (typeE6CartanMatrix *ᵥ x) 4 + 2 * (typeE6CartanMatrix *ᵥ x) 5 : ℤ) : ZMod 3) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨x 1 - x 2 + x 5, ?_⟩
  simp [typeE6CartanMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private noncomputable def typeE6AdjugateCoefficient (x : typeE6WeightModule) :
    typeE6WeightModule := fun i =>
  (typeE6CartanAdjugate *ᵥ x) i / 3

private lemma typeE6Adjugate_mulVec_dvd (x : typeE6WeightModule)
    (hx : typeE6WeightLatticeQuotientMap x = 0) :
    ∀ i, (3 : ℤ) ∣ (typeE6CartanAdjugate *ᵥ x) i := by
  have hd : (3 : ℤ) ∣ x 0 + 2 * x 1 + x 4 + 2 * x 5 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    simpa [typeE6WeightLatticeQuotientMap_eq_cast] using hx
  intro i
  fin_cases i
  · rcases hd with ⟨n, hn⟩
    refine ⟨n + x 0 + x 1 + 2 * x 2 + x 3 + x 4, ?_⟩
    simp [typeE6CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    omega
  · rcases hd with ⟨n, hn⟩
    refine ⟨2 * n + x 0 + 2 * x 1 + 4 * x 2 + 2 * x 3 + 2 * x 4, ?_⟩
    simp [typeE6CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    omega
  · refine ⟨2 * x 0 + 4 * x 1 + 6 * x 2 + 3 * x 3 + 4 * x 4 + 2 * x 5, ?_⟩
    simp [typeE6CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · refine ⟨x 0 + 2 * x 1 + 3 * x 2 + 2 * x 3 + 2 * x 4 + x 5, ?_⟩
    simp [typeE6CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · rcases hd with ⟨n, hn⟩
    refine ⟨n + x 0 + 2 * x 1 + 4 * x 2 + 2 * x 3 + 3 * x 4 + x 5, ?_⟩
    simp [typeE6CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    omega
  · rcases hd with ⟨n, hn⟩
    refine ⟨2 * n + 2 * x 2 + x 3 + x 4, ?_⟩
    simp [typeE6CartanAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    omega

private lemma typeE6CartanMap_adjugateCoefficient (x : typeE6WeightModule)
    (hx : typeE6WeightLatticeQuotientMap x = 0) :
    typeE6CartanMap (typeE6AdjugateCoefficient x) = x := by
  have hc : ∀ i, 3 * typeE6AdjugateCoefficient x i =
      (typeE6CartanAdjugate *ᵥ x) i := by
    intro i
    dsimp [typeE6AdjugateCoefficient]
    rw [mul_comm, Int.ediv_mul_cancel]
    exact typeE6Adjugate_mulVec_dvd x hx i
  have hc' : (3 : ℤ) • typeE6AdjugateCoefficient x =
      typeE6CartanAdjugate *ᵥ x := by
    funext i
    exact hc i
  have hmain := congrArg (fun v : typeE6WeightModule =>
      typeE6CartanMatrix *ᵥ v) hc'
  have hmul : typeE6CartanMatrix *ᵥ (typeE6CartanAdjugate *ᵥ x) =
      (3 : ℤ) • x := by
    calc
      typeE6CartanMatrix *ᵥ (typeE6CartanAdjugate *ᵥ x) =
          (typeE6CartanMatrix * typeE6CartanAdjugate) *ᵥ x :=
        Matrix.mulVec_mulVec x typeE6CartanMatrix typeE6CartanAdjugate
      _ = (3 : ℤ) • x := by
        rw [typeE6CartanMatrix_mul_adjugate]
        simp
  rw [Matrix.mulVec_smul, hmul] at hmain
  ext i
  have hi := congrArg (fun v : typeE6WeightModule => v i) hmain
  simpa [typeE6CartanMap, smul_eq_mul] using hi

public lemma typeE6WeightLatticeQuotientMap_ker :
    (typeE6WeightLatticeQuotientMap).ker = typeE6RootLattice := by
  ext x
  constructor
  · intro hx
    rw [typeE6RootLattice, AddMonoidHom.mem_range]
    exact ⟨typeE6AdjugateCoefficient x, typeE6CartanMap_adjugateCoefficient x hx⟩
  · rintro ⟨y, rfl⟩
    exact typeE6WeightLatticeQuotientMap_cartan y

public lemma typeE6WeightLatticeQuotientMap_surjective :
    Function.Surjective typeE6WeightLatticeQuotientMap := by
  intro z
  refine ⟨fun i => if i = 0 then ZMod.cast z else 0, ?_⟩
  change ((ZMod.cast z : ℤ) : ZMod 3) = z
  exact ZMod.intCast_zmod_cast z

/-- The canonical additive equivalence from the E6 weight/root quotient to
`ZMod 3`. -/
@[expose] public noncomputable def typeE6WeightLatticeQuotientEquiv :
    typeE6WeightLatticeQuotient ≃+ ZMod 3 :=
  (QuotientAddGroup.quotientAddEquivOfEq typeE6WeightLatticeQuotientMap_ker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective typeE6WeightLatticeQuotientMap
      typeE6WeightLatticeQuotientMap_surjective)

@[simp] public theorem typeE6WeightLatticeQuotientEquiv_mk (x : typeE6WeightModule) :
    typeE6WeightLatticeQuotientEquiv (QuotientAddGroup.mk' typeE6RootLattice x) =
      typeE6WeightLatticeQuotientMap x := by
  change (QuotientAddGroup.quotientKerEquivOfSurjective typeE6WeightLatticeQuotientMap
      typeE6WeightLatticeQuotientMap_surjective)
      (QuotientAddGroup.mk' typeE6WeightLatticeQuotientMap.ker x) =
    typeE6WeightLatticeQuotientMap x
  simp [QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse_apply,
    QuotientAddGroup.kerLift_mk]

/-- The E6 weight lattice modulo its root lattice is cyclic of order three.
The returned equivalence is the exact integral character/cocharacter quotient
needed for the simply connected--adjoint central quotient. -/
public theorem typeE6_weightLattice_quotient_isCyclicThree :
    Nonempty (typeE6WeightLatticeQuotient ≃+ ZMod 3) :=
  ⟨typeE6WeightLatticeQuotientEquiv⟩

public theorem typeE6_weightLattice_quotient_isAddCyclic :
    IsAddCyclic typeE6WeightLatticeQuotient := by
  exact typeE6WeightLatticeQuotientEquiv.isAddCyclic.mpr inferInstance

public theorem typeE6_weightLattice_quotient_card :
    Nat.card typeE6WeightLatticeQuotient = 3 := by
  rw [Nat.card_congr typeE6WeightLatticeQuotientEquiv.toEquiv, Nat.card_zmod]

/-- The cocharacter-side quotient equivalence, obtained from the symmetry of
the standard E6 Cartan datum. -/
@[expose] public noncomputable def typeE6CoweightLatticeQuotientEquiv :
    typeE6CoweightLatticeQuotient ≃+ ZMod 3 :=
  typeE6WeightLatticeQuotientEquiv

/-- The exact integral E6 root-datum endpoint: both the character/root and
cocharacter/coroot inclusions have cyclic cokernel of order three. -/
public theorem typeE6_integral_character_cocharacter_lattice_quotients :
    Nonempty (typeE6WeightLatticeQuotient ≃+ ZMod 3) ∧
      Nonempty (typeE6CoweightLatticeQuotient ≃+ ZMod 3) :=
  ⟨typeE6_weightLattice_quotient_isCyclicThree,
    ⟨typeE6CoweightLatticeQuotientEquiv⟩⟩

end Theory.AlgebraicGroup.StandardRootSystem
