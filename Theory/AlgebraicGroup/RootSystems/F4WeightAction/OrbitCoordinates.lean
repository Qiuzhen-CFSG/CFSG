module

public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Height
public import Theory.RingTheory.FundamentalOrbitSums
/-!
# Fundamental orbit coordinates of the actual F4 torus

The four distinct fundamental-weight orbit sums separate Weyl orbits on the
weight torus, in every field characteristic. The preceding integral height
and dominance calculation supplies all hypotheses of the monic invariant
algebra generation theorem. The character convention is the positive coroot
product: the ith fundamental character evaluates to the ith torus parameter.

Source: Steinberg (1963), §3.9, specialized to the determinant-one F4 lattice.
-/

public noncomputable section
open scoped BigOperators
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
noncomputable local instance orbitCoordinatesRootsFintype : Fintype typeF4Roots := Fintype.ofFinite _
noncomputable scoped instance weightAction : DistribMulAction Weyl Weight :=
  DistribMulAction.compHom Weight representation
open scoped F4WeightAction
local instance orbitCoordinatesWeylFinite : Finite Weyl := weylGroup_finite typeF4RootPairing
abbrev Lattice := Multiplicative Weight
noncomputable scoped instance latticeAction : MulDistribMulAction Weyl Lattice where
  smul w a := Multiplicative.ofAdd (representation w a.toAdd)
  one_smul a := by change Multiplicative.ofAdd (representation 1 a.toAdd) = a; rw [map_one]; rfl
  mul_smul v w a := by
    change Multiplicative.ofAdd (representation (v * w) a.toAdd) =
      Multiplicative.ofAdd (representation v (representation w a.toAdd))
    rw [map_mul]; rfl
  smul_one w := congrArg Multiplicative.ofAdd (map_zero (representation w))
  smul_mul w a b := congrArg Multiplicative.ofAdd (map_add (representation w) a.toAdd b.toAdd)


@[expose] noncomputable def character {F : Type*} [Field F] (t : Fin 4 → Fˣ) : Lattice →* Fˣ where
  toFun a := ∏ i : Fin 4, t i ^ a.toAdd i
  map_one' := by simp
  map_mul' a b := by simp [zpow_add, Finset.prod_mul_distrib]

@[expose] def fundamental (i : Fin 4) : Lattice := Multiplicative.ofAdd (Pi.single i 1)

lemma character_fundamental {F : Type*} [Field F] (t : Fin 4 → Fˣ) (i : Fin 4) :
    character t (fundamental i) = t i := by
  classical
  simp [character, fundamental, Pi.single_apply]

private noncomputable def latticeHeight (a : Lattice) : ℤ := height a.toAdd

private lemma latticeHeight_mul (a b : Lattice) :
    latticeHeight (a * b) = latticeHeight a + latticeHeight b :=
  height.map_add a.toAdd b.toAdd

private lemma maximal_factorization (a : Lattice)
    (ha : ∀ w : Weyl, latticeHeight (w • a) ≤ latticeHeight a) :
    ∃ n : Fin 4 → ℕ, a = ∏ i, fundamental i ^ n i := by
  have hn := nonneg_of_maximal_height a.toAdd ha
  refine ⟨fun i => (a.toAdd i).toNat, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_prod]
  funext j
  simp only [toAdd_pow, fundamental, toAdd_ofAdd,
    Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  simpa only [smul_ite, nsmul_eq_mul, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte] using (Int.toNat_of_nonneg (hn j)).symm

@[expose] noncomputable def fundamentalValue {F : Type*} [Field F] (t : Fin 4 → Fˣ) (i : Fin 4) : F :=
  Theory.MonoidAlgebraOrbitSums.orbitSumValue (G := Weyl) (character t) (fundamental i)

/-- The four actual fundamental F4 orbit sums separate the full weight-torus
orbits; no invariant-algebra or classification premise remains. -/
theorem exists_weyl_of_fundamentalValue_eq {F : Type*} [Field F]
    (t s : Fin 4 → Fˣ) (heq : ∀ i, fundamentalValue t i = fundamentalValue s i) :
    ∃ w : Weyl, ∀ a : Lattice, character s a = character t (w • a) := by
  apply Theory.FundamentalOrbitSums.exists_smul_of_fundamental_values_eq
    latticeHeight latticeHeight_mul fundamental ?_ maximal_factorization ?_ ?_
    (character t) (character s) heq
  · exact fun a ha => height_nonneg_of_maximal a.toAdd ha
  · intro i w
    apply height_representation_le (Pi.single i 1)
    intro j
    simp only [Pi.single_apply]; split_ifs <;> norm_num
  · intro i w h
    apply Multiplicative.toAdd.injective
    apply (height_representation_eq_iff (Pi.single i 1) (by intro j; simp only [Pi.single_apply]; split_ifs <;> norm_num) w).mp
    exact h
end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
