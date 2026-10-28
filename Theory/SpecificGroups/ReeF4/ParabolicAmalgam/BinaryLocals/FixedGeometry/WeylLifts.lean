module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Theory.AlgebraicGroup.RootSystems.IntegralTitsRankTwoBraid

/-!
# Fixed Weyl representatives in the Ree parabolic seeds

The two exceptional orbits of simple F₄ nodes have longest words `[0,3]`
and `[1,2,1,2]`. The integral Tits braid identities identify each word with
its diagram reversal. Specializing these identities to the actual matrix
carrier proves that both words are fixed by the Ree twist, including at q=2.
Every letter uses a positive and an allowed negative simple root, so the
fixed representatives lie in the corresponding root-defined seeds.

These are the concrete representatives for a fixed-point Bruhat argument.
This module proves their fixedness and containment; Bruhat coverage and
separation from the positive subgroup remain distinct geometric obligations.

Source: the integral Chevalley and Tits construction of Steinberg,
*Lectures on Chevalley Groups*; Aschbacher–Smith F.1.12(I)(5) and the q=2
case, printed pp.263–264 of `refs/quasithin.pdf`.
-/

@[expose] public section
namespace ReeF4.Parabolics.Binary.FixedGeometry

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem weylWord_simple_coe (m : ℕ) (i : Fin 4) :
    (weylWord m (typeF4SimpleRootIndex i) 1 : MatrixUnits m) =
      rootCurveTitsWord (S := CoefficientField m) [typeF4RootPairing_baseEquiv i] := by
  simp only [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val i,
    rootCurveUnit_simple, rootCurveUnit_neg_simple, inv_one]

private def rootCoxeterMatrix : CoxeterMatrix typeF4RootPairing_base.support where
  M i j := orderOf (typeF4RootPairing_base.simpleReflection i *
    typeF4RootPairing_base.simpleReflection j)
  isSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simpa [mul_inv_rev] using orderOf_inv
      (typeF4RootPairing_base.simpleReflection i * typeF4RootPairing_base.simpleReflection j)
  diagonal i := by simp
  off_diagonal i j hij := by
    intro h
    have hprod := orderOf_eq_one_iff.mp h
    apply hij
    apply typeF4RootPairing_base.simpleReflection_injective
    calc
      typeF4RootPairing_base.simpleReflection i =
          typeF4RootPairing_base.simpleReflection i * 1 := by simp
      _ = typeF4RootPairing_base.simpleReflection i *
          (typeF4RootPairing_base.simpleReflection i *
            typeF4RootPairing_base.simpleReflection j) := by rw [hprod]
      _ = typeF4RootPairing_base.simpleReflection j := by simp [← mul_assoc]

private theorem linear_braid : titsWord (P := typeF4RootPairing)
      [typeF4RootPairing_baseEquiv 0, typeF4RootPairing_baseEquiv 3] =
    titsWord [typeF4RootPairing_baseEquiv 3, typeF4RootPairing_baseEquiv 0] := by
  have h03 : rootCoxeterMatrix (typeF4RootPairing_baseEquiv 0) (typeF4RootPairing_baseEquiv 3) = 2 := by
    change orderOf _ = 2
    apply simpleReflection_mul_order_eq_two_of_cartan_zero
    norm_num [typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]; decide
  have h30 : rootCoxeterMatrix (typeF4RootPairing_baseEquiv 3) (typeF4RootPairing_baseEquiv 0) = 2 := by
    rw [rootCoxeterMatrix.symmetric, h03]
  simpa only [CoxeterSystem.braidWord, h03, h30, CoxeterSystem.alternatingWord,
    List.concat_eq_append, List.nil_append, List.cons_append] using
    titsWord_braidWord_eq_of_orders rootCoxeterMatrix (fun _ _ => rfl)
      (typeF4RootPairing_baseEquiv 0) (typeF4RootPairing_baseEquiv 3)

private theorem suzuki_braid : titsWord (P := typeF4RootPairing)
      [typeF4RootPairing_baseEquiv 1, typeF4RootPairing_baseEquiv 2,
        typeF4RootPairing_baseEquiv 1, typeF4RootPairing_baseEquiv 2] =
    titsWord [typeF4RootPairing_baseEquiv 2, typeF4RootPairing_baseEquiv 1,
      typeF4RootPairing_baseEquiv 2, typeF4RootPairing_baseEquiv 1] := by
  have h12 : rootCoxeterMatrix (typeF4RootPairing_baseEquiv 1) (typeF4RootPairing_baseEquiv 2) = 4 := by
    change orderOf _ = 4
    apply simpleReflection_mul_order_eq_four_of_cartan_neg_two_neg_one
    · norm_num [typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]; decide
    · norm_num [typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]; decide
  have h21 : rootCoxeterMatrix (typeF4RootPairing_baseEquiv 2) (typeF4RootPairing_baseEquiv 1) = 4 := by
    rw [rootCoxeterMatrix.symmetric, h12]
  simpa only [CoxeterSystem.braidWord, h12, h21, CoxeterSystem.alternatingWord,
    List.concat_eq_append, List.nil_append, List.cons_append] using
    titsWord_braidWord_eq_of_orders rootCoxeterMatrix (fun _ _ => rfl)
      (typeF4RootPairing_baseEquiv 1) (typeF4RootPairing_baseEquiv 2)

/-- A word in the numbered simple Weyl representatives in the split matrix group. -/
def simpleWord (m : ℕ) (l : List (Fin 4)) : SplitGroup m :=
  (l.map fun i => weylWord m (typeF4SimpleRootIndex i) 1).prod

/-- The split word is exactly the specialization of the integral Tits word. -/
theorem simpleWord_coe (m : ℕ) (l : List (Fin 4)) :
    (simpleWord m l : MatrixUnits m) =
      rootCurveTitsWord (l.map typeF4RootPairing_baseEquiv) := by
  induction l with
  | nil => simp [simpleWord]
  | cons i l ih =>
    simp only [simpleWord, List.map_cons, List.prod_cons, Subgroup.coe_mul] at ih ⊢
    rw [ih, weylWord_simple_coe]
    simp [rootCurveTitsWord_cons, mul_assoc]

private theorem simpleWord_eq_of_titsWord_eq (m : ℕ) (l k : List (Fin 4))
    (h : titsWord (l.map typeF4RootPairing_baseEquiv) =
      titsWord (k.map typeF4RootPairing_baseEquiv)) :
    simpleWord m l = simpleWord m k := by
  apply Subtype.ext
  rw [simpleWord_coe, simpleWord_coe]
  apply Units.ext
  exact congrArg (specializeMatrix (S := CoefficientField m)) h

/-- The Ree twist reverses the simple-node numbering in a Weyl word. -/
theorem reeTwist_simpleWord (m : ℕ) (l : List (Fin 4)) :
    reeTwist m (simpleWord m l) = simpleWord m (l.map Fin.revPerm) := by
  induction l with
  | nil => simp [simpleWord]
  | cons i l ih =>
    simp only [simpleWord, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih, reeTwist_weylWord, exceptionalRootPermutation_simple, map_one]

/-- Longest words in the two exceptional orbits of simple nodes. -/
def sideWord : ReeF4.LargeLocalSeeds.Side → List (Fin 4)
  | .suzuki => [1, 2, 1, 2]
  | .linear => [0, 3]

/-- The integral rank-two braid relations make both orbit words fixed. -/
theorem sideWord_fixed (m : ℕ) (s : ReeF4.LargeLocalSeeds.Side) :
    reeTwist m (simpleWord m (sideWord s)) = simpleWord m (sideWord s) := by
  rw [reeTwist_simpleWord]
  apply simpleWord_eq_of_titsWord_eq
  cases s
  · exact suzuki_braid.symm
  · exact linear_braid.symm

open ReeF4.LargeLocalSeeds Subgroup

private theorem weylWord_mem_splitSeed (m : ℕ) (s : Side) (i : Fin 4)
    (hi : i ∈ leviNodes s) : weylWord m (typeF4SimpleRootIndex i) 1 ∈ splitSeed m s := by
  simp only [weylWord, inv_one]
  have hp : rootGeneratorInGroup m (typeF4SimpleRootIndex i) 1 ∈ splitSeed m s :=
    subset_closure ⟨typeF4SimpleRootIndex i, 1, Or.inl
      (typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv i).property), rfl⟩
  have hn : rootGeneratorInGroup m (-typeF4SimpleRootIndex i) (-1) ∈ splitSeed m s :=
    subset_closure ⟨-typeF4SimpleRootIndex i, -1, Or.inr ⟨i, hi, rfl⟩, rfl⟩
  exact (splitSeed m s).mul_mem ((splitSeed m s).mul_mem hp hn) hp

private theorem simpleWord_mem_splitSeed (m : ℕ) (s : Side) (l : List (Fin 4))
    (hl : ∀ i ∈ l, i ∈ leviNodes s) : simpleWord m l ∈ splitSeed m s := by
  induction l with
  | nil => exact (splitSeed m s).one_mem
  | cons i l ih =>
    apply (splitSeed m s).mul_mem
    · exact weylWord_mem_splitSeed m s i (hl i (by simp))
    · exact ih (fun j hj => hl j (by simp [hj]))

/-- The two orbit Weyl representatives, inside the actual Ree fixed group. -/
def weylLift (m : ℕ) (s : Side) : Model m :=
  ⟨simpleWord m (sideWord s), (mem_fixedSubgroup m _).mpr (sideWord_fixed m s)⟩

@[simp] theorem toSplitGroup_weylLift (m : ℕ) (s : Side) :
    toSplitGroup m (weylLift m s) = simpleWord m (sideWord s) :=
  toSplitGroup_apply m _

/-- Each fixed Weyl representative belongs to its marked root-defined seed. -/
theorem weylLift_mem_seed (m : ℕ) (s : Side) : weylLift m s ∈ seed m s := by
  change toSplitGroup m (weylLift m s) ∈ splitSeed m s
  rw [toSplitGroup_weylLift]
  apply simpleWord_mem_splitSeed
  cases s <;> simp [sideWord, leviNodes]

/-- The subgroup generated by the two fixed Weyl representatives. -/
def weylSubgroup (m : ℕ) : Subgroup (Model m) := closure (Set.range (weylLift m))

theorem weylLift_mem_weylSubgroup (m : ℕ) (s : Side) :
    weylLift m s ∈ weylSubgroup m := subset_closure (Set.mem_range_self s)

/-- The two fixed seeds contain the entire Weyl-representative subgroup. -/
theorem weylSubgroup_le_seeds (m : ℕ) :
    weylSubgroup m ≤ seed m .suzuki ⊔ seed m .linear := by
  apply (closure_le _).mpr
  rintro _ ⟨s, rfl⟩
  cases s
  · exact mem_sup_left (weylLift_mem_seed m .suzuki)
  · exact mem_sup_right (weylLift_mem_seed m .linear)

end
end ReeF4.Parabolics.Binary.FixedGeometry
