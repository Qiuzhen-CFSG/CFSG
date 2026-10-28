module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.PointConstruction.SpinRelations
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.Weyl

/-!
# Nonopposite root commutators in the Clifford Spin group

For the fixed root `-e₀-e₁`, an integer certificate identifies precisely the
root sums in the standard D4 root space. The existing elementary orthogonal
coordinate formulas then verify the commutator on each of the six coordinate
supports. Faithfulness of the natural action lifts these identities to the
actual Clifford Spin carrier.

The two relations are preserved by the pinned simple-normalizer conjugations:
reflection is linear on root sums and permutes the roots and their negatives.
A spanning tree in the checked reflection table reaches all twenty-four signed
roots from the fixed root. Thus the calculation includes every distinct
nonopposite pair, with the source convention `x⁻¹ y⁻¹ x y`. In characteristic
two all the simply laced Chevalley coefficients equal one.

Source: GLS3, Theorem 1.12.1(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.PointGeneration
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
namespace SpinComparisonExistence.PointConstruction
noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
set_option linter.unusedSimpArgs false

-- The candidate sum with `-e₀-e₁`; `none` means there is no root sum.
private def baseSum : Fin 24 → Option (Fin 24) :=
  ![none, none, none, none, none, none, some 12, some 13,
    none, none, some 16, some 17, none, none, some 4, some 5,
    none, none, some 8, some 9, none, none, none, none]

private theorem baseSum_certificate : ∀ s q : Fin 24,
    (∀ p, rootVectorInt q p = rootVectorInt 0 p + rootVectorInt s p) ↔
      baseSum s = some q := by decide

private theorem baseSum_iff (s q : Fin 24) :
    (typeDRootPairing 2).root (rootAt q) =
      (typeDRootPairing 2).root (rootAt 0) + (typeDRootPairing 2).root (rootAt s) ↔
        baseSum s = some q := by
  rw [← baseSum_certificate]
  constructor
  · intro h p
    have hp := congrFun (congrArg Subtype.val h) p
    change typeDRootVector 4 (rootAt q) p =
      typeDRootVector 4 (rootAt 0) p + typeDRootVector 4 (rootAt s) p at hp
    simp only [rootAt_vector] at hp
    exact_mod_cast hp
  · intro h
    apply Subtype.ext
    funext p
    change typeDRootVector 4 (rootAt q) p =
      typeDRootVector 4 (rootAt 0) p + typeDRootVector 4 (rootAt s) p
    simp only [rootAt_vector]
    exact_mod_cast h p

private def sumValue (q : Option (Fin 24)) (a : k) : Points k :=
  q.elim 1 (fun q => rootPoint k (rootAt q) a)

-- Keep the coordinate checks in six small declarations, one per support.
-- Each check stays within the default heartbeat limit.
omit [IsAlgClosed k] in
private theorem base_action_0 (s : Fin 4) (hs : s ≠ 3) (a b : k)
    (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 0, by omega⟩) b
      (rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 0, by omega⟩) b z))) =
        (baseSum ⟨s.val + 0, by omega⟩).elim z (fun q => rootAction k (rootAt q) (a * b) z) := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  have h4 : (4 : k) = 0 := by linear_combination 2 * h2
  fin_cases s <;> try contradiction
  all_goals
    dsimp [baseSum, Option.elim, rootAt, rootAction]
    simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [Matrix.vecHead, Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq,
        sub_eq_add_neg, Fin.ext_iff] <;> ring_nf <;> simp [h2, h3, h4]

omit [IsAlgClosed k] in
private theorem base_action_4 (s : Fin 4) (a b : k)
    (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 4, by omega⟩) b
      (rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 4, by omega⟩) b z))) =
        (baseSum ⟨s.val + 4, by omega⟩).elim z (fun q => rootAction k (rootAt q) (a * b) z) := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  fin_cases s
  all_goals
    dsimp [baseSum, Option.elim, rootAt, rootAction]
    simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [Matrix.vecHead, Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq,
        sub_eq_add_neg, Fin.ext_iff] <;> ring_nf <;> simp [h2, h3]

omit [IsAlgClosed k] in
private theorem base_action_8 (s : Fin 4) (a b : k)
    (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 8, by omega⟩) b
      (rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 8, by omega⟩) b z))) =
        (baseSum ⟨s.val + 8, by omega⟩).elim z (fun q => rootAction k (rootAt q) (a * b) z) := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  fin_cases s
  all_goals
    dsimp [baseSum, Option.elim, rootAt, rootAction]
    simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [Matrix.vecHead, Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq,
        sub_eq_add_neg, Fin.ext_iff] <;> ring_nf <;> simp [h2, h3]

omit [IsAlgClosed k] in
private theorem base_action_12 (s : Fin 4) (a b : k)
    (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 12, by omega⟩) b
      (rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 12, by omega⟩) b z))) =
        (baseSum ⟨s.val + 12, by omega⟩).elim z (fun q => rootAction k (rootAt q) (a * b) z) := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  fin_cases s
  all_goals
    dsimp [baseSum, Option.elim, rootAt, rootAction]
    simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [Matrix.vecHead, Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq,
        sub_eq_add_neg, Fin.ext_iff] <;> ring_nf <;> simp [h2, h3]

omit [IsAlgClosed k] in
private theorem base_action_16 (s : Fin 4) (a b : k)
    (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 16, by omega⟩) b
      (rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 16, by omega⟩) b z))) =
        (baseSum ⟨s.val + 16, by omega⟩).elim z (fun q => rootAction k (rootAt q) (a * b) z) := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  fin_cases s
  all_goals
    dsimp [baseSum, Option.elim, rootAt, rootAction]
    simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [Matrix.vecHead, Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq,
        sub_eq_add_neg, Fin.ext_iff] <;> ring_nf <;> simp [h2, h3]

omit [IsAlgClosed k] in
private theorem base_action_20 (s : Fin 4) (a b : k)
    (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 20, by omega⟩) b
      (rootAction k (rootAt 0) a (rootAction k (rootAt ⟨s.val + 20, by omega⟩) b z))) =
        (baseSum ⟨s.val + 20, by omega⟩).elim z (fun q => rootAction k (rootAt q) (a * b) z) := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  fin_cases s
  all_goals
    dsimp [baseSum, Option.elim, rootAt, rootAction]
    simp only [show (-1 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
    apply Prod.ext <;> funext p <;> fin_cases p <;>
      simp [Matrix.vecHead, Matrix.vecTail, Pi.single_apply, CharTwo.neg_eq,
        sub_eq_add_neg, Fin.ext_iff] <;> ring_nf <;> simp [h2, h3]

omit [IsAlgClosed k] in
private theorem base_action (s : Fin 24) (hs : s ≠ 3) (a b : k)
    (z : HyperbolicSpace k 4) :
    rootAction k (rootAt 0) a (rootAction k (rootAt s) b
      (rootAction k (rootAt 0) a (rootAction k (rootAt s) b z))) =
        (baseSum s).elim z (fun q => rootAction k (rootAt q) (a * b) z) := by
  fin_cases s
  · exact base_action_0 k 0 (by decide) a b z
  · exact base_action_0 k 1 (by decide) a b z
  · exact base_action_0 k 2 (by decide) a b z
  · exact False.elim (hs rfl)
  · exact base_action_4 k 0 a b z
  · exact base_action_4 k 1 a b z
  · exact base_action_4 k 2 a b z
  · exact base_action_4 k 3 a b z
  · exact base_action_8 k 0 a b z
  · exact base_action_8 k 1 a b z
  · exact base_action_8 k 2 a b z
  · exact base_action_8 k 3 a b z
  · exact base_action_12 k 0 a b z
  · exact base_action_12 k 1 a b z
  · exact base_action_12 k 2 a b z
  · exact base_action_12 k 3 a b z
  · exact base_action_16 k 0 a b z
  · exact base_action_16 k 1 a b z
  · exact base_action_16 k 2 a b z
  · exact base_action_16 k 3 a b z
  · exact base_action_20 k 0 a b z
  · exact base_action_20 k 1 a b z
  · exact base_action_20 k 2 a b z
  · exact base_action_20 k 3 a b z

private theorem base_commutator (s : Fin 24) (hs : s ≠ 3) (a b : k) :
    (rootPoint k (rootAt 0) a)⁻¹ * (rootPoint k (rootAt s) b)⁻¹ *
      rootPoint k (rootAt 0) a * rootPoint k (rootAt s) b =
        sumValue k (baseSum s) (a * b) := by
  simp only [rootPoint_inv]
  apply naturalAction_injective k
  simp only [map_mul, naturalAction_rootPoint]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  have h := base_action k s hs a b z
  cases he : baseSum s <;>
    simpa only [he, sumValue, Option.elim, map_one, naturalAction_rootPoint,
      Subgroup.coe_mul, Subgroup.coe_one, LinearEquiv.mul_apply,
      LinearEquiv.coe_one, id_eq, rootAction_spec] using h

-- Use the actual root span so that reflection transports sums by linearity.
private def Good (r : RootIndex) : Prop :=
  ∀ s : RootIndex, r ≠ s → r ≠ negativeRoot s →
    (∀ q, (typeDRootPairing 2).root q =
      (typeDRootPairing 2).root r + (typeDRootPairing 2).root s → ∀ a b : k,
        (rootPoint k r a)⁻¹ * (rootPoint k s b)⁻¹ * rootPoint k r a * rootPoint k s b =
          rootPoint k q (a * b)) ∧
    ((∀ q, (typeDRootPairing 2).root q ≠
      (typeDRootPairing 2).root r + (typeDRootPairing 2).root s) → ∀ a b : k,
        (rootPoint k r a)⁻¹ * (rootPoint k s b)⁻¹ * rootPoint k r a * rootPoint k s b = 1)

private theorem base_good : Good k (rootAt 0) := by
  intro s _ hopp
  obtain ⟨s, rfl⟩ := rootAt_surjective s
  have hs : s ≠ 3 := by
    intro hs
    subst s
    apply hopp
    dsimp [rootAt, negativeRoot]
  constructor
  · intro q hq a b
    obtain ⟨q, rfl⟩ := rootAt_surjective q
    rw [base_commutator k s hs, (baseSum_iff s q).mp hq]
    rfl
  · intro hq a b
    have hn : baseSum s = none := by
      cases he : baseSum s with
      | none => rfl
      | some q => exact False.elim (hq (rootAt q) ((baseSum_iff s q).mpr he))
    rw [base_commutator k s hs, hn]
    rfl

private theorem good_reflection (i : Fin 4) (r : RootIndex) (hr : Good k r) :
    Good k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) r) := by
  let e := (typeDRootPairing 2).reflectionPerm (simpleRoot i)
  let f := MulAut.conj ((simpleNormalizer k i)⁻¹)
  have hf (s : RootIndex) (a : k) : f (rootPoint k s a) = rootPoint k (e s) a := by
    simpa only [f, MulAut.conj_apply, inv_inv] using
      simpleNormalizer_rootPoint_conjugation k i s a
  have he (r s q : RootIndex) :
      (typeDRootPairing 2).root (e q) =
        (typeDRootPairing 2).root (e r) + (typeDRootPairing 2).root (e s) ↔
      (typeDRootPairing 2).root q =
        (typeDRootPairing 2).root r + (typeDRootPairing 2).root s := by
    simp only [e, RootPairing.root_reflectionPerm, ← map_add]
    exact ((typeDRootPairing 2).reflection (simpleRoot i)).injective.eq_iff
  intro s hrs hopp
  obtain ⟨s, rfl⟩ := e.surjective s
  have hrs' : r ≠ s := fun h => hrs (congrArg e h)
  have hopp' : r ≠ negativeRoot s := by
    intro h
    apply hopp
    rw [h, reflection_negativeRoot]
  obtain ⟨hSum, hNo⟩ := hr s hrs' hopp'
  constructor
  · intro q hq a b
    obtain ⟨q, rfl⟩ := e.surjective q
    have h := congrArg f (hSum q ((he r s q).mp hq) a b)
    simpa only [map_mul, map_inv, hf] using h
  · intro hq a b
    have hn : ∀ q, (typeDRootPairing 2).root q ≠
        (typeDRootPairing 2).root r + (typeDRootPairing 2).root s := by
      intro q h
      exact hq (e q) ((he r s q).mpr h)
    have h := congrArg f (hNo hn a b)
    simpa only [map_mul, map_inv, map_one, hf] using h

private theorem all_good (r : RootIndex) : Good k r := by
  obtain ⟨r, rfl⟩ := rootAt_surjective r
  have step (i : Fin 4) (r : Fin 24) (hr : Good k (rootAt r)) :
      Good k (rootAt (reflectionIndex i r)) := by
    rw [← reflection_rootAt]
    exact good_reflection k i (rootAt r) hr
  -- A spanning tree for the four checked simple-reflection permutations.
  have h0 : Good k (rootAt 0) := base_good k
  have h4 : Good k (rootAt 4) := step 1 0 h0
  have h12 : Good k (rootAt 12) := step 0 4 h4
  have h8 : Good k (rootAt 8) := step 2 4 h4
  have h9 : Good k (rootAt 9) := step 3 4 h4
  have h16 : Good k (rootAt 16) := step 2 12 h12
  have h17 : Good k (rootAt 17) := step 3 12 h12
  have h5 : Good k (rootAt 5) := step 3 8 h8
  have h20 : Good k (rootAt 20) := step 1 16 h16
  have h13 : Good k (rootAt 13) := step 3 16 h16
  have h21 : Good k (rootAt 21) := step 1 17 h17
  have h1 : Good k (rootAt 1) := step 1 5 h5
  have h23 : Good k (rootAt 23) := step 3 20 h20
  have h14 : Good k (rootAt 14) := step 1 13 h13
  have h22 : Good k (rootAt 22) := step 2 21 h21
  have h2 : Good k (rootAt 2) := step 0 1 h1
  have h19 : Good k (rootAt 19) := step 1 23 h23
  have h6 : Good k (rootAt 6) := step 0 14 h14
  have h18 : Good k (rootAt 18) := step 2 14 h14
  have h11 : Good k (rootAt 11) := step 0 19 h19
  have h15 : Good k (rootAt 15) := step 2 19 h19
  have h10 : Good k (rootAt 10) := step 2 6 h6
  have h7 : Good k (rootAt 7) := step 2 11 h11
  have h3 : Good k (rootAt 3) := step 1 7 h7
  fin_cases r
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23

/-- Both source commutator relations on the genuine Clifford Spin root points,
including all signs and every distinct nonopposite pair. -/
public theorem spinCommutatorRelations : SpinCommutatorRelations k := by
  constructor
  · intro r s q hrs hopp hq a b
    exact (all_good k r s hrs hopp).1 q (Subtype.ext hq) a b
  · intro r s hrs hopp hq a b
    refine (all_good k r s hrs hopp).2 ?_ a b
    intro q he
    exact hq q (congrArg Subtype.val he)

end
end SpinComparisonExistence.PointConstruction
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
