module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Parameters
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.CartanEntries

/-!
# Four-root coordinates on the positive middle Levi block

The positive middle support consists of four roots of a B₂ subsystem.
The exact matrix swap and commutation relations collect its entire generated
subgroup into four root parameters. Triangular Cartan entries distinguish
these parameters, with their hypotheses discharged by the proved matrix-entry
formula. No global split-factorization hypothesis is needed.

The supplied local twist acts on these words by the quartet polynomial from
`FixedCoordinates.Scalars`. This module proves the split-block coordinates;
`SuzukiCoordinates` solves the fixed equations in the literal type V order
and transports the resulting chart to the negative block.

Source: GLS3, Table 2.4 type V and §2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiChart
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Subgroup Parabolics RadicalCoordinates FixedCoordinates
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}

def roots : Fin 4 → F4Chevalley.Root :=
  ![typeF4SimpleRootIndex 1, typeF4SimpleRootIndex 2,
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) (typeF4SimpleRootIndex 2),
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) (typeF4SimpleRootIndex 1)]

theorem roots_val (i : Fin 4) :
    (roots i).val = ![![0, 0, 1, -1], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1]] i := by
  fin_cases i
  · rfl
  · rfl
  all_goals
    change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
      typeF4RootPairing_simpleIndex_pairing]
    norm_num [typeF4CartanMatrix, typeF4SimpleRoot, funext_iff, Fin.forall_fin_succ, Fin.ext_iff]

theorem roots_block (i : Fin 4) :
    ((rootBlocks .positive).roots (.inr ((0 : Fin 4), i))).val = roots i := by
  apply Subtype.ext
  rw [rootBlocks_roots_val, roots_val]
  fin_cases i <;> rfl

theorem positive (i : Fin 4) : typeF4RootPairing_base.IsPos (roots i) := by
  rw [← roots_block]
  exact ((rootBlocks .positive).roots (.inr ((0 : Fin 4), i))).property

theorem long : IsLongRoot (roots 0) := by
  rw [← roots_block]
  exact (rootBlocks .positive).quartet_long (0 : Fin 4)

theorem short : IsShortRoot (roots 1) := by
  have h := (exceptionalRootPermutation_long_iff (roots 0)).mp long
  have hd : exceptionalRootPermutation (roots 0) = roots 1 := by
    simpa only [roots_block] using (rootBlocks .positive).quartet_dual_zero (0 : Fin 4)
  rwa [hd] at h

theorem root_sum : (roots 2).val = (roots 0).val + (roots 1).val := by
  simpa only [roots_block] using (rootBlocks .positive).quartet_add (0 : Fin 4)

theorem root_top : (roots 3).val = (roots 0).val + (2 : ℝ) • (roots 1).val := by
  simpa only [roots_block] using (rootBlocks .positive).quartet_add_two (0 : Fin 4)

theorem root_dot : dot (roots 0).val (roots 1).val = -1 := by
  simpa only [roots_block] using (rootBlocks .positive).quartet_dot (0 : Fin 4)

theorem simpleBlockRoot_iff (r : F4Chevalley.Root) :
    IsSimpleBlockRoot .suzuki true r ↔ ∃ i, r = roots i := by
  constructor
  · rintro ⟨hs, hp⟩
    obtain ⟨i, hi⟩ := RootPartition.table_exhaustive r hp
    have h0 := hs 0 (by simp [leviNodes])
    have h3 := hs 3 (by simp [leviNodes])
    rw [← hi, RootPartition.table_simpleCoefficient] at h0 h3
    fin_cases i <;> norm_num [RootPartition.coefficients, Matrix.cons_val_two, Matrix.cons_val_three] at h0 <;>
      norm_num [RootPartition.coefficients, Matrix.cons_val_two, Matrix.cons_val_three] at h3
    all_goals
      first
      | exact ⟨0, Subtype.ext (hi.symm.trans (roots_val 0).symm)⟩
      | exact ⟨1, Subtype.ext (hi.symm.trans (roots_val 1).symm)⟩
      | exact ⟨2, Subtype.ext (hi.symm.trans (roots_val 2).symm)⟩
      | exact ⟨3, Subtype.ext (hi.symm.trans (roots_val 3).symm)⟩
  · rintro ⟨i, rfl⟩
    refine ⟨?_, positive i⟩
    intro j hj
    have hj' : j = 0 ∨ j = 3 := by fin_cases j <;> simp_all [leviNodes]
    rcases hj' with rfl | rfl <;> rw [roots_val] <;>
      fin_cases i <;> norm_num [typeF4SimpleCoefficient]

abbrev X (i : Fin 4) (t : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m (roots i) t

theorem X_zero (i : Fin 4) : X (m := m) i 0 = 1 :=
  Subtype.ext (F4Chevalley.rootCurve_zero _)

theorem X_add (i : Fin 4) (a b : CoefficientField m) : X i (a + b) = X i a * X i b :=
  Subtype.ext (F4Chevalley.rootCurve_add _ _ _)

theorem X_self (i : Fin 4) (a : CoefficientField m) : X i a * X i a = 1 := by
  rw [← X_add, CharTwo.add_self_eq_zero, X_zero]

private theorem integral_relations :
    MatrixRelations.IntegralB2Relations (roots 0) (roots 1) (roots 2) (roots 3) :=
  MatrixRelations.integralB2Relations_of_brackets _ _ _ _ (positive 0) (positive 1)
    long short root_dot root_sum root_top
    (MatrixRelations.b2BracketRelations _ _ _ _ (positive 0) (positive 1)
      long short root_dot root_sum root_top)

theorem commute02 (a b : CoefficientField m) : Commute (X 0 a) (X 2 b) := by
  apply Subtype.ext
  exact (MatrixRelations.rootCurves_commute_of_operators_commute _ _ integral_relations.long_sum a b).eq

theorem commute03 (a b : CoefficientField m) : Commute (X 0 a) (X 3 b) := by
  apply Subtype.ext
  exact (MatrixRelations.rootCurves_commute_of_operators_commute _ _ integral_relations.long_top a b).eq

theorem commute13 (a b : CoefficientField m) : Commute (X 1 a) (X 3 b) := by
  apply Subtype.ext
  exact (MatrixRelations.rootCurves_commute_of_operators_commute _ _ integral_relations.short_top a b).eq

theorem commute23 (a b : CoefficientField m) : Commute (X 2 a) (X 3 b) := by
  apply Subtype.ext
  exact (MatrixRelations.rootCurves_commute_of_operators_commute _ _ integral_relations.sum_top a b).eq

theorem swap (a b : CoefficientField m) :
    X 1 b * X 0 a = X 0 a * X 1 b * X 2 (a * b) * X 3 (a * b ^ 2) :=
  b2RootSwap m _ _ _ _ (positive 0) (positive 1) long short root_dot root_sum root_top a b

private theorem correction_commute {G : Type*} [Group G] (A B C : G)
    (hA : A * A = 1) (hB : B * B = 1) (hC : C * C = 1)
    (h : B * A = A * B * C) : Commute B C := by
  have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_left hA
  have hBi : B⁻¹ = B := inv_eq_of_mul_eq_one_left hB
  have hCi : C⁻¹ = C := inv_eq_of_mul_eq_one_left hC
  have hi := congrArg Inv.inv h
  simp only [mul_inv_rev, hAi, hBi, hCi] at hi
  have h₁ := congrArg (fun x => A * x) h
  have h₂ := congrArg (fun x => x * A) hi
  simp only [← mul_assoc, hA, one_mul] at h₁
  simp only [mul_assoc, hA, mul_one] at h₂
  exact h₁.symm.trans (by simpa only [mul_assoc] using h₂)

theorem commute12 (b c : CoefficientField m) : Commute (X 1 b) (X 2 c) := by
  by_cases hb : b = 0
  · subst b
    rw [X_zero]
    exact Commute.one_left _
  have hw := swap (c / b) b
  rw [div_mul_cancel₀ _ hb] at hw
  have hCD := commute23 c ((c / b) * b ^ 2)
  have hE : (X 2 c * X 3 ((c / b) * b ^ 2)) *
      (X 2 c * X 3 ((c / b) * b ^ 2)) = 1 := by
    rw [hCD.symm.mul_mul_mul_comm, X_self, X_self, one_mul]
  have h := correction_commute _ _ _ (X_self 0 _) (X_self 1 _) hE
    (by simpa only [mul_assoc] using hw)
  have hh := h.mul_right (commute13 b ((c / b) * b ^ 2))
  rw [mul_assoc, X_self, mul_one] at hh
  exact hh

def splitWord (m : ℕ) (p : Fin 4 → CoefficientField m) : SplitGroup m :=
  quartetWord m roots p

theorem splitWord_def (p : Fin 4 → CoefficientField m) :
    splitWord m p = X 0 (p 0) * X 1 (p 1) * X 2 (p 2) * X 3 (p 3) := rfl

private def embedded (p : Fin 4 → CoefficientField m) :
    FixedCoordinates.BlockParameters m .positive :=
  (fun _ _ => 0, fun (i : Fin 4) (j : Fin 4) => if i = 0 then p j else 0)

private theorem root_zero (r : F4Chevalley.Root) : rootGeneratorInGroup m r 0 = 1 :=
  Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem embedded_word (p : Fin 4 → CoefficientField m) :
    (rootBlocks .positive).blockWord m (embedded p) = splitWord m p := by
  simp [RootBlocks.blockWord, embedded, pairWord, quartetWord, pairCount, quartetCount,
    List.ofFn_succ, root_zero, splitWord_def]
  change rootGeneratorInGroup m ((rootBlocks .positive).roots (.inr ((0 : Fin 4), 0))).val (p 0) *
    rootGeneratorInGroup m ((rootBlocks .positive).roots (.inr ((0 : Fin 4), 1))).val (p 1) *
    rootGeneratorInGroup m ((rootBlocks .positive).roots (.inr ((0 : Fin 4), 2))).val (p 2) *
    rootGeneratorInGroup m ((rootBlocks .positive).roots (.inr ((0 : Fin 4), 3))).val (p 3) = _
  rw [roots_block 0, roots_block 1, roots_block 2, roots_block 3]

theorem splitWord_injective : Function.Injective (splitWord m) := by
  have hinj : Function.Injective ((rootBlocks .positive).blockWord m) := by
    intro p q h
    apply ((rootBlocks .positive).repack m).symm.injective
    apply wordInSubgroup_injective_of_cartan_entries m (rootBlocks .positive).order
      (wordCartanEntry_sub_of_lower_eq m (rootBlocks .positive).order)
    apply Subtype.ext
    change word m (rootBlocks .positive).order _ = word m (rootBlocks .positive).order _
    simpa only [RootBlocks.word_eq_blockWord, Equiv.apply_symm_apply] using h
  intro p q h
  have he := hinj ((embedded_word p).trans (h.trans (embedded_word q).symm))
  funext i
  simpa [embedded] using
    congrFun (congrFun (congrArg Prod.snd he) (0 : Fin 4)) i

theorem twist_splitWord (d : LocalBlockInput m) (p : Fin 4 → CoefficientField m) :
    d.twist (splitWord m p) = splitWord m (quartetTwist m p) := by
  have he : d.twist (splitWord m p) = reeTwist m (splitWord m p) := by
    simp only [splitWord_def, map_mul, d.twist_root, reeTwist_rootGenerator]
  rw [he]
  simpa only [roots_block, splitWord] using
    (rootBlocks .positive).twist_quartet m (mixedRootCommutation m) (b2RootSwap m) (0 : Fin 4) p

theorem splitWord_fixed_iff (d : LocalBlockInput m) (p : Fin 4 → CoefficientField m) :
    d.twist (splitWord m p) = splitWord m p ↔
      p = quartetSolution m (p 0) (p 2) := by
  rw [twist_splitWord, splitWord_injective.eq_iff, quartetTwist_fixed_iff]

def central (c d : CoefficientField m) : SplitGroup m := X 2 c * X 3 d

theorem central_add (c d e f : CoefficientField m) :
    central (c + e) (d + f) = central c d * central e f := by
  simp only [central, X_add]
  exact ((commute23 e d).symm.mul_mul_mul_comm _ _).symm

theorem central_commute0 (a c d : CoefficientField m) : Commute (central c d) (X 0 a) :=
  (commute02 a c).symm.mul_left (commute03 a d).symm

theorem central_commute1 (b c d : CoefficientField m) : Commute (central c d) (X 1 b) :=
  (commute12 b c).symm.mul_left (commute13 b d).symm

theorem splitWord_mul (p q : Fin 4 → CoefficientField m) :
    splitWord m p * splitWord m q =
      splitWord m ![p 0 + q 0, p 1 + q 1,
        p 2 + q 2 + q 0 * p 1, p 3 + q 3 + q 0 * p 1 ^ 2] := by
  let E := central (p 2) (p 3)
  let F := central (q 2) (q 3)
  let K := central (q 0 * p 1) (q 0 * p 1 ^ 2)
  have hE : Commute E (X 0 (q 0) * X 1 (q 1)) :=
    (central_commute0 _ _ _).mul_right (central_commute1 _ _ _)
  have hK : Commute K (X 1 (q 1)) := central_commute1 _ _ _
  have hw : X 1 (p 1) * X 0 (q 0) = X 0 (q 0) * X 1 (p 1) * K := by
    simpa only [K, central, mul_assoc] using swap (q 0) (p 1)
  have hc : K * (E * F) =
      central (p 2 + q 2 + q 0 * p 1) (p 3 + q 3 + q 0 * p 1 ^ 2) := by
    dsimp only [K, E, F]
    rw [← central_add, ← central_add]
    congr 1 <;> ac_rfl
  have hword (v : Fin 4 → CoefficientField m) :
      splitWord m v = X 0 (v 0) * X 1 (v 1) * central (v 2) (v 3) := by
    simp only [splitWord_def, central, mul_assoc]
  rw [hword p, hword q]
  change (X 0 (p 0) * X 1 (p 1) * E) * (X 0 (q 0) * X 1 (q 1) * F) = _
  calc
    _ = (X 0 (p 0) * X 1 (p 1)) * (X 0 (q 0) * X 1 (q 1)) * (E * F) :=
      hE.mul_mul_mul_comm _ _
    _ = X 0 (p 0) * (X 1 (p 1) * X 0 (q 0)) * X 1 (q 1) * (E * F) := by
      simp only [mul_assoc]
    _ = (X 0 (p 0) * X 0 (q 0)) * (X 1 (p 1) * K * X 1 (q 1)) * (E * F) := by
      rw [hw]
      simp only [mul_assoc]
    _ = (X 0 (p 0) * X 0 (q 0)) * (X 1 (p 1) * X 1 (q 1) * K) * (E * F) := by
      rw [hK.right_comm]
    _ = X 0 (p 0 + q 0) * X 1 (p 1 + q 1) * (K * (E * F)) := by
      rw [← X_add, ← X_add]
      simp only [mul_assoc]
    _ = _ := by rw [hc, hword]; rfl

theorem splitWord_zero : splitWord m (fun _ => 0) = 1 := by
  simp only [splitWord_def, X, root_zero, mul_one]

theorem splitWord_inv (p : Fin 4 → CoefficientField m) :
    (splitWord m p)⁻¹ =
      splitWord m ![p 0, p 1, p 2 + p 0 * p 1, p 3 + p 0 * p 1 ^ 2] := by
  apply inv_eq_of_mul_eq_one_right
  rw [splitWord_mul]
  have he : (![p 0 + p 0, p 1 + p 1,
      p 2 + (p 2 + p 0 * p 1) + p 0 * p 1,
      p 3 + (p 3 + p 0 * p 1 ^ 2) + p 0 * p 1 ^ 2] : Fin 4 → CoefficientField m) =
      fun _ => 0 := by
    ext i
    fin_cases i <;> simp [Matrix.cons_val_two, Matrix.cons_val_three,
      ← add_assoc, CharTwo.add_self_eq_zero]
  change splitWord m ![p 0 + p 0, p 1 + p 1,
      p 2 + (p 2 + p 0 * p 1) + p 0 * p 1,
      p 3 + (p 3 + p 0 * p 1 ^ 2) + p 0 * p 1 ^ 2] = 1
  rw [he, splitWord_zero]

theorem splitWord_mem (p : Fin 4 → CoefficientField m) :
    splitWord m p ∈ splitSimpleBlock m .suzuki true := by
  have hx (i : Fin 4) (a : CoefficientField m) :
      X i a ∈ splitSimpleBlock m .suzuki true :=
    subset_closure ⟨roots i, a, (simpleBlockRoot_iff _).mpr ⟨i, rfl⟩, rfl⟩
  exact mul_mem (mul_mem (mul_mem (hx 0 _) (hx 1 _)) (hx 2 _)) (hx 3 _)

theorem splitWord_single (i : Fin 4) (a : CoefficientField m) :
    splitWord m (Pi.single i a) = X i a := by
  classical
  fin_cases i <;> simp [splitWord_def, X, root_zero, Fin.ext_iff]

theorem splitWord_cover {x : SplitGroup m} (hx : x ∈ splitSimpleBlock m .suzuki true) :
    ∃ p, splitWord m p = x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨r, a, hr, rfl⟩ := hx
      obtain ⟨i, rfl⟩ := (simpleBlockRoot_iff r).mp hr
      exact ⟨Pi.single i a, splitWord_single i a⟩
  | one => exact ⟨fun _ => 0, splitWord_zero⟩
  | mul x y _ _ hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      exact ⟨_, (splitWord_mul p q).symm⟩
  | inv x _ hx =>
      obtain ⟨p, rfl⟩ := hx
      exact ⟨_, (splitWord_inv p).symm⟩

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiChart
