module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NativeRankOne
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.PositiveFactors

/-!
# Canonical finite pair-collection coefficients in the positive Ree subgroup

The checked split coordinates and the fixed block equations give an actual
12-parameter equivalence onto the full native unipotent subgroup. Quartet
parameters use the high-root convention of the signed simple Suzuki chart.
For each pair of positive relative roots, the coefficient vector is defined
uniquely by this equivalence, and its native collected equation is proved.
This is a table on two root letters, not a multiplication table on the full
Ree group. Abstract collection still requires the support properties of the
mixed entries and the compatible reduced dihedral ordering.

Source: GLS3 2.3.7 and 2.4.5, `refs/KGroup/GLS3/chapter2.tex`.
The underlying integral F₄ exchanges and matrix-entry injectivity are the
existing `RadicalOrders.SplitCoordinates` theorems.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.PositiveTables
open Theory.AlgebraicGroup
open Subgroup Parabolics RadicalCoordinates FixedCoordinates
open LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
variable {m : ℕ}

/-- Four linear parameters and four pairs in the high-root Suzuki convention. -/
abbrev Parameters (m : ℕ) :=
  (Fin 4 → CoefficientField m) × (Fin 4 → Fin 2 → CoefficientField m)

/-- Change only the second quartet coordinate from high root to mixed root. -/
def mixedCoordinates (m : ℕ) : Parameters m ≃ Parameters m where
  toFun p := (p.1, fun i => ![p.2 i 0, p.2 i 0*theta m (p.2 i 0)+theta m (p.2 i 1)])
  invFun p := (p.1, fun i => ![p.2 i 0, titsEnd m (p.2 i 1)+p.2 i 0*titsEnd m (p.2 i 0)])
  left_inv p := by
    refine Prod.ext rfl ?_
    funext i j
    fin_cases j
    · rfl
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_add, map_mul,
        tits_theta]
      simp [add_assoc, add_left_comm, CharTwo.add_self_eq_zero, mul_comm]
  right_inv p := by
    refine Prod.ext rfl ?_
    funext i j
    fin_cases j
    · rfl
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_add, map_mul,
        theta_tits]
      simp [add_left_comm, CharTwo.add_self_eq_zero, mul_comm]

/-- Native split-coordinate uniqueness in the fixed block order. -/
theorem split_bijective (m : ℕ) :
    Function.Bijective (wordInSubgroup m (rootBlocks .positive).order) :=
  wordInSubgroup_bijective_of_matrix_relations m _
    (rootGenerator_exchange m) (wordCartanEntry_sub_of_lower_eq m _)

/-- The fixed-coordinate equivalence is constructed, without a cardinality choice. -/
def coordinates (m : ℕ) : Parameters m ≃ unipotent m :=
  (mixedCoordinates m).trans (((blockFixedEquiv m .positive).symm.trans
    ((rootBlocks .positive).fixedParametersEquiv m (split_bijective m)
      (mixedRootCommutation m) (b2RootSwap m)).symm).trans
        (fixedEquiv m (rootBlocks .positive).order (split_bijective m)))

/-- The positive word retains each literal split root in the checked block order. -/
theorem coordinates_split (p : Parameters m) :
    toSplitGroup m (coordinates m p) =
      (rootBlocks .positive).blockWord m (blockSolution m (mixedCoordinates m p)) := by
  change toSplitGroup m (fixedWord m (rootBlocks .positive).order _) = _
  rw [fixedWord_coe, RootBlocks.word_eq_blockWord]
  change (rootBlocks .positive).blockWord m
    ((rootBlocks .positive).repack m
      (((rootBlocks .positive).repack m).symm (blockSolution m (mixedCoordinates m p)))) = _
  rw [Equiv.apply_symm_apply]

/-- The same two-parameter convention as `suzukiWord`, with the last two roots
placed in the checked partition order (mixed before high). -/
def quartetParameters (t u : CoefficientField m) : Fin 4 → CoefficientField m :=
  ![t, theta m t, t*theta m t+theta m u, u]

private theorem solution_mixed (t u : CoefficientField m) :
    quartetSolution m t (t*theta m t+theta m u) = quartetParameters t u := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change titsEnd m (t*theta m t+theta m u)+t*titsEnd m t = u
    rw [map_add, map_mul, tits_theta, tits_theta]
    simp [add_comm, add_left_comm, mul_comm, CharTwo.add_self_eq_zero]

/-- A linear relative root chart, as an element of the full native unipotent. -/
def pair (m : ℕ) (i : Fin 4) (t : CoefficientField m) : unipotent m :=
  ⟨⟨pairWord m (fun j => ((rootBlocks .positive).roots (.inl (i,j))).val)
      (pairSolution m t), by
        apply (ReeF4.mem_fixedSubgroup m _).mpr
        exact ((rootBlocks .positive).twist_pair m (mixedRootCommutation m) i _).trans
          (congrArg (pairWord m _) (pairSolution_fixed m t))⟩, by
      change toSplitGroup m _ ∈ LargeLocalSeeds.splitUnipotent m
      rw [toSplitGroup_apply]
      apply mul_mem
      · exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inl (i,0))).property, rfl⟩
      · exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inl (i,1))).property, rfl⟩⟩

/-- A full type V relative root chart, including its central high-root parameter. -/
def quartet (m : ℕ) (i : Fin 4) (t u : CoefficientField m) : unipotent m :=
  ⟨⟨quartetWord m (fun j => ((rootBlocks .positive).roots (.inr (i,j))).val)
      (quartetParameters t u), by
        apply (ReeF4.mem_fixedSubgroup m _).mpr
        have hf : quartetTwist m (quartetParameters t u) = quartetParameters t u := by
          rw [← solution_mixed]
          exact quartetSolution_fixed m _ _
        exact ((rootBlocks .positive).twist_quartet m (mixedRootCommutation m)
          (b2RootSwap m) i _).trans (congrArg (quartetWord m _) hf)⟩, by
      change toSplitGroup m _ ∈ LargeLocalSeeds.splitUnipotent m
      rw [toSplitGroup_apply]
      apply mul_mem
      · apply mul_mem
        · apply mul_mem
          · exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inr (i,0))).property, rfl⟩
          · exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inr (i,1))).property, rfl⟩
        · exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inr (i,2))).property, rfl⟩
      · exact subset_closure ⟨_, _, ((rootBlocks .positive).roots (.inr (i,3))).property, rfl⟩⟩

@[simp] theorem pair_split (i : Fin 4) (t : CoefficientField m) :
    toSplitGroup m (pair m i t) = pairWord m
      (fun j => ((rootBlocks .positive).roots (.inl (i,j))).val) (pairSolution m t) := by
  rw [toSplitGroup_apply]
  rfl

@[simp] theorem quartet_split (i : Fin 4) (t u : CoefficientField m) :
    toSplitGroup m (quartet m i t u) = quartetWord m
      (fun j => ((rootBlocks .positive).roots (.inr (i,j))).val) (quartetParameters t u) := by
  rw [toSplitGroup_apply]
  rfl

private theorem split_root_zero (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 :=
  Subtype.ext (F4Chevalley.rootCurve_zero r)

@[simp] theorem pair_zero (i : Fin 4) : pair m i 0 = 1 := by
  apply Subtype.ext
  apply toSplitGroup_injective m
  simp only [pair_split, Subgroup.coe_one, map_one, pairWord, pairSolution, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_zero, split_root_zero, mul_one]

@[simp] theorem quartet_zero (i : Fin 4) : quartet m i 0 0 = 1 := by
  apply Subtype.ext
  apply toSplitGroup_injective m
  simp only [quartet_split, Subgroup.coe_one, map_one, quartetWord, quartetParameters,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_zero, zero_mul, zero_add, split_root_zero, mul_one]

/-- The first quartet is literally the signed simple Suzuki chart already used
in the native Gauss equation. -/
theorem quartet_simple (t u : CoefficientField m) :
    (quartet m 0 t u : Model m) = suzuki m true t u := by
  apply toSplitGroup_injective m
  rw [quartet_split, suzuki_split, SuzukiChart.word_eq]
  have hr : (fun j : Fin 4 => ((rootBlocks .positive).roots (.inr ((0 : Fin 4),j))).val) =
      SuzukiChart.roots := funext SuzukiChart.roots_block
  rw [hr]
  rfl

/-- The central coordinate in the table has the nonlinear type V product law. -/
theorem quartet_simple_mul (t u v w : CoefficientField m) :
    quartet m 0 t u * quartet m 0 v w =
      quartet m 0 (t+v) (u+w+titsEnd m t*v) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, quartet_simple] using suzuki_mul true t u v w

/-- The actual eight-factor product, in the native pair-then-quartet order. -/
def product (p : Parameters m) : unipotent m :=
  (List.ofFn fun i => pair m i (p.1 i)).prod *
    (List.ofFn fun i => quartet m i (p.2 i 0) (p.2 i 1)).prod

private theorem blockSolution_mixed (p : Parameters m) :
    blockSolution m (k := .positive) (mixedCoordinates m p) =
      ((fun i => pairSolution m (p.1 i)),
        (fun i => quartetParameters (p.2 i 0) (p.2 i 1))) := by
  refine Prod.ext rfl ?_
  funext i
  exact solution_mixed _ _

private theorem product_split (p : Parameters m) :
    toSplitGroup m (product p) = (rootBlocks .positive).blockWord m
      ((fun i => pairSolution m (p.1 i)),
        (fun i => quartetParameters (p.2 i 0) (p.2 i 1))) := by
  let f : unipotent m →* SplitGroup m := (toSplitGroup m).comp (unipotent m).subtype
  change f ((List.ofFn fun i => pair m i (p.1 i)).prod *
    (List.ofFn fun i => quartet m i (p.2 i 0) (p.2 i 1)).prod) = _
  rw [map_mul, map_list_prod, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def]
  have hp (i : Fin 4) : f (pair m i (p.1 i)) = pairWord m
      (fun j => ((rootBlocks .positive).roots (.inl (i,j))).val) (pairSolution m (p.1 i)) :=
    pair_split i (p.1 i)
  have hq (i : Fin 4) : f (quartet m i (p.2 i 0) (p.2 i 1)) = quartetWord m
      (fun j => ((rootBlocks .positive).roots (.inr (i,j))).val)
      (quartetParameters (p.2 i 0) (p.2 i 1)) := quartet_split i _ _
  simp only [hp, hq, RootBlocks.blockWord]
  rfl

/-- Every coordinate vector evaluates as its literal eight positive root factors. -/
theorem coordinates_eq_product (p : Parameters m) : coordinates m p = product p := by
  apply Subtype.ext
  apply toSplitGroup_injective m
  rw [coordinates_split, product_split, blockSolution_mixed]
  rfl

/-- Native positive collection is both exhaustive and unique. -/
theorem product_bijective (m : ℕ) : Function.Bijective (product (m := m)) := by
  have he : product (m := m) = coordinates m := funext fun p => (coordinates_eq_product p).symm
  rw [he]
  exact (coordinates m).bijective

/-- The 24 positive split roots form eight relative blocks. -/
abbrev Root := PositiveBlockIndex

/-- One parameter for type VI, two for type V. -/
abbrev Parameter (m : ℕ) : Root → Type
  | .inl _ => CoefficientField m
  | .inr _ => CoefficientField m × CoefficientField m

/-- The native positive relative-root charts. -/
def root (m : ℕ) : (i : Root) → Parameter m i → unipotent m
  | .inl i, t => pair m i t
  | .inr i, p => quartet m i p.1 p.2

/-- A coordinate vector supported on one relative root. -/
def single (i : Root) (a : Parameter m i) : Parameters m :=
  match i, a with
  | .inl i, t => (fun j => if j = i then t else 0, fun _ _ => 0)
  | .inr i, p => (fun _ => 0, fun j => if j = i then ![p.1,p.2] else 0)

/-- A single supported coordinate vector evaluates to that literal root letter. -/
theorem product_single (i : Root) (a : Parameter m i) : product (single i a) = root m i a := by
  cases i with
  | inl i =>
    fin_cases i <;> simp [single, product, root, List.ofFn_succ]
  | inr i =>
    fin_cases i <;> simp [single, product, root, List.ofFn_succ]

@[simp] theorem product_zero : product (0 : Parameters m) = 1 := by
  simp [product, List.ofFn_succ]

/-- Native positive word faithfulness, in the exact twelve coordinate convention. -/
theorem product_eq_one_iff (p : Parameters m) : product p = 1 ↔ p = 0 := by
  rw [← product_zero, (product_bijective m).injective.eq_iff]

/-- Recovering a single root letter gives exactly its supported coordinate vector. -/
theorem coordinates_symm_root (i : Root) (a : Parameter m i) :
    (coordinates m).symm (root m i a) = single i a := by
  apply (coordinates m).injective
  rw [Equiv.apply_symm_apply, coordinates_eq_product, product_single]

/-- The canonical native coefficient vector for two root letters. It quantifies
only over eight root indices and their one- or two-field parameters. -/
def exchange (i j : Root) (a : Parameter m i) (b : Parameter m j) : Parameters m :=
  (coordinates m).symm (root m i a * root m j b)

/-- The native equation of every entry of the finite pair-collection table. -/
theorem exchange_equation (i j : Root) (a : Parameter m i) (b : Parameter m j) :
    root m i a * root m j b = product (exchange i j a b) := by
  rw [← coordinates_eq_product, exchange, Equiv.apply_symm_apply]

/-- These coefficients are uniquely determined by the native model and the fixed order. -/
theorem exchange_unique (i j : Root) (a : Parameter m i) (b : Parameter m j)
    (p : Parameters m) (hp : root m i a * root m j b = product p) :
    exchange i j a b = p := by
  apply (product_bijective m).injective
  exact (exchange_equation i j a b).symm.trans hp

/-- The simple type V entries of the collected table retain their central term. -/
theorem exchange_suzuki_simple (t u v w : CoefficientField m) :
    exchange (.inr 0) (.inr 0) (t,u) (v,w) =
      single (.inr 0) (t+v,u+w+titsEnd m t*v) := by
  apply exchange_unique
  rw [product_single]
  exact quartet_simple_mul t u v w

/-- The binary table has a nonzero square, rather than the additive-pair law. -/
theorem exchange_binary_square :
    exchange (m := 0) (.inr 0) (.inr 0) (1,0) (1,0) = single (.inr 0) (0,1) := by
  rw [exchange_suzuki_simple]
  simp only [CharTwo.add_self_eq_zero, map_one, one_mul, zero_add]

end ReeF4.RootPresentationRecognition.PositiveTables
