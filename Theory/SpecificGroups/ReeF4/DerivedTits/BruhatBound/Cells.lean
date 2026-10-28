module

public import Theory.SpecificGroups.ReeF4.DerivedTits.BruhatBound.Geometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders

/-!
# Bounds for the restricted binary Ree Bruhat factors

At a fixed Weyl representative `n`, the positive intersection
`U ∩ n⁻¹Un` is disjoint from the right inversion subgroup `U ∩ n⁻¹U⁻n`.
Multiplication therefore injects their product into `U`. To lower-bound the
positive intersection, set all unselected blocks to zero in the known fixed
coordinate solution: each selected commuting pair contributes one binary
parameter, and each selected B₂ quartet contributes two. Unique split
coordinates make this family injective, without requiring the family itself
to be a subgroup.

The root calculations in `Geometry` and binary Weyl conjugation place every
selected block in the positive intersection. Since `|U| = 4096`, cancellation
gives all sixteen right-factor bounds. No presentation realization, exact
ambient order, or derived-group identification is used.

Sources: GLS3 §§2.3.5–2.3.8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.DerivedTits.BruhatBound
open Parabolics Parabolics.Binary.FixedGeometry LocalBlockInput LargeLocalSeeds
open Parabolics.Binary.FixedGeometry.BruhatCoverage
open RadicalCoordinates RadicalCoordinates.FixedCoordinates
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

/-- The positive intersection complementary to the inversion factor. -/
def fixedPositiveIntersection (n : Model 0) : Subgroup (Model 0) :=
  unipotent 0 ⊓ (unipotent 0).comap (MulAut.conj n).toMonoidHom

private theorem positive_disjoint_right (n : Model 0) :
    Disjoint (fixedPositiveIntersection n) (fixedRightUnipotent n) := by
  apply Subgroup.disjoint_def.mpr
  intro g hg hr
  apply toSplitGroup_injective 0
  have h := Subgroup.disjoint_def.mp (PairNormalization.splitUnipotent_disjoint_negative 0)
    (show toSplitGroup 0 n * toSplitGroup 0 g * (toSplitGroup 0 n)⁻¹ ∈ splitUnipotent 0 by
      have hp := hg.2
      change toSplitGroup 0 (n * g * n⁻¹) ∈ splitUnipotent 0 at hp
      simpa only [map_mul, map_inv] using hp)
    hr.2
  have he : toSplitGroup 0 g = 1 := by
    have hh := congrArg (fun z => (toSplitGroup 0 n)⁻¹ * z * toSplitGroup 0 n) h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  simpa only [map_one] using he

/-- An injective family in the positive intersection bounds the right factor. -/
theorem card_right_mul_le {α : Type*} [Finite α] (n : Model 0)
    (f : α → fixedPositiveIntersection n) (hf : Function.Injective f) :
    Nat.card α * Nat.card (fixedRightUnipotent n) ≤ 4096 := by
  let p : α × fixedRightUnipotent n → unipotent 0 := fun x =>
    ⟨(f x.1).val * x.2.val,
      (unipotent 0).mul_mem (f x.1).property.1 (fixedRightUnipotent_le n x.2.property)⟩
  have hp : Function.Injective p := by
    intro x y h
    have he : (f x.1, x.2) = (f y.1, y.2) :=
      Subgroup.mul_injective_of_disjoint (positive_disjoint_right n)
        (show (f x.1).val * x.2.val = (f y.1).val * y.2.val from congrArg Subtype.val h)
    exact Prod.ext (hf (congrArg Prod.fst he)) (congrArg (fun z : fixedPositiveIntersection n × fixedRightUnipotent n => z.2) he)
  have h := Nat.card_le_card_of_injective p hp
  rw [Nat.card_prod] at h
  simpa [card_unipotent] using h

/-- Free parameters on selected commuting pairs and B₂ quartets. -/
private abbrev PositiveParameters (P Q : Finset (Fin 4)) :=
  (P → CoefficientField 0) × (Q → Fin 2 → CoefficientField 0)

private def extendPair (P : Finset (Fin 4)) (a : P → CoefficientField 0)
    (i : Fin 4) : CoefficientField 0 :=
  if hi : i ∈ P then a ⟨i, hi⟩ else 0

private def extendQuartet (Q : Finset (Fin 4)) (a : Q → Fin 2 → CoefficientField 0)
    (i : Fin 4) : Fin 2 → CoefficientField 0 :=
  if hi : i ∈ Q then a ⟨i, hi⟩ else 0

private def selectedParameters (P Q : Finset (Fin 4)) (a : PositiveParameters P Q) :
    BlockParameters 0 .positive :=
  blockSolution 0 (extendPair P a.1, extendQuartet Q a.2)

private theorem selectedParameters_injective (P Q : Finset (Fin 4)) :
    Function.Injective (selectedParameters P Q) := by
  intro a b he
  apply Prod.ext
  · funext i
    have h := congrArg (fun t : BlockParameters 0 .positive => t.1 i.val 0) he
    simpa only [selectedParameters, blockSolution, pairSolution, Matrix.cons_val_zero,
      extendPair, dif_pos i.property] using h
  · funext i j
    fin_cases j
    · have h := congrArg (fun t : BlockParameters 0 .positive => t.2 i.val 0) he
      change extendQuartet Q a.2 i.val 0 = extendQuartet Q b.2 i.val 0 at h
      simpa [extendQuartet, i.property] using h
    · have h := congrArg (fun t : BlockParameters 0 .positive => t.2 i.val 2) he
      change extendQuartet Q a.2 i.val 1 = extendQuartet Q b.2 i.val 1 at h
      simpa [extendQuartet, i.property] using h

private theorem selectedParameters_fixed (P Q : Finset (Fin 4))
    (a : PositiveParameters P Q) :
    blockTwist 0 (selectedParameters P Q a) = selectedParameters P Q a := by
  apply Prod.ext
  · funext i
    exact pairSolution_fixed 0 _
  · funext i
    exact quartetSolution_fixed 0 _ _

private def selectedWord (P Q : Finset (Fin 4)) (a : PositiveParameters P Q) : SplitGroup 0 :=
  (rootBlocks .positive).blockWord 0 (selectedParameters P Q a)

private theorem selectedWord_injective (P Q : Finset (Fin 4)) :
    Function.Injective (selectedWord P Q) :=
  ((rootBlocks .positive).blockWord_injective 0
    (wordInSubgroup_bijective 0 _)).comp (selectedParameters_injective P Q)

private theorem selectedWord_fixed (P Q : Finset (Fin 4)) (a : PositiveParameters P Q) :
    reeTwist 0 (selectedWord P Q a) = selectedWord P Q a := by
  rw [selectedWord, RootBlocks.twist_blockWord _ _ (mixedRootCommutation 0) (b2RootSwap 0),
    selectedParameters_fixed]

private theorem selectedWord_mem (P Q : Finset (Fin 4)) (a : PositiveParameters P Q) :
    selectedWord P Q a ∈ splitUnipotent 0 := by
  have h := word_mem 0 (rootBlocks .positive).order
    (((rootBlocks .positive).repack 0).symm (selectedParameters P Q a))
  rwa [RootBlocks.word_eq_blockWord, Equiv.apply_symm_apply] at h

private theorem root_zero (r : F4Chevalley.Root) : rootGeneratorInGroup 0 r 0 = 1 :=
  Subtype.ext (F4Chevalley.rootCurve_zero r)

/-- Every selected block stays in the positive subgroup after conjugation. -/
private theorem selectedWord_conj_mem (P Q : Finset (Fin 4)) (n : SplitGroup 0)
    (hp : ∀ i ∈ P, ∀ j : Fin 2, ∀ t : CoefficientField 0,
      n * rootGeneratorInGroup 0 ((rootBlocks .positive).roots (.inl (i, j))).val t * n⁻¹ ∈
        splitUnipotent 0)
    (hq : ∀ i ∈ Q, ∀ j : Fin 4, ∀ t : CoefficientField 0,
      n * rootGeneratorInGroup 0 ((rootBlocks .positive).roots (.inr (i, j))).val t * n⁻¹ ∈
        splitUnipotent 0)
    (a : PositiveParameters P Q) : n * selectedWord P Q a * n⁻¹ ∈ splitUnipotent 0 := by
  let A := (splitUnipotent 0).comap (MulAut.conj n).toMonoidHom
  change selectedWord P Q a ∈ A
  apply A.mul_mem
  · apply A.list_prod_mem
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    change pairWord 0 _ (pairSolution 0 (extendPair P a.1 i)) ∈ A
    by_cases hi : i ∈ P
    · exact A.mul_mem (hp i hi 0 _) (hp i hi 1 _)
    · have hz : extendPair P a.1 i = 0 := by unfold extendPair; exact dif_neg hi
      rw [hz]
      simp [pairSolution, pairWord, root_zero]
  · apply A.list_prod_mem
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    change quartetWord 0 _ (quartetSolution 0 (extendQuartet Q a.2 i 0)
      (extendQuartet Q a.2 i 1)) ∈ A
    by_cases hi : i ∈ Q
    · exact A.mul_mem (A.mul_mem (A.mul_mem (hq i hi 0 _) (hq i hi 1 _))
        (hq i hi 2 _)) (hq i hi 3 _)
    · have hz : extendQuartet Q a.2 i = 0 := by unfold extendQuartet; exact dif_neg hi
      rw [hz]
      simp [quartetSolution, quartetWord, root_zero]

/-- The selected free coordinates give actual fixed matrices in the intersection. -/
private def positiveFamily (P Q : Finset (Fin 4)) (n : Model 0)
    (hp : ∀ i ∈ P, ∀ j : Fin 2, ∀ t : CoefficientField 0,
      toSplitGroup 0 n * rootGeneratorInGroup 0 ((rootBlocks .positive).roots (.inl (i, j))).val t *
        (toSplitGroup 0 n)⁻¹ ∈ splitUnipotent 0)
    (hq : ∀ i ∈ Q, ∀ j : Fin 4, ∀ t : CoefficientField 0,
      toSplitGroup 0 n * rootGeneratorInGroup 0 ((rootBlocks .positive).roots (.inr (i, j))).val t *
        (toSplitGroup 0 n)⁻¹ ∈ splitUnipotent 0) :
    PositiveParameters P Q → fixedPositiveIntersection n := fun a =>
  ⟨⟨selectedWord P Q a, (ReeF4.mem_fixedSubgroup 0 _).mpr (selectedWord_fixed P Q a)⟩,
    (by
      change toSplitGroup 0 _ ∈ splitUnipotent 0
      simpa only [toSplitGroup_apply] using selectedWord_mem P Q a), by
      change toSplitGroup 0 (n * _ * n⁻¹) ∈ splitUnipotent 0
      simpa only [map_mul, map_inv, toSplitGroup_apply] using
        selectedWord_conj_mem P Q (toSplitGroup 0 n) hp hq a⟩

private theorem positiveFamily_injective (P Q : Finset (Fin 4)) (n : Model 0) (hp hq) :
    Function.Injective (positiveFamily P Q n hp hq) := by
  intro a b h
  exact selectedWord_injective P Q (congrArg (fun x : fixedPositiveIntersection n => x.val.val) h)

private theorem card_positiveParameters (P Q : Finset (Fin 4)) :
    Nat.card (PositiveParameters P Q) = 2 ^ (P.card + 2 * Q.card) := by
  simp only [PositiveParameters, Nat.card_prod, Nat.card_fun, Nat.card_fin,
    Nat.card_eq_finsetCard, field_card, Nat.mul_zero, Nat.zero_add, pow_one,
    ← pow_mul, ← pow_add]


private theorem simpleWord_conjugation (l : List (Fin 4)) (r : F4Chevalley.Root)
    (t : CoefficientField 0) :
    simpleWord 0 l * rootGeneratorInGroup 0 r t * (simpleWord 0 l)⁻¹ =
      rootGeneratorInGroup 0 (typeF4RootPairing.weylGroupToPerm
        (FixedWeyl.rootWord l) r) t := by
  rw [FixedWeyl.rootWord, ← reflectionWord_eq_weylGroupToPerm]
  induction l with
  | nil => simp [simpleWord, reflectionWord]
  | cons i l ih =>
    have he : simpleWord 0 (i :: l) = simpleWord 0 [i] * simpleWord 0 l := by
      simpa using FixedWeyl.simpleWord_append 0 [i] l
    rw [he]
    calc
      _ = simpleWord 0 [i] * (simpleWord 0 l * rootGeneratorInGroup 0 r t *
          (simpleWord 0 l)⁻¹) * (simpleWord 0 [i])⁻¹ := by group
      _ = _ := by
        rw [ih, binarySimpleRootConjugation]
        simp only [List.map_cons, reflectionWord, typeF4RootPairing_baseEquiv_val]

private theorem pair_conjugation_mem (i : Fin 16) (j : Fin 4)
    (hj : j ∈ positivePairs i) (k : Fin 2) (t : CoefficientField 0) :
    toSplitGroup 0 (weylRepresentative i) *
      rootGeneratorInGroup 0 ((rootBlocks .positive).roots (.inl (j, k))).val t *
        (toSplitGroup 0 (weylRepresentative i))⁻¹ ∈ splitUnipotent 0 := by
  rw [toSplitGroup_weylRepresentative, simpleWord_conjugation]
  exact Subgroup.subset_closure ⟨_, t, positive_pairs_root i j hj k, rfl⟩

private theorem quartet_conjugation_mem (i : Fin 16) (j : Fin 4)
    (hj : j ∈ positiveQuartets i) (k : Fin 4) (t : CoefficientField 0) :
    toSplitGroup 0 (weylRepresentative i) *
      rootGeneratorInGroup 0 ((rootBlocks .positive).roots (.inr (j, k))).val t *
        (toSplitGroup 0 (weylRepresentative i))⁻¹ ∈ splitUnipotent 0 := by
  rw [toSplitGroup_weylRepresentative, simpleWord_conjugation]
  exact Subgroup.subset_closure ⟨_, t, positive_quartets_root i j hj k, rfl⟩

/-- Right-factor estimates for the sixteen actual binary Ree Bruhat cells. -/
theorem fixedRightUnipotent_card_le (i : Fin 16) :
    Nat.card (fixedRightUnipotent (weylRepresentative i)) ≤ 2 ^ cellExponent i := by
  have h := card_right_mul_le (weylRepresentative i)
    (positiveFamily (positivePairs i) (positiveQuartets i) (weylRepresentative i)
      (pair_conjugation_mem i) (quartet_conjugation_mem i))
    (positiveFamily_injective _ _ _ _ _)
  rw [card_positiveParameters] at h
  have he : 2 ^ ((positivePairs i).card + 2 * (positiveQuartets i).card) *
      2 ^ cellExponent i = 4096 := by
    rw [← pow_add, positive_block_exponents]
    norm_num
  exact Nat.le_of_mul_le_mul_left (h.trans_eq he.symm) (by positivity)

end ReeF4.DerivedTits.BruhatBound
