module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.Bruhat

/-!
# Independent fixed parameters on selected Ree blocks

Set unselected positive blocks to zero in the solved fixed-coordinate equations.
Unique split coordinates make the resulting family injective over every Ree
coefficient field. If the selected roots conjugate into a subgroup `H`, the
family lies in the actual intersection `U ∩ n⁻¹Hn` in the fixed matrix group.
The positive and negative intersections are disjoint, giving the complementary
upper bound for the right Bruhat factor.

This generalizes the binary construction in `DerivedTits/BruhatBound/Cells.lean`.
Source: GLS3 2.3.7–2.3.8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities
open Parabolics Parabolics.Binary.FixedGeometry LocalBlockInput LargeLocalSeeds
open RadicalCoordinates RadicalCoordinates.FixedCoordinates
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

/-- A positive fixed matrix whose left conjugate by `n` lies in `H`. -/
@[expose] def fixedIntersection {m : ℕ} (n : Model m) (H : Subgroup (SplitGroup m)) :
    Subgroup (Model m) :=
  (splitUnipotent m ⊓ H.comap (MulAut.conj (toSplitGroup m n)).toMonoidHom).comap
    (toSplitGroup m)

private theorem positive_disjoint_right {m : ℕ} (n : Model m) :
    Disjoint (fixedIntersection n (splitUnipotent m)) (fixedRightUnipotent n) := by
  apply Subgroup.disjoint_def.mpr
  intro g hg hr
  apply toSplitGroup_injective m
  have h := Subgroup.disjoint_def.mp (PairNormalization.splitUnipotent_disjoint_negative m)
    hg.2 hr.2
  have he : toSplitGroup m g = 1 := by
    have hh := congrArg (fun z => (toSplitGroup m n)⁻¹ * z * toSplitGroup m n) h
    change (toSplitGroup m n)⁻¹ *
      (toSplitGroup m n * toSplitGroup m g * (toSplitGroup m n)⁻¹) * toSplitGroup m n =
      (toSplitGroup m n)⁻¹ * 1 * toSplitGroup m n at hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  simpa only [map_one] using he

/-- An injective family in the positive intersection bounds the actual right factor. -/
theorem card_right_mul_le {m : ℕ} {α : Type*} [Finite α] (n : Model m)
    (f : α → fixedIntersection n (splitUnipotent m)) (hf : Function.Injective f) :
    Nat.card α * Nat.card (fixedRightUnipotent n) ≤ (2 ^ (2 * m + 1)) ^ 12 := by
  let p : α × fixedRightUnipotent n → unipotent m := fun x =>
    ⟨(f x.1).val * x.2.val,
      (unipotent m).mul_mem (f x.1).property.1 x.2.property.1⟩
  have hp : Function.Injective p := by
    intro x y h
    have he : (f x.1, x.2) = (f y.1, y.2) :=
      Subgroup.mul_injective_of_disjoint (positive_disjoint_right n)
        (show (f x.1).val * x.2.val = (f y.1).val * y.2.val from congrArg Subtype.val h)
    exact Prod.ext (hf (congrArg Prod.fst he))
      (congrArg (fun z : fixedIntersection n (splitUnipotent m) × fixedRightUnipotent n => z.2) he)
  have h := Nat.card_le_card_of_injective p hp
  rw [Nat.card_prod, card_unipotent] at h
  exact h

/-- Free field parameters on selected commuting pairs and B₂ quartets. -/
abbrev SelectedParameters (m : ℕ) (P Q : Finset (Fin 4)) :=
  (P → CoefficientField m) × (Q → Fin 2 → CoefficientField m)

private def extendPair (m : ℕ) (P : Finset (Fin 4)) (a : P → CoefficientField m)
    (i : Fin 4) : CoefficientField m :=
  if hi : i ∈ P then a ⟨i, hi⟩ else 0

private def extendQuartet (m : ℕ) (Q : Finset (Fin 4)) (a : Q → Fin 2 → CoefficientField m)
    (i : Fin 4) : Fin 2 → CoefficientField m :=
  if hi : i ∈ Q then a ⟨i, hi⟩ else 0

private def selectedParameters (m : ℕ) (P Q : Finset (Fin 4)) (a : SelectedParameters m P Q) :
    BlockParameters m .positive :=
  blockSolution m (extendPair m P a.1, extendQuartet m Q a.2)

private theorem selectedParameters_injective (m : ℕ) (P Q : Finset (Fin 4)) :
    Function.Injective (selectedParameters m P Q) := by
  intro a b he
  apply Prod.ext
  · funext i
    have h := congrArg (fun t : BlockParameters m .positive => t.1 i.val 0) he
    simpa only [selectedParameters, blockSolution, pairSolution, Matrix.cons_val_zero,
      extendPair, dif_pos i.property] using h
  · funext i j
    fin_cases j
    · have h := congrArg (fun t : BlockParameters m .positive => t.2 i.val 0) he
      change extendQuartet m Q a.2 i.val 0 = extendQuartet m Q b.2 i.val 0 at h
      simpa [extendQuartet, i.property] using h
    · have h := congrArg (fun t : BlockParameters m .positive => t.2 i.val 2) he
      change extendQuartet m Q a.2 i.val 1 = extendQuartet m Q b.2 i.val 1 at h
      simpa [extendQuartet, i.property] using h

private theorem selectedParameters_fixed (m : ℕ) (P Q : Finset (Fin 4))
    (a : SelectedParameters m P Q) :
    blockTwist m (selectedParameters m P Q a) = selectedParameters m P Q a := by
  apply Prod.ext
  · funext i
    exact pairSolution_fixed m _
  · funext i
    exact quartetSolution_fixed m _ _

private def selectedWord (m : ℕ) (P Q : Finset (Fin 4)) (a : SelectedParameters m P Q) : SplitGroup m :=
  (rootBlocks .positive).blockWord m (selectedParameters m P Q a)

private theorem selectedWord_injective (m : ℕ) (P Q : Finset (Fin 4)) :
    Function.Injective (selectedWord m P Q) :=
  ((rootBlocks .positive).blockWord_injective m
    (wordInSubgroup_bijective m _)).comp (selectedParameters_injective m P Q)

private theorem selectedWord_fixed (m : ℕ) (P Q : Finset (Fin 4)) (a : SelectedParameters m P Q) :
    reeTwist m (selectedWord m P Q a) = selectedWord m P Q a := by
  rw [selectedWord, RootBlocks.twist_blockWord _ _ (mixedRootCommutation m) (b2RootSwap m),
    selectedParameters_fixed m]

private theorem selectedWord_mem (m : ℕ) (P Q : Finset (Fin 4)) (a : SelectedParameters m P Q) :
    selectedWord m P Q a ∈ splitUnipotent m := by
  have h := word_mem m (rootBlocks .positive).order
    (((rootBlocks .positive).repack m).symm (selectedParameters m P Q a))
  rwa [RootBlocks.word_eq_blockWord, Equiv.apply_symm_apply] at h

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) : rootGeneratorInGroup m r 0 = 1 :=
  Subtype.ext (F4Chevalley.rootCurve_zero r)

/-- Each selected root conjugates into the specified subgroup. -/
private theorem selectedWord_conj_mem (m : ℕ) (P Q : Finset (Fin 4)) (n : SplitGroup m)
    (H : Subgroup (SplitGroup m))
    (hp : ∀ i ∈ P, ∀ j : Fin 2, ∀ t : CoefficientField m,
      n * rootGeneratorInGroup m ((rootBlocks .positive).roots (.inl (i, j))).val t * n⁻¹ ∈
        H)
    (hq : ∀ i ∈ Q, ∀ j : Fin 4, ∀ t : CoefficientField m,
      n * rootGeneratorInGroup m ((rootBlocks .positive).roots (.inr (i, j))).val t * n⁻¹ ∈
        H)
    (a : SelectedParameters m P Q) : n * selectedWord m P Q a * n⁻¹ ∈ H := by
  let A := H.comap (MulAut.conj n).toMonoidHom
  change selectedWord m P Q a ∈ A
  apply A.mul_mem
  · apply A.list_prod_mem
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    change pairWord m _ (pairSolution m (extendPair m P a.1 i)) ∈ A
    by_cases hi : i ∈ P
    · exact A.mul_mem (hp i hi 0 _) (hp i hi 1 _)
    · have hz : extendPair m P a.1 i = 0 := by unfold extendPair; exact dif_neg hi
      rw [hz]
      simp [pairSolution, pairWord, root_zero m]
  · apply A.list_prod_mem
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    change quartetWord m _ (quartetSolution m (extendQuartet m Q a.2 i 0)
      (extendQuartet m Q a.2 i 1)) ∈ A
    by_cases hi : i ∈ Q
    · exact A.mul_mem (A.mul_mem (A.mul_mem (hq i hi 0 _) (hq i hi 1 _))
        (hq i hi 2 _)) (hq i hi 3 _)
    · have hz : extendQuartet m Q a.2 i = 0 := by unfold extendQuartet; exact dif_neg hi
      rw [hz]
      simp [quartetSolution, quartetWord, root_zero m]

/-- The selected free coordinates give actual fixed matrices in the intersection. -/
def intersectionFamily (m : ℕ) (P Q : Finset (Fin 4)) (n : Model m) (H : Subgroup (SplitGroup m))
    (hp : ∀ i ∈ P, ∀ j : Fin 2, ∀ t : CoefficientField m,
      toSplitGroup m n * rootGeneratorInGroup m ((rootBlocks .positive).roots (.inl (i, j))).val t *
        (toSplitGroup m n)⁻¹ ∈ H)
    (hq : ∀ i ∈ Q, ∀ j : Fin 4, ∀ t : CoefficientField m,
      toSplitGroup m n * rootGeneratorInGroup m ((rootBlocks .positive).roots (.inr (i, j))).val t *
        (toSplitGroup m n)⁻¹ ∈ H) :
    SelectedParameters m P Q → fixedIntersection n H := fun a =>
  ⟨⟨selectedWord m P Q a, (ReeF4.mem_fixedSubgroup m _).mpr (selectedWord_fixed m P Q a)⟩,
    (by
      change toSplitGroup m _ ∈ splitUnipotent m
      simpa only [toSplitGroup_apply] using selectedWord_mem m P Q a), by
      change toSplitGroup m n * toSplitGroup m _ * (toSplitGroup m n)⁻¹ ∈ H
      simpa only [toSplitGroup_apply] using
        selectedWord_conj_mem m P Q (toSplitGroup m n) H hp hq a⟩

/-- Unique split coordinates distinguish all selected fixed-parameter words. -/
theorem intersectionFamily_injective (m : ℕ) (P Q : Finset (Fin 4))
    (n : Model m) (H : Subgroup (SplitGroup m)) (hp hq) :
    Function.Injective (intersectionFamily m P Q n H hp hq) := by
  intro a b h
  exact selectedWord_injective m P Q (congrArg (fun x : fixedIntersection n H => x.val.val) h)

/-- One free parameter per selected pair and two per selected quartet. -/
theorem card_selectedParameters (m : ℕ) (P Q : Finset (Fin 4)) :
    Nat.card (SelectedParameters m P Q) = (2 ^ (2 * m + 1)) ^ (P.card + 2 * Q.card) := by
  simp only [SelectedParameters, Nat.card_prod, Nat.card_fun, Nat.card_fin,
    Nat.card_eq_finsetCard, field_card,
    ← pow_mul, ← pow_add]
  congr 1
  ring

end ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities
