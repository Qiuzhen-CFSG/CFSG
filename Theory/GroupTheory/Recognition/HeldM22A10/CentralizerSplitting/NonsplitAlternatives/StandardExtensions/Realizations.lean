module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Parity
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitModels
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Realization of the two standard parity extensions

Explicit words in six generators compare each parity crossed product with its
published generated permutation subgroup on sixteen points. Every element has
a certified word. Multiplication by each of the six generators is checked in
those coordinates, and word induction proves the full multiplication law.
Trivial-kernel and range certificates yield actual multiplicative equivalences.

The generator images were found by exploratory GAP calculations. The Lean
kernel checks the word coverage, multiplication, kernel and range assertions;
no group identifier or external isomorphism routine enters the proofs.
Source context: Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
open LocalModelDichotomy AbelianExtension NonsplitModels

private def evalWord {M : Type*} [Monoid M] (g : Fin 6 → M) (w : List (Fin 6)) : M :=
  (w.map g).prod

private theorem evalWord_mem {M : Type*} [Group M] (H : Subgroup M)
    (g : Fin 6 → M) (hg : ∀ i, g i ∈ H) (w : List (Fin 6)) : evalWord g w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (hg i) ih

private def homFromWords {E M : Type*} [Group E] [Group M]
    (a : Fin 6 → E) (b : Fin 6 → M) (w : E → List (Fin 6))
    (hcover : ∀ x, evalWord a (w x) = x)
    (h1 : evalWord b (w 1) = 1)
    (hstep : ∀ i x, evalWord b (w (a i * x)) = b i * evalWord b (w x)) : E →* M where
  toFun x := evalWord b (w x)
  map_one' := h1
  map_mul' x y := by
    have hw : ∀ l z, evalWord b (w (evalWord a l * z)) =
        evalWord b l * evalWord b (w z) := by
      intro l
      induction l with
      | nil => intro z; simp [evalWord]
      | cons i l ih =>
        intro z
        change evalWord b (w ((a i * evalWord a l) * z)) =
          (b i * evalWord b l) * evalWord b (w z)
        rw [mul_assoc, hstep, ih, mul_assoc]
    have hx := hw (w x) 1
    rw [hcover, mul_one, h1, mul_one] at hx
    rw [← hcover x, hw, ← hx, hcover]

private def vectorAt (i : Fin 16) : BinaryFour :=
  Multiplicative.ofAdd (![![0, 0, 0, 0],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![1, 1, 0, 0],
    ![0, 0, 1, 0],
    ![1, 0, 1, 0],
    ![0, 1, 1, 0],
    ![1, 1, 1, 0],
    ![0, 0, 0, 1],
    ![1, 0, 0, 1],
    ![0, 1, 0, 1],
    ![1, 1, 0, 1],
    ![0, 0, 1, 1],
    ![1, 0, 1, 1],
    ![0, 1, 1, 1],
    ![1, 1, 1, 1]] i)

private def quotientAt (i : Fin 24) : SymmetricFour where
  toFun := (![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 1, 0, 3],
    ![2, 1, 3, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![3, 0, 1, 2],
    ![3, 0, 2, 1],
    ![3, 1, 0, 2],
    ![3, 1, 2, 0],
    ![3, 2, 0, 1],
    ![3, 2, 1, 0]] i)
  invFun := (![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 3, 1, 2],
    ![0, 2, 3, 1],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![2, 0, 1, 3],
    ![3, 0, 1, 2],
    ![2, 0, 3, 1],
    ![3, 0, 2, 1],
    ![1, 2, 0, 3],
    ![1, 3, 0, 2],
    ![2, 1, 0, 3],
    ![3, 1, 0, 2],
    ![2, 3, 0, 1],
    ![3, 2, 0, 1],
    ![1, 2, 3, 0],
    ![1, 3, 2, 0],
    ![2, 1, 3, 0],
    ![3, 1, 2, 0],
    ![2, 3, 1, 0],
    ![3, 2, 1, 0]] i)
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private theorem vectorAt_surjective : Function.Surjective vectorAt := by
  decide +kernel

private theorem quotientAt_surjective : Function.Surjective quotientAt := by
  decide +kernel

private theorem extension_coordinates {α : SymmetricFour →* MulAut BinaryFour}
    {c : FactorSet α} (x : c.Extension) :
    ∃ (v : Fin 16) (q : Fin 24), x = ⟨vectorAt v, quotientAt q⟩ := by
  obtain ⟨v, hv⟩ := vectorAt_surjective x.vector
  obtain ⟨q, hq⟩ := quotientAt_surjective x.quotient
  exact ⟨v, q, FactorSet.Extension.ext hv.symm hq.symm⟩

private def sourceGenerators {α : SymmetricFour →* MulAut BinaryFour}
    (c : FactorSet α) : Fin 6 → c.Extension :=
  ![⟨Multiplicative.ofAdd ![1,0,0,0], 1⟩,
    ⟨Multiplicative.ofAdd ![0,1,0,0], 1⟩,
    ⟨Multiplicative.ofAdd ![0,0,1,0], 1⟩,
    ⟨Multiplicative.ofAdd ![0,0,0,1], 1⟩,
    ⟨1, Equiv.swap 0 1⟩,
    ⟨1, { toFun := ![1,2,3,0], invFun := ![3,0,1,2],
          left_inv := by decide +kernel, right_inv := by decide +kernel }⟩]

private def quotientWord (q : SymmetricFour) : List (Fin 6) :=
  match (q 0).val * 64 + (q 1).val * 16 + (q 2).val * 4 + (q 3).val with
  | 27 => []
  | 30 => [5, 5, 4, 5, 5]
  | 39 => [5, 4, 5, 5, 5]
  | 45 => [4, 5]
  | 54 => [4, 5, 4, 5]
  | 57 => [5, 4, 5, 5, 4]
  | 75 => [4]
  | 78 => [4, 5, 5, 4, 5, 5]
  | 99 => [4, 5, 4, 5, 5, 5]
  | 108 => [5]
  | 114 => [5, 4, 5]
  | 120 => [4, 5, 4, 5, 5, 4]
  | 135 => [5, 5, 4, 5]
  | 141 => [4, 5, 4]
  | 147 => [4, 5, 5, 4, 5]
  | 156 => [5, 4]
  | 177 => [5, 5]
  | 180 => [4, 5, 5]
  | 198 => [5, 5, 5]
  | 201 => [5, 4, 5, 5]
  | 210 => [4, 5, 5, 5]
  | 216 => [4, 5, 4, 5, 5]
  | 225 => [5, 5, 4]
  | 228 => [4, 5, 5, 4]
  | _ => []

private def coordinateWord (v : BinaryFour) (q : SymmetricFour) : List (Fin 6) :=
  let w := quotientWord q
  let n := if w.length / 2 % 2 = 0 then v else v * diagonal
  (if n.toAdd 0 = 1 then [0] else []) ++
  (if n.toAdd 1 = 1 then [1] else []) ++
  (if n.toAdd 2 = 1 then [2] else []) ++
  (if n.toAdd 3 = 1 then [3] else []) ++ w

private def extensionWord {α : SymmetricFour →* MulAut BinaryFour}
    {c : FactorSet α} (x : c.Extension) : List (Fin 6) :=
  coordinateWord x.vector x.quotient

private def ordinaryGenerators (i : Fin 6) : Equiv.Perm (Fin 16) where
  toFun := (![
    ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 12, 13, 14, 15],
    ![2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 12, 13],
    ![11, 8, 9, 10, 7, 4, 5, 6, 3, 0, 1, 2, 15, 12, 13, 14],
    ![7, 4, 5, 6, 13, 14, 15, 12, 3, 0, 1, 2, 9, 10, 11, 8]] i)
  invFun := (![
    ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 12, 13, 14, 15],
    ![2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 12, 13],
    ![9, 10, 11, 8, 5, 6, 7, 4, 1, 2, 3, 0, 13, 14, 15, 12],
    ![9, 10, 11, 8, 1, 2, 3, 0, 15, 12, 13, 14, 7, 4, 5, 6]] i)
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private theorem ordinary_cover : ∀ x : permutationFactorSet.Extension,
    evalWord (sourceGenerators permutationFactorSet) (extensionWord x) = x := by
  have h : ∀ (v : Fin 16) (q : Fin 24),
      (evalWord (sourceGenerators permutationFactorSet) (coordinateWord (vectorAt v) (quotientAt q))).vector = vectorAt v ∧
      (evalWord (sourceGenerators permutationFactorSet) (coordinateWord (vectorAt v) (quotientAt q))).quotient = quotientAt q := by
    decide +kernel
  intro x
  obtain ⟨v, q, rfl⟩ := extension_coordinates x
  exact FactorSet.Extension.ext (h v q).1 (h v q).2

private theorem ordinary_step_table : ∀ (i : Fin 6) (v : Fin 16) (q : Fin 24),
    evalWord ordinaryGenerators (extensionWord (sourceGenerators permutationFactorSet i * ⟨vectorAt v, quotientAt q⟩)) =
      ordinaryGenerators i * evalWord ordinaryGenerators (coordinateWord (vectorAt v) (quotientAt q)) := by
  decide +kernel

private theorem ordinary_step : ∀ (i : Fin 6) (x : permutationFactorSet.Extension),
    evalWord ordinaryGenerators (extensionWord (sourceGenerators permutationFactorSet i * x)) =
      ordinaryGenerators i * evalWord ordinaryGenerators (extensionWord x) := by
  intro i x
  obtain ⟨v, q, rfl⟩ := extension_coordinates x
  exact ordinary_step_table i v q

private def ordinaryHom : permutationFactorSet.Extension →* Equiv.Perm (Fin 16) :=
  homFromWords (sourceGenerators permutationFactorSet) ordinaryGenerators extensionWord
    ordinary_cover (by decide +kernel) ordinary_step

private theorem ordinary_trivial_kernel : ∀ x : permutationFactorSet.Extension,
    ordinaryHom x = 1 → x = 1 := by
  have h : ∀ (v : Fin 16) (q : Fin 24),
      ordinaryHom ⟨vectorAt v, quotientAt q⟩ = 1 → vectorAt v = 1 ∧ quotientAt q = 1 := by
    decide +kernel
  intro x
  obtain ⟨v, q, rfl⟩ := extension_coordinates x
  intro hx
  exact FactorSet.Extension.ext (h v q hx).1 (h v q hx).2

private theorem ordinary_injective : Function.Injective ordinaryHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  exact ordinary_trivial_kernel x hx

private def ordinaryModelWord : Fin 6 → List (Fin 6) :=
  ![[1, 2, 3, 2, 1], [3, 3, 0, 1, 0], [1, 1, 2, 3, 2], [1, 0, 3, 3, 0], [0, 0, 1, 1, 0], [1, 2, 1, 1, 1]]

private def ordinaryModelGenerators : Fin 6 → Equiv.Perm (Fin 16) :=
  ![firstA, firstB, firstA⁻¹, firstB⁻¹, 1, 1]

private theorem ordinary_model_words : ∀ i,
    ordinaryGenerators i = evalWord ordinaryModelGenerators (ordinaryModelWord i) := by
  decide +kernel

private theorem ordinary_range : ordinaryHom.range = firstSubgroup := by
  have ha : firstA ∈ firstSubgroup := Subgroup.subset_closure (by simp)
  have hb : firstB ∈ firstSubgroup := Subgroup.subset_closure (by simp)
  have hg : ∀ i, ordinaryModelGenerators i ∈ firstSubgroup := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact firstSubgroup.inv_mem ha
    · exact firstSubgroup.inv_mem hb
    · exact firstSubgroup.one_mem
    · exact firstSubgroup.one_mem
  have ht : ∀ i, ordinaryGenerators i ∈ firstSubgroup := by
    intro i
    rw [ordinary_model_words]
    exact evalWord_mem _ _ hg _
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact evalWord_mem _ _ ht _
  · apply (Subgroup.closure_le _).mpr
    intro p hp
    rcases hp with rfl | rfl
    · exact ⟨evalWord (sourceGenerators permutationFactorSet) [2, 3, 5, 4, 5], by decide +kernel⟩
    · exact ⟨evalWord (sourceGenerators permutationFactorSet) [0, 1, 2, 5, 5, 4, 5], by decide +kernel⟩

/-- The ordinary parity crossed product is the exact published first model. -/
public noncomputable def permutationFactorSetEquivFirst :
    permutationFactorSet.Extension ≃* First :=
  (MonoidHom.ofInjective ordinary_injective).trans (MulEquiv.subgroupCongr ordinary_range)

private def twistedGenerators (i : Fin 6) : Equiv.Perm (Fin 16) where
  toFun := (![
    ![1, 0, 5, 12, 7, 2, 8, 4, 6, 13, 14, 15, 3, 9, 10, 11],
    ![1, 0, 5, 6, 7, 2, 3, 4, 12, 15, 14, 13, 8, 11, 10, 9],
    ![1, 0, 14, 6, 7, 10, 3, 4, 12, 13, 5, 15, 8, 9, 2, 11],
    ![7, 4, 5, 6, 1, 2, 3, 0, 12, 13, 14, 15, 8, 9, 10, 11],
    ![7, 0, 14, 13, 1, 2, 11, 4, 15, 6, 5, 12, 9, 8, 10, 3],
    ![6, 8, 7, 13, 12, 0, 11, 3, 15, 14, 1, 5, 9, 2, 4, 10]] i)
  invFun := (![
    ![1, 0, 5, 12, 7, 2, 8, 4, 6, 13, 14, 15, 3, 9, 10, 11],
    ![1, 0, 5, 6, 7, 2, 3, 4, 12, 15, 14, 13, 8, 11, 10, 9],
    ![1, 0, 14, 6, 7, 10, 3, 4, 12, 13, 5, 15, 8, 9, 2, 11],
    ![7, 4, 5, 6, 1, 2, 3, 0, 12, 13, 14, 15, 8, 9, 10, 11],
    ![1, 4, 5, 15, 7, 10, 9, 0, 13, 12, 14, 6, 11, 3, 2, 8],
    ![5, 10, 13, 7, 14, 11, 0, 2, 1, 12, 15, 6, 4, 3, 9, 8]] i)
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private theorem twisted_cover : ∀ x : twistedFactorSet.Extension,
    evalWord (sourceGenerators twistedFactorSet) (extensionWord x) = x := by
  have h : ∀ (v : Fin 16) (q : Fin 24),
      (evalWord (sourceGenerators twistedFactorSet) (coordinateWord (vectorAt v) (quotientAt q))).vector = vectorAt v ∧
      (evalWord (sourceGenerators twistedFactorSet) (coordinateWord (vectorAt v) (quotientAt q))).quotient = quotientAt q := by
    decide +kernel
  intro x
  obtain ⟨v, q, rfl⟩ := extension_coordinates x
  exact FactorSet.Extension.ext (h v q).1 (h v q).2

private theorem twisted_step_table : ∀ (i : Fin 6) (v : Fin 16) (q : Fin 24),
    evalWord twistedGenerators (extensionWord (sourceGenerators twistedFactorSet i * ⟨vectorAt v, quotientAt q⟩)) =
      twistedGenerators i * evalWord twistedGenerators (coordinateWord (vectorAt v) (quotientAt q)) := by
  decide +kernel

private theorem twisted_step : ∀ (i : Fin 6) (x : twistedFactorSet.Extension),
    evalWord twistedGenerators (extensionWord (sourceGenerators twistedFactorSet i * x)) =
      twistedGenerators i * evalWord twistedGenerators (extensionWord x) := by
  intro i x
  obtain ⟨v, q, rfl⟩ := extension_coordinates x
  exact twisted_step_table i v q

private def twistedHom : twistedFactorSet.Extension →* Equiv.Perm (Fin 16) :=
  homFromWords (sourceGenerators twistedFactorSet) twistedGenerators extensionWord
    twisted_cover (by decide +kernel) twisted_step

private theorem twisted_trivial_kernel : ∀ x : twistedFactorSet.Extension,
    twistedHom x = 1 → x = 1 := by
  have h : ∀ (v : Fin 16) (q : Fin 24),
      twistedHom ⟨vectorAt v, quotientAt q⟩ = 1 → vectorAt v = 1 ∧ quotientAt q = 1 := by
    decide +kernel
  intro x
  obtain ⟨v, q, rfl⟩ := extension_coordinates x
  intro hx
  exact FactorSet.Extension.ext (h v q hx).1 (h v q hx).2

private theorem twisted_injective : Function.Injective twistedHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  exact twisted_trivial_kernel x hx

private def twistedModelWord : Fin 6 → List (Fin 6) :=
  ![[3, 3, 0, 3, 3, 0, 3, 3, 0, 1, 0], [1, 1, 1], [3, 0, 3, 0, 1, 1, 0, 3, 0], [0, 3, 0, 1, 1, 1, 0, 1, 0], [3, 0, 1, 1, 1, 0, 1, 0], [3, 0, 1, 1, 1, 0, 3, 0]]

private def twistedModelGenerators : Fin 6 → Equiv.Perm (Fin 16) :=
  ![secondA, secondB, secondA⁻¹, secondB⁻¹, 1, 1]

private theorem twisted_model_words : ∀ i,
    twistedGenerators i = evalWord twistedModelGenerators (twistedModelWord i) := by
  decide +kernel

private theorem twisted_range : twistedHom.range = secondSubgroup := by
  have ha : secondA ∈ secondSubgroup := Subgroup.subset_closure (by simp)
  have hb : secondB ∈ secondSubgroup := Subgroup.subset_closure (by simp)
  have hg : ∀ i, twistedModelGenerators i ∈ secondSubgroup := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact secondSubgroup.inv_mem ha
    · exact secondSubgroup.inv_mem hb
    · exact secondSubgroup.one_mem
    · exact secondSubgroup.one_mem
  have ht : ∀ i, twistedGenerators i ∈ secondSubgroup := by
    intro i
    rw [twisted_model_words]
    exact evalWord_mem _ _ hg _
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact evalWord_mem _ _ ht _
  · apply (Subgroup.closure_le _).mpr
    intro p hp
    rcases hp with rfl | rfl
    · exact ⟨evalWord (sourceGenerators twistedFactorSet) [0, 1, 2, 4], by decide +kernel⟩
    · exact ⟨evalWord (sourceGenerators twistedFactorSet) [2, 5, 4], by decide +kernel⟩

/-- The twisted parity crossed product is the exact published second model. -/
public noncomputable def twistedFactorSetEquivSecond :
    twistedFactorSet.Extension ≃* Second :=
  (MonoidHom.ofInjective twisted_injective).trans (MulEquiv.subgroupCongr twisted_range)

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
