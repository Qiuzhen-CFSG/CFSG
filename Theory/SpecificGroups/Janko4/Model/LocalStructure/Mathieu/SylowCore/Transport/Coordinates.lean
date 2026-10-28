module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.Bridge

/-!
# Binary coordinates and the actual max1 quotient action

Evaluation identifies bounded binary masks with the actual eleven-dimensional
kernel. The marked generator equations extend the pair-label comparison to
all local elements, and hence identify `starMask` with left conjugation.

Source: the ATLAS max1 kernel tables and pair-label certificates documented in
`Image.Coordinates`, `Image.StarData`, and `Image.Comparison`.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.Transport
open Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
open Cardinality.KernelCount Simplicity.Max1Fusion.QuotientInvolutions
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

/-- Projection through the literal local quotient to its marked star model. -/
noncomputable def starProjection : max1Subgroup hA hB →* StarGroup :=
  (quotientStarEquiv hA hB).toMonoidHom.comp (QuotientGroup.mk' (localKernel hA hB))

theorem starProjection_surjective : Function.Surjective (starProjection hA hB) :=
  (quotientStarEquiv hA hB).surjective.comp (QuotientGroup.mk'_surjective _)

theorem starProjection_ker : (starProjection hA hB).ker = localKernel hA hB := by
  ext g
  change quotientStarEquiv hA hB (QuotientGroup.mk' _ g) = 1 ↔ _
  rw [map_eq_one_iff _ (quotientStarEquiv hA hB).injective]
  exact QuotientGroup.eq_one_iff g

@[simp] theorem starProjection_x : starProjection hA hB (localX hA hB) = starFirst :=
  quotientStarEquiv_x hA hB

@[simp] theorem starProjection_y : starProjection hA hB (localY hA hB) = starSecond :=
  quotientStarEquiv_y hA hB

private def maskValue (m : ℕ) : localKernel hA hB :=
  coordinates hA hB (fun i => m.testBit i.val)

private lemma maskValue_zero : maskValue hA hB 0 = 1 := by
  apply Subtype.ext
  simp [maskValue, coordinates_val, binaryProduct_zero]

private lemma maskValue_xor (m n : ℕ) :
    maskValue hA hB (Nat.xor m n) = maskValue hA hB m * maskValue hA hB n := by
  change maskValue hA hB (m ^^^ n) = _
  simp only [maskValue, coordinates_mul, Nat.testBit_xor]

private lemma maskValue_fold (l : List ℕ) :
    maskValue hA hB (l.foldr Nat.xor 0) = (l.map (maskValue hA hB)).prod := by
  induction l with
  | nil => exact maskValue_zero hA hB
  | cons a l ih => simpa only [List.foldr_cons, List.map_cons, List.prod_cons,
      maskValue_xor] using congrArg (maskValue hA hB a * ·) ih

private lemma maskValue_maskImage (masks : Fin 11 → ℕ) (m : ℕ) :
    (maskValue hA hB (maskImage masks m) : max1Subgroup hA hB) =
      binaryProduct (fun i => binaryProduct (basis hA hB)
        (fun j => (masks i).testBit j.val)) (fun i => m.testBit i.val) := by
  rw [maskImage, maskValue_fold]
  simp only [List.map_ofFn, SubmonoidClass.coe_list_prod]
  rw [binaryProduct]
  congr 1
  congr 1
  funext i
  dsimp only [Function.comp_apply]
  split_ifs
  · rfl
  · change (maskValue hA hB 0 : max1Subgroup hA hB) = 1
    rw [maskValue_zero]
    rfl

private lemma right_compatible_x (i j : Fin 24) :
    action hA hB (localX hA hB)⁻¹ (maskValue hA hB (pairLabel i j)) =
      maskValue hA hB (pairLabel (rightX i) (rightX j)) := by
  apply Subtype.ext
  rw [action_apply, inv_inv, pairLabel_rightX, maskValue_maskImage]
  exact right_conj_coordinates_x hA hB _

private lemma right_compatible_y (i j : Fin 24) :
    action hA hB (localY hA hB)⁻¹ (maskValue hA hB (pairLabel i j)) =
      maskValue hA hB (pairLabel (rightY i) (rightY j)) := by
  apply Subtype.ext
  rw [action_apply, inv_inv, pairLabel_rightY, maskValue_maskImage]
  exact right_conj_coordinates_y hA hB _

private lemma maskValue_injective_bounded {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (h : maskValue hA hB m = maskValue hA hB n) : m = n := by
  have hb := coordinates_injective hA hB h
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 11
  · exact congrFun hb ⟨j, hj⟩
  · have hp : 2^11 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn hp)]

private lemma maskValue_basis (i : Fin 11) :
    (maskValue hA hB (2 ^ i.val) : max1Subgroup hA hB) = basis hA hB i := by
  simp only [maskValue, coordinates_val, Nat.testBit_two_pow]
  convert binaryProduct_single (basis hA hB) i using 2
  funext j
  simp only [Fin.ext_iff, eq_comm]


private def Compatible (g : max1Subgroup hA hB) : Prop :=
  ∀ i j, action hA hB g (maskValue hA hB (pairLabel i j)) =
    maskValue hA hB (pairLabel ((starProjection hA hB g).val i)
      ((starProjection hA hB g).val j))

private lemma compatible_inv {g : max1Subgroup hA hB} (h : Compatible hA hB g) :
    Compatible hA hB g⁻¹ := by
  intro i j
  apply (action hA hB g).injective
  simpa using
    (h ((starProjection hA hB g).val⁻¹ i) ((starProjection hA hB g).val⁻¹ j)).symm

private theorem compatible (g : max1Subgroup hA hB) : Compatible hA hB g := by
  have hg : g ∈ Subgroup.closure {localX hA hB, localY hA hB} := by
    rw [localXY_generate]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · have hr : Compatible hA hB (localX hA hB)⁻¹ := by
        intro i j
        simpa only [map_inv, starProjection_x, Subgroup.coe_inv, starFirst, starX,
          inv_inv] using right_compatible_x hA hB i j
      simpa only [inv_inv] using compatible_inv hA hB hr
    · obtain rfl := Set.mem_singleton_iff.mp hg
      have hr : Compatible hA hB (localY hA hB)⁻¹ := by
        intro i j
        simpa only [map_inv, starProjection_y, Subgroup.coe_inv, starSecond, starY,
          inv_inv] using right_compatible_y hA hB i j
      simpa only [inv_inv] using compatible_inv hA hB hr
  | one => intro i j; simp only [map_one, Subgroup.coe_one, Equiv.Perm.one_apply]
  | mul g k hg hk ig ik =>
    intro i j
    simp only [map_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply]
    rw [ik, ig]
  | inv g hg ih => exact compatible_inv hA hB ih

private theorem maskValue_starMask (g : max1Subgroup hA hB) (m : ℕ) :
    maskValue hA hB (starMask (starProjection hA hB g) m) =
      action hA hB g (maskValue hA hB m) := by
  have hb (i : Fin 11) :
      binaryProduct (basis hA hB)
        (fun j => (pairLabel ((starProjection hA hB g).val (basisPair i).1)
          ((starProjection hA hB g).val (basisPair i).2)).testBit j.val) =
        (MulAut.conj g) (basis hA hB i) := by
    have hi := compatible hA hB g (basisPair i).1 (basisPair i).2
    rw [pairLabel_basisPair] at hi
    have hv := congrArg (fun n : localKernel hA hB => (n : max1Subgroup hA hB)) hi
    rw [action_apply, maskValue_basis] at hv
    simpa only [maskValue, coordinates_val, MulAut.conj_apply] using hv.symm
  apply Subtype.ext
  rw [starMask, maskValue_maskImage]
  simp_rw [hb]
  exact (map_binaryProduct (MulAut.conj g).toMonoidHom _ _).symm

private theorem maskImage_lt (rows : Fin 11 → ℕ) (hr : ∀ i, rows i < 2048) (m : ℕ) :
    maskImage rows m < 2048 := by
  have hf (l : List ℕ) (hl : ∀ x ∈ l, x < 2048) : l.foldr Nat.xor 0 < 2048 := by
    induction l with
    | nil => decide
    | cons x l ih =>
      exact Nat.xor_lt_two_pow (n := 11) (hl x (by simp))
        (ih (fun y hy => hl y (by simp [hy])))
  apply hf
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split_ifs
  · exact hr i
  · decide

theorem starMask_lt (g : StarGroup) (m : ℕ) : starMask g m < 2048 :=
  maskImage_lt _ (fun _ => pairLabel_lt _ _) m

/-- Bounded mask evaluation in the actual elementary kernel. -/
def maskEval (m : Fin 2048) : localKernel hA hB := coordinates hA hB (fun i => m.val.testBit i.val)

theorem maskEval_injective : Function.Injective (maskEval hA hB) := by
  intro m n h
  exact Fin.ext (maskValue_injective_bounded hA hB m.isLt n.isLt h)

/-- Every element of the kernel has a unique bounded mask. -/
noncomputable def maskEquiv : Fin 2048 ≃ localKernel hA hB :=
  Equiv.ofBijective (maskEval hA hB)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨maskEval_injective hA hB, by rw [Nat.card_fin, localKernel_card]⟩)

@[simp] theorem maskEquiv_apply (m : Fin 2048) :
    maskEquiv hA hB m = maskEval hA hB m := rfl

/-- The mask action is exactly actual left conjugation, with the row convention. -/
theorem maskEquiv_starMask (g : max1Subgroup hA hB) (m : Fin 2048) :
    maskEquiv hA hB ⟨starMask (starProjection hA hB g) m.val, starMask_lt _ _⟩ =
      action hA hB g (maskEquiv hA hB m) :=
  maskValue_starMask hA hB g m.val

end Janko4.LocalStructure.SylowCore.Transport
