module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftWords
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondCharacter

/-!
# Native pair characters for the elementary-eight kernel bases

The full second-centralizer residual character is pointwise fixation of the
marked star pair. Explicit native word conjugators carry that seed to each
of four independent fixed-kernel pairs in both rows. Thus the full intrinsic
inner-half character is computed on the actual kernel elements, with the
original quotient projection retained. These are the pairings needed for
KW (1988), Propositions 2.3.4--2.3.5; no abstract form is substituted.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Theory.GroupTheory Subgroup Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
open LargeCenterRadicals.OuterHalf Janko4.InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "L" => SylowCore.Local
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four

theorem starHom_eq : starHom = π := by
  apply MonoidHom.eq_of_eqOn_dense (localXY_generate matrixA_mul_self matrixB_pow_four)
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · rw [starProjection_x]
    apply Subtype.ext
    exact actionImageEquivStarGroup_x _ _
  · obtain rfl := Set.mem_singleton_iff.mp hg
    rw [starProjection_y]
    apply Subtype.ext
    exact actionImageEquivStarGroup_y _ _

private theorem seedMask : nativeMask 1 = seed :=
  Simplicity.Max1Fusion.KernelOrbits.maskValue_one matrixA_mul_self matrixB_pow_four

theorem seed_inner_iff (g : L) (hc : Commute (nativeMask 1) g) :
    InnerRelated ((nativeMask 1 : L) : Model) (g : Model) ↔
      (π g).val 0 = 0 ∧ (π g).val 1 = 1 := by
  rw [seedMask] at hc ⊢
  have hg : g ∈ localCentralizer := mem_centralizer_singleton_iff.mpr hc.eq.symm
  simpa only [starHom_eq] using innerRelated_second_iff_star ⟨g,hg⟩

/-- The full inner-half character at every native conjugate of the kernel seed. -/
theorem conjugate_seed_inner_iff (h x : L)
    (hc : Commute (h * nativeMask 1 * h⁻¹) x) :
    InnerRelated ((h * nativeMask 1 * h⁻¹ : L) : Model) (x : Model) ↔
      (π x).val ((π h).val 0) = (π h).val 0 ∧
      (π x).val ((π h).val 1) = (π h).val 1 := by
  let y := h⁻¹ * x * h
  have hy : Commute (nativeMask 1) y := by
    have hh := hc.map (MulAut.conj h⁻¹).toMonoidHom
    simpa only [y, MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one, MulEquiv.coe_toMonoidHom] using hh
  have hi : InnerRelated ((h * nativeMask 1 * h⁻¹ : L) : Model) (x : Model) ↔
      InnerRelated ((nativeMask 1 : L) : Model) (y : Model) := by
    have hh := innerRelated_equiv (MulAut.conj (h : Model))
      ((nativeMask 1 : L) : Model) (y : Model)
    simpa only [y, MulAut.conj_apply, coe_mul, coe_inv, mul_assoc,
      mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh
  rw [hi, seed_inner_iff y hy]
  have he (i : Fin 24) : (π y).val i = i ↔
      (π x).val ((π h).val i) = (π h).val i := by
    change (π (h⁻¹ * x * h)).val i = i ↔ _
    rw [map_mul, map_mul, map_inv]
    change (π h).val.symm ((π x).val ((π h).val i)) = i ↔ _
    exact (π h).val.symm_apply_eq
  exact and_congr (he 0) (he 1)


private theorem alphabet_projection (i : Fin 4) :
    (π (nativeAlphabet i)).val = alphabet i := by
  fin_cases i
  · exact congrArg Subtype.val (starProjection_x _ _)
  · exact congrArg Subtype.val (starProjection_y _ _)
  · change (π (localX matrixA_mul_self matrixB_pow_four)⁻¹).val = starX⁻¹
    rw [map_inv, starProjection_x]
    rfl
  · change (π (localY matrixA_mul_self matrixB_pow_four)⁻¹).val = starY⁻¹
    rw [map_inv, starProjection_y]
    rfl

private theorem eval_projection (w : List (Fin 4)) :
    (π (evalWord nativeAlphabet w)).val = evalWord alphabet w := by
  induction w with
  | nil => simp only [evalWord, map_one, coe_one]
  | cons i w ih => simp only [evalWord, map_mul, coe_mul, alphabet_projection, ih]

@[expose] def kernelPairs : Fin 2 → Fin 4 → Fin 24 × Fin 24 := ![![(0,1), (2,3), (19,20), (13,21)], ![(0,1), (4,5), (11,12), (13,21)]]
@[expose] def kernelPairMasks : Fin 2 → Fin 4 → ℕ := ![![1,2,816,1128], ![1,4,819,1128]]
@[expose] def pairMoverWord : Fin 2 → Fin 4 → List (Fin 4) := ![![[], [0], [1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3], [0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0]], ![[], [1, 0], [0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3], [0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0]]]

@[expose] def pairMover (r : Fin 2) (j : Fin 4) : L :=
  evalWord nativeAlphabet (pairMoverWord r j)

theorem pairMover_marking (r : Fin 2) (j : Fin 4) :
    (π (pairMover r j)).val 0 = (kernelPairs r j).1 ∧
    (π (pairMover r j)).val 1 = (kernelPairs r j).2 := by
  simp only [pairMover, eval_projection]
  revert r j
  decide +kernel

theorem pairMover_seed (r : Fin 2) (j : Fin 4) :
    pairMover r j * nativeMask 1 * (pairMover r j)⁻¹ = nativeMask (kernelPairMasks r j) := by
  have h := congrArg (fun a : localKernel matrixA_mul_self matrixB_pow_four => (a : L))
    (starHom_pair (pairMover r j) 0 1)
  change pairMover r j * nativeMask 1 * (pairMover r j)⁻¹ =
    nativeMask (pairLabel ((starHom (pairMover r j)).val 0)
      ((starHom (pairMover r j)).val 1)) at h
  rw [starHom_eq, (pairMover_marking r j).1, (pairMover_marking r j).2] at h
  have he : ∀ r j, pairLabel (kernelPairs r j).1 (kernelPairs r j).2 = kernelPairMasks r j := by
    decide +kernel
  rwa [he] at h

/-- Exact residual membership for each of the four kernel basis pairs, for
 every native element centralizing it. -/
theorem kernelPair_inner_iff (r : Fin 2) (j : Fin 4) (x : L)
    (hc : Commute (nativeMask (kernelPairMasks r j)) x) :
    InnerRelated ((nativeMask (kernelPairMasks r j) : L) : Model) (x : Model) ↔
      (π x).val (kernelPairs r j).1 = (kernelPairs r j).1 ∧
      (π x).val (kernelPairs r j).2 = (kernelPairs r j).2 := by
  have hh := conjugate_seed_inner_iff (pairMover r j) x (by rwa [pairMover_seed])
  simpa only [pairMover_seed, (pairMover_marking r j).1, (pairMover_marking r j).2] using hh

end Janko4.LocalStructure.ElementaryEightGeometry
