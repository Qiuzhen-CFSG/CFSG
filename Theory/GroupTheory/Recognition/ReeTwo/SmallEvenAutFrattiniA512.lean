module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenAutCarrierA512
public import Theory.Frattini.BinarySquares

/-!
# Frattini kernels of the six order-512 small even candidates

The fixed rank-four and rank-three coordinate maps preserve multiplication:
substitute the nine free carrier parameters into the polynomial even-complement
multiplication, then simplify over the binary field. Candidate 4 uses the
quadratic correction already specified by its coordinate map.

For the converse kernel inclusion, each identity fiber has a normal form in
five core generators (six for candidate 4). The square-word table expresses
these generators as products of squares of words in the original nine candidate
generators. The normal form for candidate 4 includes the central correction
`b₂ b₄`. All table identities and normal forms are checked by the Lean kernel.
The finite two-group square-generation theorem then identifies each fiber with
its Frattini subgroup.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified `Core`, `Sylow`,
and `EvenCoordinates` models. The quotient conventions are those of
`SmallEvenAutCoordinatesA512`; the square-generation argument follows
`SmallParityFourFrattini` and `Theory.Frattini.BinarySquares`.
-/

namespace ReeTwo.SylowModel
open ReeTwo.SmallEvenAutProfilesA
set_option maxRecDepth 16384
private def fourCarrierRow (j : Fin 5) : Fin 6 := ![0,1,2,4,5] j
private theorem highBit_twice (t : ZMod 2) :
    (((2 * t.val : ZMod 4).val / 2 : ℕ) : ZMod 2) = t :=
  (by decide : ∀ t : ZMod 2, (((2 * t.val : ZMod 4).val / 2 : ℕ) : ZMod 2) = t) t
private theorem four_toAdd (j : Fin 5) (x : SylowModel) :
    (smallEvenFourCoordinatesA512 j x).toAdd =
      let b := x.left
      let t : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
      (![![b.b0 + b.b3 + b.b4, b.b3 + b.b4, b.b0 + t, b.b5 + b.b6],
        ![b.b0 + b.b2 + b.b4, b.b2 + b.b4, b.b0 + t, b.b2 + b.b6],
        ![b.b0 + t, t, b.b3 + b.b4 + t, b.b5 + t],
        ![b.b2 + b.b3 + t, t, b.b2 + b.b4 + b.b5, b.b4 + b.b5],
        ![b.b1 + b.b3, t, b.b1, b.b1 + b.b6]]) j := rfl
private theorem four_mul_element (j : Fin 5) (v w : Fin 9 → ZMod 2) :
    smallEvenFourCoordinatesA512 j (smallEvenElementA512 (fourCarrierRow j) v *
      smallEvenElementA512 (fourCarrierRow j) w) =
    smallEvenFourCoordinatesA512 j (smallEvenElementA512 (fourCarrierRow j) v) *
      smallEvenFourCoordinatesA512 j (smallEvenElementA512 (fourCarrierRow j) w) := by
  change smallEvenFourCoordinatesA512 j (evenElement (v 8) _ * evenElement (w 8) _) = _
  rw [evenElement_mul]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, four_toAdd, four_toAdd, four_toAdd]
  funext k
  fin_cases j <;> fin_cases k
  all_goals simp only [smallEvenElementA512, fourCarrierRow,
    evenElement, Matrix.cons_val, Fin.reduceFinMk, Pi.add_apply, toAdd_ofAdd,
    highBit_twice]
  all_goals split_ifs with h
  all_goals have hv : v 8 = 0 ∨ v 8 = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) _
  all_goals simp_all only [false_or]
  all_goals simp only [Core.mul, evenCoreAction]
  all_goals ring_nf
  all_goals reduce_mod_char

private theorem three_mul_element (v w : Fin 9 → ZMod 2) :
    smallEvenThreeCoordinatesA512 (smallEvenElementA512 3 v * smallEvenElementA512 3 w) =
    smallEvenThreeCoordinatesA512 (smallEvenElementA512 3 v) *
      smallEvenThreeCoordinatesA512 (smallEvenElementA512 3 w) := by
  change smallEvenThreeCoordinatesA512 (evenElement (v 8) _ * evenElement (w 8) _) = _
  rw [evenElement_mul]
  apply Multiplicative.toAdd.injective
  funext k
  fin_cases k
  all_goals simp only [smallEvenThreeCoordinatesA512, smallEvenElementA512,
    evenElement, Matrix.cons_val, Fin.reduceFinMk, toAdd_mul, Pi.add_apply, toAdd_ofAdd,
    highBit_twice]
  all_goals split_ifs with h
  all_goals have hv : v 8 = 0 ∨ v 8 = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) _
  all_goals simp_all only [false_or]
  all_goals simp only [Core.mul, evenCoreAction]
  all_goals ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals ring_nf

/-- Five core generators per rank-four row; candidate 4 has six. -/
private def kernelCore (i : Fin 6) : Fin 6 → Core :=
  (![![⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩],
    ![⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩],
    ![⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩],
    ![⟨0, 0, 1, 1, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩],
    ![⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩],
    ![⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩]]) i

/-- Inner lists are words in the nine original generators; each word is squared. -/
private def squareWords (i : Fin 6) : Fin 6 → List (List (Fin 9)) :=
  (![![[[5, 1]], [[0], [5, 1]], [[3, 5]], [[0, 1]], [[0, 2, 5]], []],
    ![[[1, 4]], [[1, 2, 5]], [[1, 1]], [[0, 1]], [[0, 1, 3]], []],
    ![[[5, 1]], [[1], [1, 2, 7]], [[3, 5]], [[0, 1, 3]], [[0, 5]], []],
    ![[[1], [0, 1, 2]], [[1, 4, 0]], [[0, 4, 2]], [[2, 5]], [[0], [0, 4, 2]], [[0, 2]]],
    ![[[0, 1]], [[1], [1, 2, 5]], [[2, 5]], [[0]], [[1, 1]], []],
    ![[[2], [1, 2]], [[0, 2, 6]], [[0], [1, 3, 4]], [[0]], [[3, 4]], []]]) i

private def word {I : Type*} (g : I → SylowModel) (w : List I) : SylowModel :=
  (w.map g).prod
private def kernelGenerator (i k : Fin 6) : SylowModel := evenElement 0 (kernelCore i k)
set_option Elab.async false in
private theorem squareWords_valid : ∀ (i k : Fin 6),
    word (fun w => (word (smallEvenGeneratorsA512 i) w) ^ 2) (squareWords i k) =
      kernelGenerator i k := by decide +kernel

/-- The binary normal-form exponents, including candidate 4's central correction. -/
private def kernelExponents (i : Fin 6) (x : SylowModel) : Fin 6 → ZMod 2 :=
  let b := x.left
  (![![b.b2, b.b5, b.b7, b.b8, b.b9, 0],
    ![b.b2, b.b5, b.b7, b.b8, b.b9, 0],
    ![b.b2, b.b6, b.b7, b.b8, b.b9, 0],
    ![b.b2, b.b4, b.b6, b.b7, b.b8, b.b9 + b.b2 * b.b4],
    ![b.b4, b.b6, b.b7, b.b8, b.b9, 0],
    ![b.b4, b.b5, b.b7, b.b8, b.b9, 0]]) i
private def kernelWord (i : Fin 6) (x : SylowModel) : SylowModel :=
  kernelGenerator i 0 ^ (kernelExponents i x 0).val *
    kernelGenerator i 1 ^ (kernelExponents i x 1).val *
    kernelGenerator i 2 ^ (kernelExponents i x 2).val *
    kernelGenerator i 3 ^ (kernelExponents i x 3).val *
    kernelGenerator i 4 ^ (kernelExponents i x 4).val *
    kernelGenerator i 5 ^ (kernelExponents i x 5).val
private theorem evenElement_pow_bit (t : ZMod 2) (b : Core) (z : ZMod 2) :
    evenElement t b ^ z.val = evenElement (if z = 0 then 0 else t)
      (if z = 0 then 1 else b) := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
  · exact pow_zero _
  · exact pow_one _
-- Check the 512 parameter values one row at a time.
set_option Elab.async false in
private theorem four_kernelWord_valid_0 : ∀ v : Fin 9 → ZMod 2,
    smallEvenFourCoordinatesA512 0 (smallEvenElementA512 0 v) = 1 →
      kernelWord 0 (smallEvenElementA512 0 v) = smallEvenElementA512 0 v := by
  intro v
  simp only [kernelWord, kernelGenerator, evenElement_pow_bit, evenElement_mul]
  revert v
  decide +kernel
set_option Elab.async false in
private theorem four_kernelWord_valid_1 : ∀ v : Fin 9 → ZMod 2,
    smallEvenFourCoordinatesA512 1 (smallEvenElementA512 1 v) = 1 →
      kernelWord 1 (smallEvenElementA512 1 v) = smallEvenElementA512 1 v := by
  intro v
  simp only [kernelWord, kernelGenerator, evenElement_pow_bit, evenElement_mul]
  revert v
  decide +kernel
set_option Elab.async false in
private theorem four_kernelWord_valid_2 : ∀ v : Fin 9 → ZMod 2,
    smallEvenFourCoordinatesA512 2 (smallEvenElementA512 2 v) = 1 →
      kernelWord 2 (smallEvenElementA512 2 v) = smallEvenElementA512 2 v := by
  intro v
  simp only [kernelWord, kernelGenerator, evenElement_pow_bit, evenElement_mul]
  revert v
  decide +kernel
set_option Elab.async false in
private theorem four_kernelWord_valid_3 : ∀ v : Fin 9 → ZMod 2,
    smallEvenFourCoordinatesA512 3 (smallEvenElementA512 4 v) = 1 →
      kernelWord 4 (smallEvenElementA512 4 v) = smallEvenElementA512 4 v := by
  intro v
  simp only [kernelWord, kernelGenerator, evenElement_pow_bit, evenElement_mul]
  revert v
  decide +kernel
set_option Elab.async false in
private theorem four_kernelWord_valid_4 : ∀ v : Fin 9 → ZMod 2,
    smallEvenFourCoordinatesA512 4 (smallEvenElementA512 5 v) = 1 →
      kernelWord 5 (smallEvenElementA512 5 v) = smallEvenElementA512 5 v := by
  intro v
  simp only [kernelWord, kernelGenerator, evenElement_pow_bit, evenElement_mul]
  revert v
  decide +kernel
set_option Elab.async false in
private theorem three_kernelWord_valid : ∀ v : Fin 9 → ZMod 2,
    smallEvenThreeCoordinatesA512 (smallEvenElementA512 3 v) = 1 →
      kernelWord 3 (smallEvenElementA512 3 v) = smallEvenElementA512 3 v := by
  intro v
  simp only [kernelWord, kernelGenerator, evenElement_pow_bit, evenElement_mul]
  revert v
  decide +kernel

private theorem four_index (j : Fin 5) :
    fourIndex (smallEvenFourRowA512 j) = smallEvenIndexA512 (fourCarrierRow j) := by
  fin_cases j <;> rfl

/-- The fixed rank-four coordinates preserve multiplication on the original candidate. -/
public theorem smallEvenFourMapA512_mul (j : Fin 5)
    (x y : smallEvenCandidate (fourIndex (smallEvenFourRowA512 j))) :
    smallEvenFourMapA512 j (x * y) = smallEvenFourMapA512 j x * smallEvenFourMapA512 j y := by
  have hx : smallEvenCarrierA512 (fourCarrierRow j) x.val :=
    (smallEvenCandidate_mem_iff_carrierA512 _ _).mp (four_index j ▸ x.property)
  have hy : smallEvenCarrierA512 (fourCarrierRow j) y.val :=
    (smallEvenCandidate_mem_iff_carrierA512 _ _).mp (four_index j ▸ y.property)
  change smallEvenFourCoordinatesA512 j (x.val * y.val) =
    smallEvenFourCoordinatesA512 j x.val * smallEvenFourCoordinatesA512 j y.val
  rw [← smallEvenElementA512_parameters _ x.val hx, ← smallEvenElementA512_parameters _ y.val hy]
  exact four_mul_element j _ _

/-- The fixed rank-three coordinates preserve multiplication on candidate 4. -/
public theorem smallEvenThreeMapA512_mul (x y : smallEvenCandidate 4) :
    smallEvenThreeMapA512 (x * y) = smallEvenThreeMapA512 x * smallEvenThreeMapA512 y := by
  have hx := (smallEvenCandidate_mem_iff_carrierA512 3 x.val).mp x.property
  have hy := (smallEvenCandidate_mem_iff_carrierA512 3 y.val).mp y.property
  change smallEvenThreeCoordinatesA512 (x.val * y.val) =
    smallEvenThreeCoordinatesA512 x.val * smallEvenThreeCoordinatesA512 y.val
  rw [← smallEvenElementA512_parameters _ x.val hx, ← smallEvenElementA512_parameters _ y.val hy]
  exact three_mul_element _ _

private theorem word_mem {I : Type*} (D : Subgroup SylowModel)
    (g : I → SylowModel) (hg : ∀ j, g j ∈ D) (w : List I) : word g w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons j w ih => exact D.mul_mem (hg j) ih

private theorem kernelGenerator_mem (i : Fin 6) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallEvenCandidate (smallEvenIndexA512 i), x ^ 2 ∈ D)
    (k : Fin 6) : kernelGenerator i k ∈ D := by
  rw [← squareWords_valid i k]
  apply word_mem
  intro w
  apply hsq
  exact word_mem _ _ (smallEvenGeneratorsA512_mem i) w

private theorem kernelWord_mem (i : Fin 6) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallEvenCandidate (smallEvenIndexA512 i), x ^ 2 ∈ D)
    (x : SylowModel) : kernelWord i x ∈ D := by
  unfold kernelWord
  repeat apply Subgroup.mul_mem
  all_goals exact D.pow_mem (kernelGenerator_mem i D hsq _) _

private theorem four_kernelWord_valid (j : Fin 5) (v : Fin 9 → ZMod 2)
    (hv : smallEvenFourCoordinatesA512 j (smallEvenElementA512 (fourCarrierRow j) v) = 1) :
    kernelWord (fourCarrierRow j) (smallEvenElementA512 (fourCarrierRow j) v) =
      smallEvenElementA512 (fourCarrierRow j) v := by
  fin_cases j
  · exact four_kernelWord_valid_0 v hv
  · exact four_kernelWord_valid_1 v hv
  · exact four_kernelWord_valid_2 v hv
  · exact four_kernelWord_valid_3 v hv
  · exact four_kernelWord_valid_4 v hv

private theorem four_mem_of_squares (j : Fin 5) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallEvenCandidate (fourIndex (smallEvenFourRowA512 j)), x ^ 2 ∈ D)
    (x : smallEvenCandidate (fourIndex (smallEvenFourRowA512 j)))
    (hx : smallEvenFourMapA512 j x = 1) : x.val ∈ D := by
  have hc := (smallEvenCandidate_mem_iff_carrierA512 (fourCarrierRow j) x.val).mp
    (four_index j ▸ x.property)
  have he := smallEvenElementA512_parameters _ x.val hc
  have hz : smallEvenFourCoordinatesA512 j
      (smallEvenElementA512 (fourCarrierRow j) (smallEvenParametersA512 (fourCarrierRow j) x.val)) = 1 := by
    rw [he]
    exact hx
  have hw := four_kernelWord_valid j _ hz
  rw [he] at hw
  rw [← hw]
  exact kernelWord_mem _ D (four_index j ▸ hsq) _

private theorem three_mem_of_squares (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallEvenCandidate 4, x ^ 2 ∈ D)
    (x : smallEvenCandidate 4) (hx : smallEvenThreeMapA512 x = 1) : x.val ∈ D := by
  have hc := (smallEvenCandidate_mem_iff_carrierA512 3 x.val).mp x.property
  have he := smallEvenElementA512_parameters _ x.val hc
  have hz : smallEvenThreeCoordinatesA512
      (smallEvenElementA512 3 (smallEvenParametersA512 3 x.val)) = 1 := by
    rw [he]
    exact hx
  have hw := three_kernelWord_valid _ hz
  rw [he] at hw
  rw [← hw]
  exact kernelWord_mem 3 D hsq _

/-- The identity fiber of each fixed rank-four map is exactly the Frattini subgroup. -/
public theorem smallEvenFourMapA512_eq_one_iff_mem_frattini (j : Fin 5)
    (x : smallEvenCandidate (fourIndex (smallEvenFourRowA512 j))) :
    smallEvenFourMapA512 j x = 1 ↔
      x ∈ frattini (smallEvenCandidate (fourIndex (smallEvenFourRowA512 j))) := by
  let U := smallEvenCandidate (fourIndex (smallEvenFourRowA512 j))
  let π : U →* FourQuotient := MonoidHom.mk' (smallEvenFourMapA512 j) (smallEvenFourMapA512_mul j)
  have hU : IsPGroup 2 U := (IsPGroup.of_card (n := 12) card).to_subgroup U
  have hphi := hU.frattini_eq_closure_squares
  constructor
  · intro hx
    let D := (frattini U).map U.subtype
    have hsq (y : SylowModel) (hy : y ∈ U) : y ^ 2 ∈ D := by
      refine ⟨(⟨y, hy⟩ : U) ^ 2, ?_, rfl⟩
      rw [hphi]
      exact Subgroup.subset_closure ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := four_mem_of_squares j D hsq x hx
    exact (show y = x from Subtype.ext he) ▸ hy
  · intro hx
    have hle : frattini U ≤ π.ker := by
      rw [hphi]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨y, rfl⟩
      change π (y ^ 2) = 1
      rw [map_pow]
      exact (by decide +kernel : ∀ v : FourQuotient, v ^ 2 = 1) _
    exact hle hx

/-- The identity fiber of candidate 4's fixed rank-three map is its Frattini subgroup. -/
public theorem smallEvenThreeMapA512_eq_one_iff_mem_frattini (x : smallEvenCandidate 4) :
    smallEvenThreeMapA512 x = 1 ↔ x ∈ frattini (smallEvenCandidate 4) := by
  let U := smallEvenCandidate 4
  let π : U →* ThreeQuotient := MonoidHom.mk' smallEvenThreeMapA512 smallEvenThreeMapA512_mul
  have hU : IsPGroup 2 U := (IsPGroup.of_card (n := 12) card).to_subgroup U
  have hphi := hU.frattini_eq_closure_squares
  constructor
  · intro hx
    let D := (frattini U).map U.subtype
    have hsq (y : SylowModel) (hy : y ∈ U) : y ^ 2 ∈ D := by
      refine ⟨(⟨y, hy⟩ : U) ^ 2, ?_, rfl⟩
      rw [hphi]
      exact Subgroup.subset_closure ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := three_mem_of_squares D hsq x hx
    exact (show y = x from Subtype.ext he) ▸ hy
  · intro hx
    have hle : frattini U ≤ π.ker := by
      rw [hphi]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨y, rfl⟩
      change π (y ^ 2) = 1
      rw [map_pow]
      exact (by decide +kernel : ∀ v : ThreeQuotient, v ^ 2 = 1) _
    exact hle hx

end ReeTwo.SylowModel
