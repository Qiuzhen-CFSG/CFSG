module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourCoordinates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourGeneration
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourMultiplication
public import Theory.Frattini.BinarySquares

/-!
# Square certificates for the rank-four Ree two parity kernels

Short products of squares of the four basis lifts supply five generators for
rows 0–3, four for rows 4–5, and three for rows 6–7 (the remaining table entries
are identities). The carrier equations and the four vanishing quotient
coordinates give an ordered normal form in these generators. Thus every such
element lies in every subgroup containing the squares of the exact candidate.

Since all candidates are subgroups of the verified two-group of order 4096,
the square-closure theorem identifies this subgroup with the Frattini subgroup.
The independent generation and multiplication certificates identify the exact
candidate carriers and prove multiplicativity of the fixed coordinates,
discharging both premises of the square-kernel argument for all eight rows.

Source: Shinoda (1975), (2.3), pp. 81–82, as realized by the verified `Core`,
`RootAction`, and `Sylow` multiplication. The basis conventions are those of
`SmallParityFourCoordinates`. Each square-word identity is kernel checked.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 32768

private def squareWords (i : Fin 8) (j : Fin 5) : List (List (Fin 4)) :=
  (![![[[1]], [[0, 1], [1, 2, 2]], [[2, 3]], [[0]], [[0], [0, 2]]],
   ![[[1], [1, 2, 1]], [[1], [0, 1]], [[1, 2, 1]], [[0]], [[0, 1, 1]]],
   ![[[1]], [[1], [2, 1, 3]], [[0], [1, 1, 2]], [[0, 2]], [[0, 3]]],
   ![[[1]], [[1], [0, 2, 1]], [[2]], [[0, 2]], [[0, 3]]],
   ![[[1]], [], [[1], [0, 1, 2]], [[1, 1, 2]], [[0, 3]]],
   ![[[2, 1, 3]], [], [[1], [1, 2, 3]], [[1, 1]], [[0, 3]]],
   ![[[1]], [[1], [0, 1, 2]], [], [[0]], []],
   ![[[1]], [], [], [[1, 1]], [[0, 2]]]] : Fin 8 → Fin 5 → List (List (Fin 4))) i j

private def word {I : Type*} (g : I → SylowModel) (w : List I) : SylowModel :=
  (w.map g).prod

private def kernelGenerator (i : Fin 8) : Fin 5 → SylowModel :=
  (![![rootOne ^ 2, root 4, root 7, root 8, root 9],
      ![root 6 * rootOne ^ 2, root 4, root 7, root 8, root 9],
      ![rootOne ^ 2, root 6, root 7, root 8, root 9],
      ![rootOne ^ 2, root 4 * root 6, root 7, root 8, root 9],
      ![rootOne ^ 2, 1, root 7, root 8, root 9],
      ![root 6 * rootOne ^ 2, 1, root 7, root 8, root 9],
      ![rootOne ^ 2, root 4, 1, root 8, 1],
      ![root 6 * root 7 * rootOne ^ 2, 1, 1, root 8, root 9]]) i

set_option maxHeartbeats 8000000 in
private theorem squareWords_valid : ∀ (i : Fin 8) (j : Fin 5),
    word (fun w => (word (smallParityFourBasis i) w) ^ 2) (squareWords i j) =
      kernelGenerator i j := by decide +kernel

private def kernelWord (i : Fin 8) (x : SylowModel) : SylowModel :=
  kernelGenerator i 1 ^ (if i = 2 then x.left.b6 else x.left.b4).val *
    kernelGenerator i 2 ^ x.left.b7.val * kernelGenerator i 3 ^ x.left.b8.val *
    kernelGenerator i 4 ^ x.left.b9.val *
    kernelGenerator i 0 ^ (x.right.toAdd.val / 2)

set_option maxHeartbeats 8000000 in
private theorem kernelWord_valid (i : Fin 8) (x : SylowModel)
    (hx : smallParityFourCarrier i x) (hzero : smallParityFourCoordinates i x = 1) :
    kernelWord i x = x := by
  rcases x with ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩, t⟩
  rcases hx with ⟨rfl, rfl, hx⟩
  have hz0 := congrArg (fun v : SmallParityFourQuotient => v.toAdd 0) hzero
  have hz1 := congrArg (fun v : SmallParityFourQuotient => v.toAdd 1) hzero
  have hz2 := congrArg (fun v : SmallParityFourQuotient => v.toAdd 2) hzero
  have hz3 := congrArg (fun v : SmallParityFourQuotient => v.toAdd 3) hzero
  clear hzero
  fin_cases i <;> fin_cases t
  all_goals dsimp [smallParityFourCoordinates] at hz0 hz1 hz2 hz3
  all_goals norm_num [toAdd_ofAdd, ZMod.cast, ZMod.val] at hx hz0 hz1 hz2 hz3
  all_goals try exact absurd hz1 (by decide +kernel)
  all_goals simp_all only [zero_add, add_zero, add_eq_zero_iff_eq_neg]
  all_goals subst_vars
  all_goals try revert b2
  all_goals try revert b3
  all_goals try revert b4
  all_goals try revert b5
  all_goals try revert b6
  all_goals try revert b7
  all_goals try revert b8
  all_goals try revert b9
  all_goals decide +kernel

private theorem word_mem {I : Type*} (D : Subgroup SylowModel)
    (g : I → SylowModel) (hg : ∀ j, g j ∈ D) (w : List I) : word g w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons j w ih => exact D.mul_mem (hg j) ih

private theorem kernelGenerator_mem (i : Fin 8) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallParityTwoCandidate (smallParityFourIndex i), x ^ 2 ∈ D)
    (j : Fin 5) : kernelGenerator i j ∈ D := by
  rw [← squareWords_valid i j]
  apply word_mem
  intro w
  apply hsq
  exact word_mem _ _ (smallParityFourBasis_mem i) w

private theorem kernelWord_mem (i : Fin 8) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallParityTwoCandidate (smallParityFourIndex i), x ^ 2 ∈ D)
    (x : SylowModel) : kernelWord i x ∈ D := by
  unfold kernelWord
  repeat apply Subgroup.mul_mem
  all_goals exact D.pow_mem (kernelGenerator_mem i D hsq _) _

/-- The carrier equations and vanishing coordinates force an element into every
subgroup containing the squares of the exact candidate. -/
public theorem smallParityFourCoordinates_mem_of_squares (i : Fin 8) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ smallParityTwoCandidate (smallParityFourIndex i), x ^ 2 ∈ D)
    (x : SylowModel) (hx : smallParityFourCarrier i x)
    (hzero : smallParityFourCoordinates i x = 1) : x ∈ D := by
  rw [← kernelWord_valid i x hx hzero]
  exact kernelWord_mem i D hsq x

/-- The square certificates identify the Frattini kernel once carrier
containment and multiplicativity of the fixed map are established. -/
public theorem smallParityFourMap_eq_one_iff_mem_frattini_of_carrier_of_mul (i : Fin 8)
    (hcarrier : ∀ x ∈ smallParityTwoCandidate (smallParityFourIndex i),
      smallParityFourCarrier i x)
    (hmul : ∀ x y : smallParityTwoCandidate (smallParityFourIndex i),
      smallParityFourMap i (x * y) = smallParityFourMap i x * smallParityFourMap i y)
    (x : smallParityTwoCandidate (smallParityFourIndex i)) :
    smallParityFourMap i x = 1 ↔
      x ∈ frattini (smallParityTwoCandidate (smallParityFourIndex i)) := by
  let U := smallParityTwoCandidate (smallParityFourIndex i)
  let π : U →* SmallParityFourQuotient := MonoidHom.mk' (smallParityFourMap i) hmul
  have hU : IsPGroup 2 U := (IsPGroup.of_card (n := 12) card).to_subgroup U
  have hphi := hU.frattini_eq_closure_squares
  constructor
  · intro hx
    let D := (frattini U).map U.subtype
    have hsq (y : SylowModel) (hy : y ∈ U) : y ^ 2 ∈ D := by
      refine ⟨(⟨y, hy⟩ : U) ^ 2, ?_, rfl⟩
      rw [hphi]
      exact Subgroup.subset_closure ⟨⟨y, hy⟩, rfl⟩
    have hval : x.val ∈ D := smallParityFourCoordinates_mem_of_squares i D hsq x.val
      (hcarrier x.val x.property) hx
    obtain ⟨y, hy, he⟩ := hval
    exact (show y = x from Subtype.ext he) ▸ hy
  · intro hx
    have hle : frattini U ≤ π.ker := by
      rw [hphi]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨y, rfl⟩
      change π (y ^ 2) = 1
      rw [map_pow]
      exact (by decide +kernel : ∀ v : SmallParityFourQuotient, v ^ 2 = 1) _
    exact hle hx

/-- The displayed generator closure has exactly the fixed carrier equations. -/
public theorem smallParityFour_mem_iff_carrier (i : Fin 8) (x : SylowModel) :
    x ∈ smallParityTwoCandidate (smallParityFourIndex i) ↔ smallParityFourCarrier i x := by
  rw [smallParityFourCandidate_eq_of_carrier i (smallParityFourCarrierSubgroup i)
    (mem_smallParityFourCarrierSubgroup i)]
  exact mem_smallParityFourCarrierSubgroup i x

/-- The fixed quotient coordinates preserve multiplication on the exact candidate. -/
public theorem smallParityFourMap_mul (i : Fin 8)
    (x y : smallParityTwoCandidate (smallParityFourIndex i)) :
    smallParityFourMap i (x * y) = smallParityFourMap i x * smallParityFourMap i y := by
  exact smallParityFourCoordinates_mul_of_carrier i x.val y.val
    ((smallParityFour_mem_iff_carrier i x.val).mp x.property)
    ((smallParityFour_mem_iff_carrier i y.val).mp y.property)

/-- The identity fiber of the fixed quotient map is the candidate's Frattini subgroup. -/
public theorem smallParityFourMap_eq_one_iff_mem_frattini (i : Fin 8)
    (x : smallParityTwoCandidate (smallParityFourIndex i)) :
    smallParityFourMap i x = 1 ↔
      x ∈ frattini (smallParityTwoCandidate (smallParityFourIndex i)) := by
  exact smallParityFourMap_eq_one_iff_mem_frattini_of_carrier_of_mul i
    (fun y hy => (smallParityFour_mem_iff_carrier i y).mp hy)
    (smallParityFourMap_mul i) x

end ReeTwo.SylowModel
