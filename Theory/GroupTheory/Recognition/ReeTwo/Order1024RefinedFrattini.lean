module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCoordinates
public import Theory.Frattini.BinarySquares
/-!
# Frattini kernels of the four refined Ree two coordinate maps

For residual indices 1, 5, 7, and 13, the fixed binary rank-three map has
Frattini kernel. The Frattini subgroup of a finite two-group is generated
by squares, so it lies in the kernel. For the reverse inclusion, short
products of squares give each of the six tail roots. Modulo the tail,
every kernel element is either the identity or the image of the square
`(refinedGenerators c 2 * refinedGenerators c 3) ^ 2`.

The square-word table uses the four candidate generators as letters 0–3
and the six tail roots as letters 4–9. Every table identity and the small
tail-quotient check are verified by Lean's kernel; no enumeration of the
full candidate subgroup is needed in the proof.

Source: Shinoda (1975), (2.3), pp. 81–82, using the checked multiplication
and action in `ReeTwo.Core` and `ReeTwo.RootAction`, and the fixed maps in
`Order1024RefinedCoordinates`.
-/

namespace ReeTwo.SylowModel
open TailQuotient

private def frattiniSeed (c : Fin 4) (i : Fin 10) : SylowModel :=
  if h : i.val < 4 then refinedGenerators c ⟨i.val, h⟩ else root i

private theorem frattiniSeed_mem (c : Fin 4) (i : Fin 10) :
    frattiniSeed c i ∈ residualCandidate (refinedIndex c) := by
  unfold frattiniSeed
  split
  · exact refinedGenerators_mem c _
  · apply tailSubgroup_le_residualCandidate
    exact Subgroup.subset_closure ⟨i, show 4 ≤ i.val from by omega, rfl⟩

private def frattiniWord {I : Type*} (g : I → SylowModel) (w : List I) : SylowModel :=
  (w.map g).prod

private theorem frattini_word_mem {I : Type*} (H : Subgroup SylowModel)
    (g : I → SylowModel) (hg : ∀ i, g i ∈ H) (w : List I) :
    frattiniWord g w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (hg i) ih

private def frattiniExtra (c : Fin 4) : SylowModel :=
  (refinedGenerators c 2 * refinedGenerators c 3) ^ 2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem frattini_quotient_kernel : ∀ c q,
    refinedTailMember c q → refinedCoordinates c q = 1 →
    q = 1 ∨ q = projection (frattiniExtra c) := by
  intro c q hm hk
  have h : coordinateCode q = coordinateCode 1 ∨
      coordinateCode q = coordinateCode (projection (frattiniExtra c)) :=
    (by decide +kernel : ∀ c q, refinedTailMember c q → refinedCoordinates c q = 1 →
      coordinateCode q = coordinateCode 1 ∨
      coordinateCode q = coordinateCode (projection (frattiniExtra c))) c q hm hk
  exact h.imp (fun he => coordinateCode_injective he)
    (fun he => coordinateCode_injective he)
/-- Each inner word is squared; the outer list is multiplied in order. -/
private def frattiniTailWords (c : Fin 4) (i : Fin 6) : List (List (Fin 10)) :=
  (![![[[2,3],[1,3]], [[2]], [[1,2],[2,7]], [[0,1],[0,6]], [[0]], [[1]]],
     ![[[1,3],[1]], [[0,2]], [[0,1],[1,2]], [[0,2],[4,1]], [[3]], [[0,3]]],
     ![[[1,2],[1,3]], [[0,2]], [[0,1],[1,2]], [[0,2],[4,1]], [[3,6]], [[4,5]]],
     ![[[1,2],[2,7]], [[0],[1,2],[0,2]], [[0],[0,2],[2,4]],
       [[0,1],[0,6]], [[0]], [[1]]]] : Fin 4 → Fin 6 → List (List (Fin 10))) c i

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem frattiniTailWords_valid : ∀ (c : Fin 4) (i : Fin 6),
    frattiniWord
      (fun w => (frattiniWord (frattiniSeed c) w) ^ 2)
      (frattiniTailWords c i) = root ⟨i.val + 4, by omega⟩ := by decide +kernel

private theorem frattini_tail_le (c : Fin 4) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ residualCandidate (refinedIndex c), x ^ 2 ∈ D) : tailSubgroup ≤ D := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, hi, rfl⟩
  change 4 ≤ i.val at hi
  let j : Fin 6 := ⟨i.val - 4, by omega⟩
  have he : (⟨j.val + 4, by omega⟩ : CoreRoot) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [← he, ← frattiniTailWords_valid c j]
  apply frattini_word_mem
  intro w
  exact hsq _ (frattini_word_mem _ _ (frattiniSeed_mem c) w)

/-- The fixed three binary coordinates have precisely the Frattini kernel. -/
public theorem refinedProjection_ker_eq_frattini (c : Fin 4) :
    (refinedProjection c).ker = frattini (residualCandidate (refinedIndex c)) := by
  let U := residualCandidate (refinedIndex c)
  have hU : IsPGroup 2 U := (IsPGroup.of_card (n := 12) card).to_subgroup U
  have hphi := hU.frattini_eq_closure_squares
  apply le_antisymm
  · let D := (frattini U).map U.subtype
    have hsq (x : SylowModel) (hx : x ∈ U) : x ^ 2 ∈ D := by
      refine ⟨(⟨x, hx⟩ : U) ^ 2, ?_, rfl⟩
      rw [hphi]
      exact Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩
    have htail : tailSubgroup ≤ D := frattini_tail_le c D hsq
    have hextra : frattiniExtra c ∈ D :=
      hsq _ (U.mul_mem (refinedGenerators_mem c 2) (refinedGenerators_mem c 3))
    intro x hx
    have hxq : refinedCoordinates c (projection x.val) = 1 := hx
    have hxmem := (refinedCandidate_mem c x.val).mp x.property
    have hval : x.val ∈ D := by
      rcases frattini_quotient_kernel c (projection x.val) hxmem hxq with h | h
      · apply htail
        rw [← ker_projection]
        exact h
      · have ht : (frattiniExtra c)⁻¹ * x.val ∈ tailSubgroup := by
          rw [← ker_projection, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
        have hm := D.mul_mem hextra (htail ht)
        simpa only [mul_inv_cancel_left] using hm
    obtain ⟨y, hy, he⟩ := hval
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy
  · rw [hphi]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    change refinedProjection c (x ^ 2) = 1
    rw [map_pow]
    exact (by decide +kernel : ∀ v : RefinedQuotient, v ^ 2 = 1) _

end ReeTwo.SylowModel
