module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RankTwoCoordinates

/-!
# Frattini kernels of the three rank-two Ree two coordinate maps

The fixed coordinate kernels for residual indices 10, 11 and 14 are exactly
the Frattini subgroups of the original parity-kernel representatives. In each
finite two-group, squares generate the Frattini subgroup. Short products of
squares give all six tail roots. In the order-64 tail quotient, the coordinate
kernel consists of the four products of two distinguished squares. Removing
the corresponding square word from any kernel element leaves an element of
the tail, proving the reverse containment.

The square-word table uses the three ordered candidate generators as letters
0--2 and roots 4--9 as letters 3--8. Both this table and the four-element
quotient certificate are verified by Lean's kernel.

Source: Shinoda (1975), (2.3), pp. 81--82, with the verified multiplication
and action in `ReeTwo.Core` and `ReeTwo.RootAction`, and the coordinate maps
and original representatives in `Order1024RankTwoCoordinates`.
-/

namespace ReeTwo.SylowModel
open TailQuotient

private def rankTwoFrattiniSeed (c : Fin 3) (i : Fin 9) : SylowModel :=
  if h : i.val < 3 then rankTwoGenerators c ⟨i.val, h⟩
  else root ⟨i.val + 1, by omega⟩

private theorem rankTwoFrattiniSeed_mem (c : Fin 3) (i : Fin 9) :
    rankTwoFrattiniSeed c i ∈ residualCandidate (rankTwoIndex c) := by
  unfold rankTwoFrattiniSeed
  split
  · exact rankTwoGenerators_mem c _
  · apply tailSubgroup_le_residualCandidate
    exact Subgroup.subset_closure ⟨⟨i.val + 1, by omega⟩,
      show 4 ≤ i.val + 1 from by omega, rfl⟩

private def rankTwoFrattiniWord {I : Type*} (g : I → SylowModel)
    (w : List I) : SylowModel := (w.map g).prod

private theorem rankTwoFrattiniWord_mem {I : Type*} (D : Subgroup SylowModel)
    (g : I → SylowModel) (hg : ∀ i, g i ∈ D) (w : List I) :
    rankTwoFrattiniWord g w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons i w ih => exact D.mul_mem (hg i) ih

/-- Each inner word is squared, then the squares are multiplied in order. -/
private def rankTwoFrattiniTailWords (c : Fin 3) (i : Fin 6) : List (List (Fin 9)) :=
  (![![[[1,0],[2,2]], [[0,2],[6,2]], [[1],[4,2],[0,2]],
        [[0,3],[3,4]], [[0],[0,3]], [[3,4]]],
     ![[[1],[0,2],[2,0]], [[2],[0,2]], [[1],[2,0],[2,7]],
        [[0,3],[3,4]], [[0],[0,3]], [[3,4]]],
     ![[[1],[2,4],[2,6]], [[1]], [[0,1],[3,1]],
        [[0,3],[3,4]], [[0],[0,3]], [[3,4]]]] :
      Fin 3 → Fin 6 → List (List (Fin 9))) c i

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem rankTwoFrattiniTailWords_valid : ∀ (c : Fin 3) (i : Fin 6),
    rankTwoFrattiniWord
      (fun w => (rankTwoFrattiniWord (rankTwoFrattiniSeed c) w) ^ 2)
      (rankTwoFrattiniTailWords c i) = root ⟨i.val + 4, by omega⟩ := by
  decide +kernel

private theorem rankTwoFrattini_tail_le (c : Fin 3) (D : Subgroup SylowModel)
    (hsq : ∀ x ∈ residualCandidate (rankTwoIndex c), x ^ 2 ∈ D) :
    tailSubgroup ≤ D := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, hi, rfl⟩
  change 4 ≤ i.val at hi
  let j : Fin 6 := ⟨i.val - 4, by omega⟩
  have he : (⟨j.val + 4, by omega⟩ : CoreRoot) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [← he, ← rankTwoFrattiniTailWords_valid c j]
  apply rankTwoFrattiniWord_mem
  intro w
  exact hsq _ (rankTwoFrattiniWord_mem _ _ (rankTwoFrattiniSeed_mem c) w)

private def rankTwoFrattiniExtra (c : Fin 3) (j : Fin 2) : SylowModel :=
  ![rankTwoGenerators c 2 ^ 2,
    (rankTwoGenerators c 1 * rankTwoGenerators c 2) ^ 2] j

private def rankTwoFrattiniBlock (c : Fin 3) (p : Fin 2 × Fin 2) : SylowModel :=
  rankTwoFrattiniExtra c 0 ^ p.1.val * rankTwoFrattiniExtra c 1 ^ p.2.val

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem rankTwoFrattini_quotient_kernel (c : Fin 3) (q : TailQuotient.Group)
    (hm : rankTwoTailMember c q) (hk : rankTwoCoordinates q = 1) :
    ∃ p : Fin 2 × Fin 2, q = projection (rankTwoFrattiniBlock c p) := by
  obtain ⟨p, hp⟩ := (by decide +kernel : ∀ c q,
    rankTwoTailMember c q → rankTwoCoordinates q = 1 →
    ∃ p : Fin 2 × Fin 2,
      coordinateCode q = coordinateCode (projection (rankTwoFrattiniBlock c p))) c q hm hk
  exact ⟨p, coordinateCode_injective hp⟩

/-- The prescribed binary rank-two maps realize the Frattini quotients of the
original three residual candidates. -/
public theorem rankTwoProjection_ker_eq_frattini (c : Fin 3) :
    (rankTwoProjection c).ker = frattini (residualCandidate (rankTwoIndex c)) := by
  apply le_antisymm
  · let U := residualCandidate (rankTwoIndex c)
    let D := (frattini U).map U.subtype
    have hphi := ((IsPGroup.of_card (n := 12) card).to_subgroup U).frattini_eq_closure_squares
    have hsq (x : SylowModel) (hx : x ∈ U) : x ^ 2 ∈ D := by
      refine ⟨(⟨x, hx⟩ : U) ^ 2, ?_, rfl⟩
      rw [hphi]
      exact Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩
    have htail : tailSubgroup ≤ D := rankTwoFrattini_tail_le c D hsq
    have hextra (j : Fin 2) : rankTwoFrattiniExtra c j ∈ D := by
      fin_cases j
      · exact hsq _ (rankTwoGenerators_mem c 2)
      · exact hsq _ (U.mul_mem (rankTwoGenerators_mem c 1) (rankTwoGenerators_mem c 2))
    have hblock (p : Fin 2 × Fin 2) : rankTwoFrattiniBlock c p ∈ D :=
      D.mul_mem (D.pow_mem (hextra 0) _) (D.pow_mem (hextra 1) _)
    intro x hx
    have hxq : rankTwoCoordinates (projection x.val) = 1 := hx
    obtain ⟨p, hp⟩ := rankTwoFrattini_quotient_kernel c (projection x.val)
      ((rankTwoCandidate_mem c x.val).mp x.property) hxq
    have ht : (rankTwoFrattiniBlock c p)⁻¹ * x.val ∈ tailSubgroup := by
      rw [← ker_projection, MonoidHom.mem_ker, map_mul, map_inv, hp, inv_mul_cancel]
    have hval : x.val ∈ D := by
      simpa only [mul_inv_cancel_left] using D.mul_mem (hblock p) (htail ht)
    obtain ⟨y, hy, he⟩ := hval
    exact (Subtype.ext he : y = x) ▸ hy
  · exact frattini_le_rankTwoProjection_ker c

end ReeTwo.SylowModel
