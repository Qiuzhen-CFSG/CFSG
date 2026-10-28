module

public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeLargeField
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Natural special-linear cohomology in dimensions three, four and five

For a finite characteristic-two field K, the natural SL₃(K) first cohomology
has F₂-dimension one when |K| = 2 and zero otherwise. The binary calculation
uses an explicit nonprincipal cocycle and a normal form for every cocycle;
the larger-field calculation forces every elementary value to have row
support. These calculations are re-exported here, and scalar restriction
gives the prime-field dimension used in the source.

For any field, a fourth index provides a commuting elementary transvection
which kills each off-row coordinate of a cocycle value. The three-index
relation then identifies all its remaining coefficients with a single vector,
so the cocycle is principal.

Consequently H¹ vanishes for the natural SL₄(2) and SL₅(2) modules. Their
canonical projective identifications establish the same result for L₄(2) and
L₅(2), with the actual natural action retained.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma
I.1.6(4),(6), printed p.408 (PDF p.419), citing Jones--Parshall [JP76]. The
elementary-matrix proof here works over every field in dimension at least four.
-/

open Matrix Matrix.SpecialLinearGroup

namespace Representation.OneCohomology.SLHigherNatural

variable {K : Type*} [Field K] {d : ℕ}

section DimensionThree

variable [Finite K] [CharP K 2]

/-- The defining-field dimension of natural SL₃ cohomology, including the binary exception. -/
public theorem finrank_H1_sl3 :
    Module.finrank K (H1 (specialLinearNatural (k := K) 3)) =
      if Nat.card K = 2 then 1 else 0 := by
  split_ifs with hK
  · exact finrank_H1_sl3_card_two hK
  · let := Fintype.ofFinite K
    have hcard : 1 < Nat.card K := by
      simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := K))
    exact finrank_H1_sl3_large_field (by omega)

variable [Algebra (ZMod 2) K]

/-- Over a two-element field, scalar restriction preserves the exceptional dimension one. -/
public theorem finrank_restrict_sl3_card_two (hK : Nat.card K = 2) :
    Module.finrank (ZMod 2)
      (H1 (restrictScalars (k := ZMod 2) (specialLinearNatural (k := K) 3))) = 1 := by
  rw [finrank_restrictScalars, finrank_H1_sl3_card_two hK,
    coefficient_finrank_of_card 2 1 (by simpa using hK), mul_one]

omit [CharP K 2] in
/-- Vanishing over the defining field also gives vanishing over its binary prime field. -/
public theorem finrank_restrict_sl3_large_field (hK : 2 < Nat.card K) :
    Module.finrank (ZMod 2)
      (H1 (restrictScalars (k := ZMod 2) (specialLinearNatural (k := K) 3))) = 0 := by
  rw [finrank_restrictScalars, finrank_H1_sl3_large_field hK, mul_zero]

/-- The prime-field dimension of natural SL₃ cohomology in characteristic two. -/
public theorem finrank_restrict_sl3 :
    Module.finrank (ZMod 2)
      (H1 (restrictScalars (k := ZMod 2) (specialLinearNatural (k := K) 3))) =
        if Nat.card K = 2 then 1 else 0 := by
  by_cases hK : Nat.card K = 2
  · simpa only [if_pos hK] using finrank_restrict_sl3_card_two hK
  · rw [finrank_restrictScalars, finrank_H1_sl3, if_neg hK, mul_zero]

/-- Aschbacher--Smith I.1.6(4): for |K| = 2^n the prime-field dimension is
one for n = 1 and zero for n > 1. -/
public theorem finrank_restrict_sl3_of_card_pow (n : ℕ) (hK : Nat.card K = 2 ^ n) :
    Module.finrank (ZMod 2)
      (H1 (restrictScalars (k := ZMod 2) (specialLinearNatural (k := K) 3))) =
        if n = 1 then 1 else 0 := by
  rw [finrank_restrict_sl3, hK]
  have h : 2 ^ n = 2 ↔ n = 1 := by
    constructor
    · intro hn
      exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hn)
    · rintro rfl
      rfl
  simp only [h]

end DimensionThree

private lemma exists_outside_three (hd : 4 ≤ d) (i j l : Fin d) :
    ∃ k : Fin d, k ≠ i ∧ k ≠ j ∧ k ≠ l := by
  have hcard : ({i, j, l} : Finset (Fin d)).card < (Finset.univ : Finset (Fin d)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have : ({i, j, l} : Finset (Fin d)).card ≤ 3 := by
      exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
        (le_trans (Finset.card_insert_le _ _) (by simp)) _)
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨k, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk⟩

/-- In dimension at least four, every elementary cocycle value is supported in its row. -/
public lemma cocycle_transvection_support (hd : 4 ≤ d)
    (f : cocycles (specialLinearNatural (k := K) d))
    {i j : Fin d} (hij : i ≠ j) (a : K) :
    f.val (transvection hij a) = Pi.single i (f.val (transvection hij a) i) := by
  ext l
  by_cases hli : l = i
  · simp [hli]
  · obtain ⟨k, hki, hkj, hkl⟩ := exists_outside_three hd i j l
    simpa [Pi.single_eq_of_ne hli] using
      cocycle_off_diagonal f hij hkl hkj.symm hli hki a

/-- Every natural-module cocycle is principal in dimension at least four. -/
public lemma exists_principal_of_four_le (hd : 4 ≤ d)
    (f : cocycles (specialLinearNatural (k := K) d)) :
    ∃ v : Fin d → K, f = principal (specialLinearNatural (k := K) d) v :=
  exists_principal_of_support (by omega) f (fun _ _ hij a => cocycle_transvection_support hd f hij a)

/-- Natural special-linear first cohomology vanishes in dimension at least four. -/
public lemma H1_subsingleton_of_four_le (hd : 4 ≤ d) :
    Subsingleton (H1 (specialLinearNatural (k := K) d)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  obtain ⟨v, hv⟩ := exists_principal_of_four_le hd f
  exact ⟨v, hv.symm⟩

/-- The dimension of natural special-linear first cohomology is zero in dimension at least four. -/
public lemma finrank_H1_of_four_le (hd : 4 ≤ d) :
    Module.finrank K (H1 (specialLinearNatural (k := K) d)) = 0 := by
  let := H1_subsingleton_of_four_le (K := K) hd
  exact Module.finrank_zero_of_subsingleton

/-- The same vanishing holds for the actual projective natural action over F₂. -/
public lemma finrank_H1_binaryProjective_of_four_le (hd : 4 ≤ d) :
    Module.finrank (ZMod 2) (H1 (binaryProjectiveNatural d)) = 0 := by
  have e := H1Congr (specialLinearNatural (k := ZMod 2) d) (binaryProjectiveNatural d)
    (binaryProjectiveEquiv d) (LinearEquiv.refl (ZMod 2) (Fin d → ZMod 2))
    (fun g v => (binaryProjectiveNatural_apply d g v).symm)
  rw [← e.finrank_eq]
  exact finrank_H1_of_four_le (K := ZMod 2) (d := d) hd

/-- Aschbacher--Smith I.1.6(6), in the determinant-one matrix model of L₄(2). -/
public theorem finrank_H1_sl4_two :
    Module.finrank (ZMod 2) (H1 (specialLinearNatural (k := ZMod 2) 4)) = 0 :=
  finrank_H1_of_four_le (K := ZMod 2) (d := 4) (by decide)

/-- Aschbacher--Smith I.1.6(6), in the determinant-one matrix model of L₅(2). -/
public theorem finrank_H1_sl5_two :
    Module.finrank (ZMod 2) (H1 (specialLinearNatural (k := ZMod 2) 5)) = 0 :=
  finrank_H1_of_four_le (K := ZMod 2) (d := 5) (by decide)

/-- Aschbacher--Smith I.1.6(6) for the canonical natural L₄(2) action. -/
public theorem finrank_H1_psl4_two :
    Module.finrank (ZMod 2) (H1 (binaryProjectiveNatural 4)) = 0 :=
  finrank_H1_binaryProjective_of_four_le (d := 4) (by decide)

/-- Aschbacher--Smith I.1.6(6) for the canonical natural L₅(2) action. -/
public theorem finrank_H1_psl5_two :
    Module.finrank (ZMod 2) (H1 (binaryProjectiveNatural 5)) = 0 :=
  finrank_H1_binaryProjective_of_four_le (d := 5) (by decide)

end Representation.OneCohomology.SLHigherNatural
