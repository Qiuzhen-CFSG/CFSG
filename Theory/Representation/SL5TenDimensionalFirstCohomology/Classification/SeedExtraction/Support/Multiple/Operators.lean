module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.LocalData
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Coefficient extraction for binary SL₅ local highest vectors

The upper-transvection difference kills a local highest vector. At an active
root it sends the corresponding exchange translate back to the original vector;
at every other simple root it kills that translate. These identities prove
independence of the highest vector and all its active simple-exchange translates.

For two separated active roots the difference operators commute with the other
exchange. Applying the two operators successively extracts the coefficients of
the four exchange translates, proving a four-dimensional lower bound. These are
initial dimension estimates, not the eleven-dimensional multiple-support bound.
No weight-space separation or irreducibility assumption is used here.

The intended application is the highest-vector route to Aschbacher--Smith,
*The Classification of Quasithin Groups*, I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification

private theorem upper_mul_swap (i : Fin 4) :
    simpleUpper i * simpleSwap i = simpleLower i * simpleUpper i := by
  revert i
  decide

private theorem upper_swap_commute (i j : Fin 4)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    simpleUpper i * simpleSwap j = simpleSwap j * simpleUpper i := by
  revert i j
  decide

private def exchangedIndex (j : Fin 4) : Equiv.Perm (Fin 5) :=
  Equiv.swap j.castSucc j.succ

private theorem exchangedIndex_lt (i j : Fin 4) (hij : i ≠ j) :
    exchangedIndex j i.castSucc < exchangedIndex j i.succ := by
  revert i j
  decide

private theorem upper_mul_other_swap (i j : Fin 4) (hij : i ≠ j) :
    simpleUpper i * simpleSwap j = simpleSwap j *
      Matrix.SpecialLinearGroup.transvection (ne_of_lt (exchangedIndex_lt i j hij))
        (1 : ZMod 2) := by
  revert i j
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_add_self (x : V) : x + x = 0 := by
  have hh : (1 : ZMod 2) + 1 = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) hh

/-- The difference between an upper simple transvection and the identity. -/
def upperDifference (ρ : Representation (ZMod 2) Group V) (i : Fin 4) : V →ₗ[ZMod 2] V :=
  ρ (simpleUpper i) - LinearMap.id

/-- Every upper simple-root difference kills the highest vector. -/
theorem LocalHighestVector.upperDifference_self
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (i : Fin 4) : upperDifference ρ i v = 0 := by
  have hu := h.upper_fixed i.castSucc i.succ (by simp)
  change ρ (simpleUpper i) v = v at hu
  change ρ (simpleUpper i) v - v = 0
  rw [hu, sub_self]

/-- At an active root, the difference recovers the highest vector from its exchange translate. -/
theorem LocalHighestVector.upperDifference_swap
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) {i : Fin 4} (hi : i ∈ J) :
    upperDifference ρ i (ρ (simpleSwap i) v) = v := by
  have hu := h.upper_fixed i.castSucc i.succ (by simp)
  change ρ (simpleUpper i) v = v at hu
  have ha := h.active_relation i hi
  have hl : ρ (simpleLower i) v = v + ρ (simpleSwap i) v := by
    have ht := congrArg (fun x => x + ρ (simpleLower i) v) ha
    simpa only [add_assoc, binary_add_self, add_zero, zero_add] using ht.symm
  have he : ρ (simpleUpper i) (ρ (simpleSwap i) v) = v + ρ (simpleSwap i) v := by
    calc
      _ = ρ (simpleUpper i * simpleSwap i) v := by rw [map_mul]; rfl
      _ = ρ (simpleLower i * simpleUpper i) v := by rw [upper_mul_swap]
      _ = ρ (simpleLower i) v := by
        rw [map_mul]
        change ρ (simpleLower i) (ρ (simpleUpper i) v) = _
        rw [hu]
      _ = _ := hl
  change ρ (simpleUpper i) (ρ (simpleSwap i) v) - ρ (simpleSwap i) v = v
  rw [he, add_sub_cancel_right]

/-- A different simple-root difference kills an exchange translate, even for adjacent roots. -/
theorem LocalHighestVector.upperDifference_other_swap
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) {i j : Fin 4} (hij : i ≠ j) :
    upperDifference ρ i (ρ (simpleSwap j) v) = 0 := by
  have ht := h.upper_fixed _ _ (exchangedIndex_lt i j hij)
  have he : ρ (simpleUpper i) (ρ (simpleSwap j) v) = ρ (simpleSwap j) v := by
    calc
      _ = ρ (simpleUpper i * simpleSwap j) v := by rw [map_mul]; rfl
      _ = ρ (simpleSwap j) v := by
        rw [upper_mul_other_swap i j hij, map_mul]
        change ρ (simpleSwap j) (ρ _ v) = _
        rw [ht]
  change ρ (simpleUpper i) (ρ (simpleSwap j) v) - ρ (simpleSwap j) v = 0
  rw [he, sub_self]

/-- Separated roots give commuting difference and exchange operators on the entire module. -/
theorem upperDifference_swap_commute
    (ρ : Representation (ZMod 2) Group V) (i j : Fin 4)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) (x : V) :
    upperDifference ρ i (ρ (simpleSwap j) x) =
      ρ (simpleSwap j) (upperDifference ρ i x) := by
  change ρ (simpleUpper i) (ρ (simpleSwap j) x) - ρ (simpleSwap j) x =
    ρ (simpleSwap j) (ρ (simpleUpper i) x - x)
  rw [map_sub]
  congr 1
  change (ρ (simpleUpper i) * ρ (simpleSwap j)) x =
    (ρ (simpleSwap j) * ρ (simpleUpper i)) x
  rw [← map_mul, ← map_mul, upper_swap_commute i j hij]

private theorem pair_coefficients {a b : V} (ha : a ≠ 0)
    (D : V →ₗ[ZMod 2] V) (hDa : D a = 0) (hDb : D b = a)
    {c d : ZMod 2} (he : c • a + d • b = 0) : c = 0 ∧ d = 0 := by
  have hh := congrArg D he
  simp only [map_add, map_smul, hDa, hDb, smul_zero, zero_add, map_zero] at hh
  have hd : d = 0 := (smul_eq_zero.mp hh).resolve_right ha
  have hc : c = 0 := (smul_eq_zero.mp (by simpa [hd] using he)).resolve_right ha
  exact ⟨hc, hd⟩

/-- The highest vector and its translate at one active root are independent. -/
theorem LocalHighestVector.linearIndependent_active_pair
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) {i : Fin 4} (hi : i ∈ J) :
    LinearIndependent (ZMod 2) ![v, ρ (simpleSwap i) v] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  obtain ⟨h0, h1⟩ := pair_coefficients hv (upperDifference ρ i)
    (h.upperDifference_self i) (h.upperDifference_swap hi) hc
  intro k
  fin_cases k <;> assumption

/-- All active simple-exchange translates, together with the highest vector, are independent. -/
theorem LocalHighestVector.linearIndependent_simple_support
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) :
    LinearIndependent (ZMod 2)
      (fun k : Option {i : Fin 4 // i ∈ J} => k.elim v (fun i => ρ (simpleSwap i) v)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hs (j : {i : Fin 4 // i ∈ J}) : c (some j) = 0 := by
    have he := congrArg (upperDifference ρ j) hc
    have hd (i : {i : Fin 4 // i ∈ J}) :
        upperDifference ρ j (ρ (simpleSwap i) v) = if i = j then v else 0 := by
      by_cases hij : i = j
      · subst i
        simpa using h.upperDifference_swap j.property
      · rw [if_neg hij]
        exact h.upperDifference_other_swap (fun he => hij (Subtype.ext he.symm))
    simp only [map_add, map_sum, map_smul, map_zero, Fintype.sum_option,
      Option.elim_none, Option.elim_some, h.upperDifference_self, smul_zero,
      hd] at he
    have he' : c (some j) • v = 0 := by simpa using he
    exact (smul_eq_zero.mp he').resolve_right hv
  have hn : c none = 0 := by
    have he : c none • v = 0 := by simpa [Fintype.sum_option, hs] using hc
    exact (smul_eq_zero.mp he).resolve_right hv
  intro k
  cases k with
  | none => exact hn
  | some j => exact hs j

/-- The support size plus one is a lower bound on dimension. -/
theorem LocalHighestVector.card_support_add_one_le_finrank
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) :
    J.card + 1 ≤ Module.finrank (ZMod 2) V := by
  simpa using (h.linearIndependent_simple_support hv).fintype_card_le_finrank

/-- Two separated active roots give four independent exchange translates. -/
theorem LocalHighestVector.linearIndependent_separated_square
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) {i j : Fin 4}
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 < j.val) :
    LinearIndependent (ZMod 2)
      ![v, ρ (simpleSwap i) v, ρ (simpleSwap j) v,
        ρ (simpleSwap i) (ρ (simpleSwap j) v)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_four] at hc
  change c 0 • v + c 1 • ρ (simpleSwap i) v + c 2 • ρ (simpleSwap j) v +
    c 3 • ρ (simpleSwap i) (ρ (simpleSwap j) v) = 0 at hc
  have he := congrArg (upperDifference ρ j) hc
  simp only [map_add, map_smul, map_zero,
    upperDifference_swap_commute ρ j i (Or.inr hij),
    h.upperDifference_self, h.upperDifference_swap hj, smul_zero, zero_add] at he
  obtain ⟨h2, h3⟩ := pair_coefficients hv (upperDifference ρ i)
    (h.upperDifference_self i) (h.upperDifference_swap hi) he
  have he' : c 0 • v + c 1 • ρ (simpleSwap i) v = 0 := by
    simpa only [h2, h3, zero_smul, add_zero] using hc
  obtain ⟨h0, h1⟩ := pair_coefficients hv (upperDifference ρ i)
    (h.upperDifference_self i) (h.upperDifference_swap hi) he'
  intro k
  fin_cases k <;> assumption

/-- A module with two separated active roots has dimension at least four. -/
theorem LocalHighestVector.four_le_finrank_of_separated
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) {i j : Fin 4}
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 < j.val) :
    4 ≤ Module.finrank (ZMod 2) V := by
  simpa using (h.linearIndependent_separated_square hv hi hj hij).fintype_card_le_finrank

end Representation.SL5TenDimensional.Classification
