module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryRankOne
public import Theory.Combinatorics.PeriodicBinaryWeight
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition
public import Theory.Representation.SL2.BinaryHermitianRecognition
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank

/-!
# Recognition of the small binary rank-one modules

The small-degree alternatives in `BinaryRankOne` retain the actual Schur
field and an intertwining equivalence after its algebraic closure. Here
we identify the highest weights themselves: a single binary digit, two
digits separated by the Schur degree, or all three digits for SL₂(8).

The Frobenius period makes the digit block repeat. The known dimensions
two, four and eight imply that each block has just one nonzero digit.
The resulting equivalences are retained, including the bit position and
field embedding. No component hypothesis is used, so this reduction also
applies to the irreducible factor in the two-component argument.

The concrete model comparisons descend these equivalences to the natural
scalar restriction, the Hermitian action over the half-field, and the
SL₂(8) triple Frobenius tensor. The exhaustive classifier retains the
Schur degrees, an actual field identification in the Hermitian case, and
GF(8) identification and Frobenius generation in the exceptional case.
Both the faithful and the weaker nontrivial-action forms are available.

The proved sharp automorphism two-rank bounds for SL₂ and its genuine
projective quotient are re-exported from `BinaryAutomorphismRank`.
The original-actor conclusions of G.9.3 are assembled in the descendant
`RankOneRecognition.Component`. Recognition here is in the concrete
Hermitian model; comparison with the literal minus Omega action remains
a separate equivariant group-and-module comparison for its assembly owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(6),
(7), (16), printed pp.354,356--357; GLS volume 3, §§2.8.6, 2.8.8, 2.8.10(b).
-/

public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation Representation.SL2
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]

/-- The actual Schur-field scalar extension has one of the three exact
highest weights, with its intertwining equivalence and bit position. -/
theorem binary_small_highestWeight_alternatives (hρ : ∃ g, ρ g ≠ 1)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (n + 1)) :
    let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
    let s := Module.finrank (ZMod 2) E
    ∃ e : K →+* AlgebraicClosure E,
      (s = n ∧ Module.finrank (ZMod 2) V = 2 * n ∧
        ∃ j < n, Nonempty ((extendScalars (AlgebraicClosure E) ρ.endFieldRep).Equiv
          (highestWeightSpan e (2 ^ j)).toRepresentation)) ∨
      (2 * s = n ∧ Module.finrank (ZMod 2) V = 2 * n ∧
        ∃ j < s, Nonempty ((extendScalars (AlgebraicClosure E) ρ.endFieldRep).Equiv
          (highestWeightSpan e (2 ^ j * (1 + 2 ^ s))).toRepresentation)) ∨
      (s = 1 ∧ n = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧
        Nonempty ((extendScalars (AlgebraicClosure E) ρ.endFieldRep).Equiv
          (highestWeightSpan e 7).toRepresentation)) := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let s := Module.finrank (ZMod 2) E
  obtain ⟨hs, w, hw, hsdiv, hperiod, hdim, e, he⟩ :=
    exists_binary_highestWeight_parameters ρ hρ n hcard
  have hweight (t : ℕ) (ht : 0 < t) (hnt : n = s * t)
      (hdt : Module.finrank (ZMod 2) V = s * 2 ^ t) :
      ∃ j < s, w.val = 2 ^ j * ∑ i ∈ Finset.range t, (2 ^ s) ^ i := by
    apply Nat.binary_weight_of_period_and_degree s t w.val hs ht
    · rw [← hnt, ← hcard]; exact w.isLt
    · simpa only [hcard, hnt] using hperiod
    · have hp : (∏ i : Fin n, (w.val / 2 ^ (i : ℕ) % 2 + 1)) = 2 ^ t :=
        Nat.eq_of_mul_eq_mul_left hs (hdim.symm.trans hdt)
      subst n
      exact hp
  refine ⟨e, ?_⟩
  rcases binary_small_degree_schur_alternatives ρ hρ n hn hcard hd with h | h | h
  · have hsn : s = n := h.1
    obtain ⟨j, hj, hwj⟩ := hweight 1 (by decide) (by dsimp [s, E]; omega)
      (by simpa only [pow_one, hsn, mul_comm] using h.2)
    have hwj' : w.val = 2 ^ j := by simpa using hwj
    exact Or.inl ⟨h.1, h.2, j, by omega, hwj' ▸ he⟩
  · obtain ⟨j, hj, hwj⟩ := hweight 2 (by decide) (by dsimp [s, E]; omega)
      (by dsimp [s, E]; nlinarith [h.1, h.2])
    have hwj' : w.val = 2 ^ j * (1 + 2 ^ s) := by
      simpa [Finset.sum_range_succ] using hwj
    exact Or.inr (Or.inl ⟨h.1, h.2, j, hj, hwj' ▸ he⟩)
  · obtain ⟨j, hj, hwj⟩ := hweight 3 (by decide) (by dsimp [s, E]; omega)
      (by dsimp [s, E]; rw [h.1]; simpa using h.2.2)
    have hj0 : j = 0 := by dsimp [s, E] at hj; omega
    have hw7 : w.val = 7 := by
      simpa [s, E, h.1, hj0, Finset.sum_range_succ] using hwj
    exact Or.inr (Or.inr ⟨h.1, h.2.1, h.2.2, hw7 ▸ he⟩)

/-- Every nontrivial irreducible binary SL₂-module in the small-degree range
is the natural scalar restriction, the Hermitian half-field module, or the
SL₂(8) triple Frobenius tensor. All alternatives retain actual intertwining
equivalences and the Schur degree; the last retains GF(8) and Frobenius generation.
No component or SQTK hypothesis is required. -/
theorem binary_small_module_alternatives (hρ : ∃ g, ρ g ≠ 1)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (n + 1)) :
    let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
    (s = n ∧ Module.finrank (ZMod 2) V = 2 * n ∧ BinarySmall.IsNatural ρ) ∨
    (2 * s = n ∧ Module.finrank (ZMod 2) V = 2 * n ∧
      ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩; BinarySmall.IsHermitian ρ s) ∨
    (s = 1 ∧ n = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧ BinarySmall.IsTriple ρ ∧
      Nonempty (K ≃+* GaloisField 2 3) ∧
      ∀ τ : K ≃+* K, ∃ j : ℕ, j < 3 ∧ (iterateFrobeniusEquiv K 2 1) ^ j = τ) := by
  obtain ⟨e, h | h | h⟩ := binary_small_highestWeight_alternatives ρ hρ n hn hcard hd
  · obtain ⟨hs, hd, j, hj, he⟩ := h
    exact .inl ⟨hs, hd, BinarySmall.isNatural_of_highestWeight_pow_two
      ρ n hn hcard hs j hj e he⟩
  · obtain ⟨hs, hd, j, hj, he⟩ := h
    have hpos : 0 < Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) :=
      Nat.zero_lt_of_lt hj
    refine .inr (.inl ⟨hs, hd, hpos, ?_⟩)
    exact BinaryHermitian.isHermitian_of_highestWeight_pair ρ hpos
      (by rwa [hs]) rfl j hj e he
  · obtain ⟨hs, hn3, hd, he⟩ := h
    have hc : Nat.card K = 8 := by simpa [hn3] using hcard
    exact .inr (.inr ⟨hs, hn3, hd,
      BinarySmall.isTriple_of_highestWeight_seven ρ hc hs e he,
      BinarySmall.nonempty_fieldEightEquiv hc,
      BinarySmall.exists_frobenius_pow_eq_of_card_eight hc⟩)

omit [Finite K] [CharP K 2] [FiniteDimensional (ZMod 2) V] [ρ.IsIrreducible] in
private theorem nontrivial_action_of_faithful (hρ : Function.Injective ρ) :
    ∃ g, ρ g ≠ 1 := by
  let g : SL(2,K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨g, fun hg => ?_⟩
  have hg1 : g = 1 := hρ (hg.trans ρ.map_one.symm)
  have he := congrArg (fun a : SL(2,K) => a.val 0 1) hg1
  simp [g] at he

/-- The faithful irreducible classification for every binary field of order
`2^n`, `n ≥ 2`, with no assumed model, highest weight, or descent premise.
In the Hermitian branch `n = 2*s` and the coefficient field has order `2^s`;
in the exceptional branch extension to `K` is the literal triple tensor. -/
theorem binary_small_faithful_classification (hρ : Function.Injective ρ)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (n + 1)) :
    let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
    (s = n ∧ Module.finrank (ZMod 2) V = 2 * n ∧ BinarySmall.IsNatural ρ) ∨
    (2 * s = n ∧ Module.finrank (ZMod 2) V = 2 * n ∧
      ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩; BinarySmall.IsHermitian ρ s) ∨
    (s = 1 ∧ n = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧ BinarySmall.IsTriple ρ ∧
      Nonempty (K ≃+* GaloisField 2 3) ∧
      ∀ τ : K ≃+* K, ∃ j : ℕ, j < 3 ∧ (iterateFrobeniusEquiv K 2 1) ^ j = τ) :=
  binary_small_module_alternatives ρ (nontrivial_action_of_faithful ρ hρ) n hn hcard hd

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
