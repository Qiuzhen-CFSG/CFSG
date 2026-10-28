module

public import Theory.Representation.EndFieldFrobenius
public import Theory.Combinatorics.PeriodicWordProduct
public import Mathlib.Data.List.OfFn

/-!
# From an actual tensor period to a binary degree word

This conditional descent step consumes a tensor word and its dimension and
Frobenius-equivalence properties. It derives the word length and repetition
number using the actual Schur field, rather than assuming those parameters.
The existence and classification of the tensor factors remain separate inputs.

The Schur-field theorem identifies its degree `s` with the Frobenius period.
The full word length `n` is a period, so `s` divides `n`. Cutting the periodic
degree word after `s` entries and applying the dimension tower gives the binary
degree `s*b^t`, where `n=s*t` and `b` is the product of that block.

Source: GLS3, 2.8.6 and Remark 2.8.8, as used for G₂ in Aschbacher--Smith,
G.9.3(10), printed pp.356--357.
-/

open scoped MonoidAlgebra TensorProduct

public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary

variable {G V : Type*} [Monoid G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [Representation.IsIrreducible ρ]
  (K : Type*) [Field K] [IsAlgClosed K]
  [Algebra (Module.End (ZMod 2)[G] ρ.asModule) K] [CharP K 2]

/-- Once an actual tensor classification supplies the displayed word data,
the repetition parameters use exactly the original representation's Schur
degree. None of the tensor-classification premises is asserted here. -/
theorem parameters_of_periodic_word (n : ℕ) (hn : 0 < n) (w : ℕ → ℕ)
    (hnperiod : ∀ i, w (i + n) = w i)
    (hperiod : ∀ r, Nonempty ((Representation.extendScalars K ρ.endFieldRep).Equiv
      (Representation.frobeniusConjugate 2 r
        (Representation.extendScalars K ρ.endFieldRep))) ↔ ∀ i, w (i + r) = w i)
    (hdegree : Module.finrank K
      (K ⊗[Module.End (ZMod 2)[G] ρ.asModule] ρ.asModule) =
        ∏ i ∈ Finset.range n, w i)
    (hbasic : ∀ i, i < n → w i = 1 ∨ w i = 6 ∨ w i = 14 ∨ w i = 64)
    (hnontrivial : (∏ i ∈ Finset.range n, w i) ≠ 1) :
    let s := Representation.schurDegree 2 ρ
    0 < s ∧ ∃ (t : ℕ) (l : List ℕ), 0 < t ∧ l.length = s ∧ n = s * t ∧
      Module.finrank (ZMod 2) V = s * l.prod ^ t ∧ l.prod ≠ 1 ∧
        ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64 := by
  let s := Representation.schurDegree 2 ρ
  have hs : 0 < s := Representation.schurDegree_pos 2 ρ
  have hsdvd : s ∣ n :=
    (Representation.endFieldRep_frobenius_equiv_iff 2 ρ K n).mp
      ((hperiod n).mpr hnperiod)
  have hsperiod : ∀ i, w (i + s) = w i :=
    (hperiod s).mp
      ((Representation.endFieldRep_frobenius_equiv_iff 2 ρ K s).mpr (dvd_refl s))
  obtain ⟨t, hnt⟩ := hsdvd
  have ht : 0 < t := by
    by_contra! ht
    have : t = 0 := Nat.eq_zero_of_le_zero ht
    simp only [this, mul_zero] at hnt
    omega
  have hsn : s ≤ n := Nat.le_of_dvd hn ⟨t, hnt⟩
  let l : List ℕ := List.ofFn (fun i : Fin s => w i)
  have hprod : (∏ i ∈ Finset.range n, w i) = l.prod ^ t := by
    rw [hnt, Finset.prod_range_mul_of_period w s t hsperiod]
    congr 1
    exact (Fin.prod_ofFn (fun i : Fin s => w i)).trans
      (Fin.prod_univ_eq_prod_range w s) |>.symm
  refine ⟨hs, t, l, ht, List.length_ofFn, hnt, ?_, ?_, ?_⟩
  · rw [Representation.finrank_eq_schurDegree_mul 2 ρ K, hdegree, hprod]
  · intro h
    apply hnontrivial
    rw [hprod, h, one_pow]
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hbasic i (i.isLt.trans_le hsn)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
