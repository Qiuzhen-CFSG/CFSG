module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree.Actions

/-!
# Binary degree bounds for products of odd-prime dihedral groups

A faithful binary representation of `r` such factors has degree at least
`2r`, at least `2(r+1)` if a prime differs from three, and strictly greater
than `2(r+1)` if a prime exceeds five. The empty product and arbitrary
trivial summands are included.

The proof uses strong induction on the number of factors. Splitting at one
factor gives a rotation-fixed space and two isomorphic half-spaces. The
other factors partition into products acting faithfully on the fixed space
and on one half-space. Their inductive bounds give the result. For a
specified exceptional prime, split at a different factor; the one-factor
case instead uses the even moved dimension and its prime-order orbit
congruence, which in particular excludes seven in degree at most four.

Source: Aschbacher--Smith G.9.2, printed pp.351--353 (combined manuscript,
1 March 2004). The genuine A.1.44 splitting remains the explicit earlier
theorem input. No degree estimate or module classification is assumed.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

universe v

namespace DihedralDegree

private def DegreeAt (n : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (p : ι → ℕ), (∀ i, (p i).Prime) → (∀ i, Odd (p i)) →
      ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
        [FiniteDimensional (ZMod 2) W],
        ∀ σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W,
          Function.Injective σ →
            2 * n ≤ Module.finrank (ZMod 2) W ∧
            ((∃ i, p i ≠ 3) → 2 * (n + 1) ≤ Module.finrank (ZMod 2) W) ∧
            ((∃ i, 5 < p i) → 2 * (n + 1) < Module.finrank (ZMod 2) W)

private theorem degreeAt_of_splitting (split : DihedralSplittingTheorem.{v}) :
    ∀ n, DegreeAt.{v} n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ι _ _ hn p hp ho W _ _ _ σ hf
    classical
    by_cases hz : n = 0
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (hn.trans hz)
      simp [hz]
    have hpos : 0 < Fintype.card ι := by omega
    obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hpos
    by_cases hn1 : n = 1
    · have hb (i : ι) := single_factor_bounds (factorRep σ i) split (hp i) (ho i)
        (factorRep_injective σ hf i)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hn1] using (hb i₀).1
      · rintro ⟨i, hi⟩
        simpa [hn1] using (hb i).2.1 hi
      · rintro ⟨i, hi⟩
        simpa [hn1] using (hb i).2.2 hi
    have hstep (i : ι) :
        2 * n ≤ Module.finrank (ZMod 2) W ∧
        ((∃ j, j ≠ i ∧ p j ≠ 3) → 2 * (n + 1) ≤ Module.finrank (ZMod 2) W) ∧
        ((∃ j, j ≠ i ∧ 5 < p j) → 2 * (n + 1) < Module.finrank (ZMod 2) W) := by
      obtain ⟨a⟩ := exists_splitActions split hp ho σ hf i
      let I := Finset.univ.erase i \ a.J
      let C := rotationFixed (factorRep σ i)
      let U := reflectionHalf (factorRep σ i)
      have hJsub : a.J ⊆ Finset.univ.erase i := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun h => a.excluded (h ▸ hj), Finset.mem_univ _⟩
      have hcard : n = I.card + a.J.card + 1 := by
        have h := Finset.card_sdiff_add_card_eq_card hJsub
        have he := Finset.card_erase_of_mem (Finset.mem_univ i)
        simp only [Finset.card_univ] at he
        change I.card + a.J.card = _ at h
        omega
      have hIlt : I.card < n := by omega
      have hJlt : a.J.card < n := by omega
      have hC := ih I.card hIlt I (by simp) (fun j : I => p j)
        (fun j => hp j) (fun j => ho j) C
        (Representation.subrepresentation (σ.comp (subproductHom I)) C a.fixed_stable)
        a.fixed_faithful
      have hU := ih a.J.card hJlt a.J (by simp) (fun j : a.J => p j)
        (fun j => hp j) (fun j => ho j) U
        (Representation.subrepresentation (σ.comp (subproductHom a.J)) U a.half_stable)
        a.half_faithful
      obtain ⟨hd, _, hUp⟩ := split_dimensions (factorRep σ i) split (hp i) (ho i)
        (factorRep_injective σ hf i)
      change Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) C +
        2 * Module.finrank (ZMod 2) U at hd
      change 0 < Module.finrank (ZMod 2) U at hUp
      have hpart (j : ι) (hji : j ≠ i) : j ∈ I ∨ j ∈ a.J := by
        by_cases hj : j ∈ a.J
        · exact Or.inr hj
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr
            ⟨hji, Finset.mem_univ j⟩, hj⟩)
      refine ⟨by have := hC.1; have := hU.1; omega, ?_, ?_⟩
      · rintro ⟨j, hji, hj⟩
        rcases hpart j hji with hjI | hjJ
        · have h := hC.2.1 ⟨⟨j, hjI⟩, hj⟩
          have := hU.1
          omega
        · have h := hU.2.1 ⟨⟨j, hjJ⟩, hj⟩
          have := hC.1
          omega
      · rintro ⟨j, hji, hj⟩
        rcases hpart j hji with hjI | hjJ
        · have h := hC.2.2 ⟨⟨j, hjI⟩, hj⟩
          have := hU.1
          omega
        · have h := hU.2.2 ⟨⟨j, hjJ⟩, hj⟩
          have := hC.1
          omega
    refine ⟨(hstep i₀).1, ?_, ?_⟩
    · rintro ⟨j, hj⟩
      obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) j
      exact (hstep i).2.1 ⟨j, Ne.symm hi, hj⟩
    · rintro ⟨j, hj⟩
      obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) j
      exact (hstep i).2.2 ⟨j, Ne.symm hi, hj⟩

end DihedralDegree

/-- The uniform bounds in the dihedral induction, conditional only on the
A.1.44 splitting contract. The G.9.2 assembly supplies that earlier theorem. -/
theorem dihedralDegree_of_splitting (split : DihedralSplittingTheorem.{v}) :
    DihedralDegreeTheorem.{v} := by
  intro W _ _ _ r p hp ho σ hf
  exact DihedralDegree.degreeAt_of_splitting split r (Fin r) (Fintype.card_fin r)
    p hp ho W σ hf

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
