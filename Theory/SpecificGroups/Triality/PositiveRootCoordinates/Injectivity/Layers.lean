module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Injectivity.Filtration
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Injectivity.Recovery

/-!
# Uniqueness of height-ordered canonical root products

Integral divided powers raise root weights by the corresponding multiple of
the root. A positive real height therefore filters the actual specialized
matrices. At the first root's height, cross terms and other roots contribute
nothing to its Cartan/opposite-root column. The recovery functional extracts
its parameter. Canceling that unit and inducting proves uniqueness for the
whole list of distinct roots in nondecreasing height.

Source: GLS3, 1.12.7 and 2.3.6–7 (`refs/KGroup/GLS3/chapter2.tex`). No
normal-form certificate, collection law, or characteristic restriction is used.
-/

@[expose] public section
open scoped BigOperators
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace Triality.Standard.PositiveCoordinates.Injectivity
noncomputable section
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {S : Type*} [CommRing S]

abbrev rootMatrix (r : ι) (t : S) :=
  rootCurveMatrix (integralChevalleyRootOperators (P := P) (b := b)) r t

lemma rootMatrix_sub_one (r : ι) (t : S) :
    rootMatrix (b := b) r t - 1 =
      t • specializeMatrix (rootDividedPower (b := b) r 1) +
      t ^ 2 • specializeMatrix (rootDividedPower (b := b) r 2) +
      t ^ 3 • specializeMatrix (rootDividedPower (b := b) r 3) := by
  change (1 + _ + _ + _) - 1 = _
  abel

lemma rootDividedPower_raises (L : M →+ ℝ) (r : ι) (hr : b.IsPos r) (n : ℕ) :
    Raises (fun j => L (rootWeight (b := b) j)) ((n : ℝ) * L (P.root r))
      (specializeMatrix (S := S) (rootDividedPower (b := b) r n)) := by
  intro i j hij
  by_contra hne
  have hInt : rootDividedPower (b := b) r n i j ≠ 0 := by
    intro hz
    exact hne (by simp [specializeMatrix, hz])
  have hw := congrArg L (rootDividedPower_homogeneous r hr n i j hInt)
  simp only [map_add, map_nsmul, nsmul_eq_mul] at hw
  linarith

lemma rootMatrix_raises (L : M →+ ℝ) (r : ι) (hr : b.IsPos r)
    (hL : 0 ≤ L (P.root r)) (t : S) :
    Raises (fun j => L (rootWeight (b := b) j)) (L (P.root r))
      (rootMatrix (b := b) r t - 1) := by
  rw [rootMatrix_sub_one]
  have h1 := rootDividedPower_raises (S := S) L r hr 1
  have h2 := rootDividedPower_raises (S := S) L r hr 2
  have h3 := rootDividedPower_raises (S := S) L r hr 3
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul] at h1 h2 h3
  exact ((h1.smul _ t).add _ ((h2.mono _ (by linarith)).smul _ (t ^ 2))).add _
    ((h3.mono _ (by linarith)).smul _ (t ^ 3))

lemma rootMatrix_other_cartan (L : M →+ ℝ) (r s : ι) (hs : b.IsPos s)
    (hpos : 0 < L (P.root r)) (hle : L (P.root r) ≤ L (P.root s))
    (hne : s ≠ r) (t : S) (c : b.support) :
    rootMatrix (b := b) s t (Sum.inl c) (Sum.inr (P.reflectionPerm r r)) = 0 := by
  let := P.indexNeg
  have hnroot (j : ι) : P.root (-j) = -P.root j := by simp
  have h1 : specializeMatrix (S := S) (rootDividedPower (b := b) s 1)
      (Sum.inl c) (Sum.inr (-r)) = 0 := by
    have hz : rootDividedPower (b := b) s 1 (Sum.inl c) (Sum.inr (-r)) = 0 := by
      by_contra h
      have hw := rootDividedPower_homogeneous s hs 1 (Sum.inl c) (Sum.inr (-r)) h
      change (0 : M) = 1 • P.root s + P.root (-r) at hw
      simp only [one_nsmul, hnroot, ← sub_eq_add_neg] at hw
      exact hne (P.root.injective (sub_eq_zero.mp hw.symm))
    simp only [specializeMatrix, Matrix.map_apply, hz, map_zero]
  have h2 := rootDividedPower_raises (S := S) L s hs 2
    (Sum.inl c) (Sum.inr (-r))
  have h3 := rootDividedPower_raises (S := S) L s hs 3
    (Sum.inl c) (Sum.inr (-r))
  simp only [rootWeight, Sum.elim_inl, Sum.elim_inr, map_zero, hnroot,
    map_neg, Nat.cast_ofNat] at h2 h3
  have hz2 := h2 (by linarith)
  have hz3 := h3 (by linarith)
  change (1 + t • specializeMatrix (rootDividedPower (b := b) s 1) +
    t ^ 2 • specializeMatrix (rootDividedPower (b := b) s 2) +
    t ^ 3 • specializeMatrix (rootDividedPower (b := b) s 3) :
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)
      (Sum.inl c) (Sum.inr (-r)) = 0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h1, hz2, hz3,
    mul_zero, Matrix.one_apply, Sum.inl_ne_inr, if_false, add_zero]

lemma positiveRecovery_prod (L : M →+ ℝ) (r : ι) (l : List ι) (a : ι → S)
    (hr : b.IsPos r) (hl : ∀ s ∈ l, b.IsPos s) (hnot : r ∉ l)
    (hpos : 0 < L (P.root r)) (hle : ∀ s ∈ l, L (P.root r) ≤ L (P.root s)) :
    positiveRecovery (b := b) r
      ((r :: l).map (fun s => rootMatrix (b := b) s (a s))).prod = a r := by
  apply (positiveRecovery_congr r _ (rootMatrix r (a r)) ?_).trans
    (positiveRecovery_curve r hr (a r))
  intro c
  let := P.indexNeg
  let d := fun j => L (rootWeight (b := b) j)
  let h := L (P.root r)
  have hraise : ∀ A ∈ (r :: l).map (fun s => rootMatrix (b := b) s (a s)),
      Raises d h (A - 1) := by
    intro A hA
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hA
    rcases List.mem_cons.mp hs with hs | hs
    · subst s
      exact rootMatrix_raises L r hr hpos.le (a r)
    · exact (rootMatrix_raises L s (hl s hs) (hpos.le.trans (hle s hs)) (a s)).mono d (hle s hs)
  have he := prod_entry_eq_sum d h hpos _ hraise (Sum.inl c) (Sum.inr (-r))
    (by simp [d, h, rootWeight])
  have htail : ((l.map (fun s => rootMatrix (b := b) s (a s) - 1)).sum :
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) S) (Sum.inl c) (Sum.inr (-r)) = 0 := by
    have hz (s : ι) (hs : s ∈ l) :
        (rootMatrix (b := b) s (a s) - 1) (Sum.inl c) (Sum.inr (-r)) = 0 := by
      have hsr : s ≠ r := fun he => hnot (he ▸ hs)
      simpa using rootMatrix_other_cartan L r s (hl s hs) hpos (hle s hs) hsr (a s) c
    apply list_sum_entry_zero
    intro A hA
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hA
    exact hz s hs
  change ((r :: l).map (fun s => rootMatrix (b := b) s (a s))).prod
    (Sum.inl c) (Sum.inr (-r)) = rootMatrix (b := b) r (a r) (Sum.inl c) (Sum.inr (-r))
  simpa only [List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Sum.inl.injEq,
    Sum.inl_ne_inr, if_false, zero_add, sub_zero, htail, add_zero] using he

/-- An ordered list of distinct positive roots has unique parameters when its
heights are nondecreasing. -/
lemma rootCurve_prod_parameters_eq (L : M →+ ℝ) (l : List ι)
    (hl : ∀ r ∈ l, b.IsPos r) (hpos : ∀ r ∈ l, 0 < L (P.root r))
    (hnd : l.Nodup)
    (hsort : l.Pairwise (fun r s => L (P.root r) ≤ L (P.root s)))
    (a a' : ι → S)
    (heq : (l.map (fun r => rootCurveUnit (integralChevalleyRootOperators (b := b)) r (a r))).prod =
      (l.map (fun r => rootCurveUnit (integralChevalleyRootOperators (b := b)) r (a' r))).prod) :
    ∀ r ∈ l, a r = a' r := by
  induction l with
  | nil => simp
  | cons r l ih =>
    have hmem : r ∈ r :: l := List.mem_cons_self
    have hl' : ∀ s ∈ l, b.IsPos s := fun s hs => hl s (List.mem_cons_of_mem r hs)
    have hpos' : ∀ s ∈ l, 0 < L (P.root s) := fun s hs => hpos s (List.mem_cons_of_mem r hs)
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hle, hsort'⟩ := List.pairwise_cons.mp hsort
    have hm : ((r :: l).map (fun s => rootMatrix (b := b) s (a s))).prod =
        ((r :: l).map (fun s => rootMatrix (b := b) s (a' s))).prod := by
      have hv := congrArg (Units.coeHom (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)) heq
      simpa only [map_list_prod, List.map_map, Function.comp_def,
        Units.coeHom_apply, rootCurveUnit] using hv
    have hr : a r = a' r := by
      have he := congrArg (positiveRecovery (b := b) r) hm
      simpa only [positiveRecovery_prod L r l a (hl r hmem) hl' hnot (hpos r hmem) hle,
        positiveRecovery_prod L r l a' (hl r hmem) hl' hnot (hpos r hmem) hle] using he
    simp only [List.map_cons, List.prod_cons, hr] at heq
    have htail := ih hl' hpos' hnd' hsort' (mul_left_cancel heq)
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hr
    · exact htail s hs

end
end Triality.Standard.PositiveCoordinates.Injectivity
