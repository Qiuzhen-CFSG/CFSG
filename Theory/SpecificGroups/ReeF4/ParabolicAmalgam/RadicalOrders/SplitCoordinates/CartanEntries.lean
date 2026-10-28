module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Detection
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation

/-!
# Triangular Cartan entries of ordered F4 root products

If two parameter families agree below a positive root's height, the difference
of their ordered products in that root row and a simple Cartan column is the
parameter difference times the root-coroot pairing. This holds for every order
of the positive or radical supports and for every Ree coefficient field,
including the field at `m = 0`.

The coroot combination with coefficients `(11, 21, 15, 8)` realizes ordinary
root height. Divided-power homogeneity gives a filtration of the actual
matrices by height increase. At the first height where factors differ,
multiplication adds their differences; all cross terms have greater height.
The linear divided power's Cartan column then singles out the specified root.

This proves the matrix calculation required by
`wordInSubgroup_injective_of_cartan_entries`, independently of root exchanges
or ordered factorization. It is the uniqueness calculation in the Chevalley
root construction underlying Aschbacher–Smith F.1.12(I)(5), printed p.263
(PDF p.274) of `refs/quasithin.pdf`; the parabolic order and fixed-point
assemblies are separate. The integral grading is from
`IntegralChevalleyTorusConjugation`, and the Cartan-column formula from
`PositiveSimple.RootLinear.RootSums.Columns`.
-/

open scoped BigOperators Matrix

namespace ReeF4.Parabolics.RadicalCoordinates

open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction

noncomputable section

section FilteredMatrices

variable {ι K : Type*} [CommRing K]

private def HasDegreeGE (w : ι → ℤ) (d : ℤ) (A : Matrix ι ι K) : Prop :=
  ∀ i j, w i - w j < d → A i j = 0

private lemma HasDegreeGE.zero (w : ι → ℤ) (d : ℤ) :
    HasDegreeGE w d (0 : Matrix ι ι K) := by
  intro i j _
  rfl

private lemma HasDegreeGE.mono {w : ι → ℤ} {d e : ℤ} {A : Matrix ι ι K}
    (hA : HasDegreeGE w d A) (he : e ≤ d) : HasDegreeGE w e A := by
  intro i j hij
  exact hA i j (lt_of_lt_of_le hij he)

private lemma HasDegreeGE.add {w : ι → ℤ} {d : ℤ} {A B : Matrix ι ι K}
    (hA : HasDegreeGE w d A) (hB : HasDegreeGE w d B) : HasDegreeGE w d (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private lemma HasDegreeGE.sub {w : ι → ℤ} {d : ℤ} {A B : Matrix ι ι K}
    (hA : HasDegreeGE w d A) (hB : HasDegreeGE w d B) : HasDegreeGE w d (A - B) := by
  intro i j hij
  simp only [Matrix.sub_apply, hA i j hij, hB i j hij, sub_zero]

private lemma HasDegreeGE.mul [Fintype ι] {w : ι → ℤ} {d e : ℤ} {A B : Matrix ι ι K}
    (hA : HasDegreeGE w d A) (hB : HasDegreeGE w e B) : HasDegreeGE w (d + e) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i - w k < d
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private lemma HasDegreeGE.smul {w : ι → ℤ} {d : ℤ} {A : Matrix ι ι K}
    (hA : HasDegreeGE w d A) (t : K) : HasDegreeGE w d (t • A) := by
  intro i j hij
  simp only [Matrix.smul_apply, smul_eq_mul, hA i j hij, mul_zero]

private lemma unipotent_list_prod [Fintype ι] [DecidableEq ι] {α : Type*} (w : ι → ℤ)
    (A : α → Matrix ι ι K) (l : List α)
    (hA : ∀ a ∈ l, HasDegreeGE w 1 (A a - 1)) :
    HasDegreeGE w 1 ((l.map A).prod - 1) := by
  induction l with
  | nil => simpa using HasDegreeGE.zero (K := K) w 1
  | cons a l ih =>
    have ha := hA a (List.mem_cons_self ..)
    have hl := ih (fun b hb => hA b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons, List.prod_cons]
    have eqn : A a * (l.map A).prod - 1 =
        (A a - 1) + ((l.map A).prod - 1) + (A a - 1) * ((l.map A).prod - 1) := by
      noncomm_ring
    rw [eqn]
    exact (ha.add hl).add ((ha.mul hl).mono (by omega))

/-- At the first degree at which factors can differ, multiplication adds their differences. -/
private lemma list_prod_difference [Fintype ι] [DecidableEq ι] {α : Type*} (w : ι → ℤ) (d : ℤ)
    (A B : α → Matrix ι ι K) (l : List α)
    (hA : ∀ a ∈ l, HasDegreeGE w 1 (A a - 1))
    (hB : ∀ a ∈ l, HasDegreeGE w 1 (B a - 1))
    (hD : ∀ a ∈ l, HasDegreeGE w d (A a - B a)) :
    HasDegreeGE w d ((l.map A).prod - (l.map B).prod) ∧
      HasDegreeGE w (d + 1)
        ((l.map A).prod - (l.map B).prod - (l.map fun a => A a - B a).sum) := by
  induction l with
  | nil => simpa using ⟨HasDegreeGE.zero (K := K) w d, HasDegreeGE.zero (K := K) w (d + 1)⟩
  | cons a l ih =>
    have ha := hA a (List.mem_cons_self ..)
    have hd := hD a (List.mem_cons_self ..)
    have hb := unipotent_list_prod w B l (fun b hb => hB b (List.mem_cons_of_mem a hb))
    obtain ⟨hld, hle⟩ := ih
      (fun b hb => hA b (List.mem_cons_of_mem a hb))
      (fun b hb => hB b (List.mem_cons_of_mem a hb))
      (fun b hb => hD b (List.mem_cons_of_mem a hb))
    have hcross : HasDegreeGE w (d + 1)
        ((A a - 1) * ((l.map A).prod - (l.map B).prod) +
          (A a - B a) * ((l.map B).prod - 1)) := by
      exact ((ha.mul hld).mono (by omega)).add (hd.mul hb)
    have eqn : A a * (l.map A).prod - B a * (l.map B).prod =
        (A a - B a) + ((l.map A).prod - (l.map B).prod) +
          ((A a - 1) * ((l.map A).prod - (l.map B).prod) +
            (A a - B a) * ((l.map B).prod - 1)) := by noncomm_ring
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    constructor
    · rw [eqn]
      exact (hd.add hld).add (hcross.mono (by omega))
    · have eqn' : A a * (l.map A).prod - B a * (l.map B).prod -
          (A a - B a + (l.map fun a => A a - B a).sum) =
          ((l.map A).prod - (l.map B).prod - (l.map fun a => A a - B a).sum) +
          ((A a - 1) * ((l.map A).prod - (l.map B).prod) +
            (A a - B a) * ((l.map B).prod - 1)) := by rw [eqn]; abel
      rw [eqn']
      exact hle.add hcross

end FilteredMatrices

private def corootHeight (r : F4Chevalley.Root) : ℤ :=
  11 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  21 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  15 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  8 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)

private lemma corootHeight_simple (i : Fin 4) :
    corootHeight (typeF4SimpleRootIndex i) = 1 := by
  have hp (j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [corootHeight, hp]
  fin_cases i <;> norm_num [typeF4CartanMatrix, Fin.ext_iff]

private lemma corootHeight_add {i j k : F4Chevalley.Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    corootHeight k = corootHeight i + corootHeight j := by
  have hp (q : F4Chevalley.Root) :=
    typeF4RootPairing.pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := q) h
  simp only [corootHeight, hp]
  ring

private lemma corootHeight_eq_height {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) :
    corootHeight r = typeF4RootPairing_base.height r := by
  have hs (i : F4Chevalley.Root) (hi : i ∈ typeF4RootPairing_base.support) :
      corootHeight i = typeF4RootPairing_base.height i := by
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, corootHeight_simple]
    exact (RootPairing.Base.height_one_of_mem_support (he ▸ hi)).symm
  apply hr.induction_on_add hs
  intro i j k hk hi hj
  rw [corootHeight_add hk, typeF4RootPairing_base.height_add hk, hi, hs j hj]

private def cartanBasisDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  11 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  21 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  15 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  8 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)

private lemma cartanBasisDegree_root {k : Support} (r : Root k) :
    cartanBasisDegree (Sum.inr r.val) = (rootDegree r.val : ℤ) := by
  change corootHeight r.val = _
  rw [corootHeight_eq_height (supported_isPos r), rootDegree_cast]

private lemma cartanBasisDegree_cartan (j : typeF4RootPairing_base.support) :
    cartanBasisDegree (Sum.inl j) = 0 := by
  simp [cartanBasisDegree, chevalleyBasisWeight]

private lemma dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    cartanBasisDegree i - cartanBasisDegree j = (n : ℤ) * corootHeight r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  dsimp only [cartanBasisDegree, corootHeight]
  linear_combination 11 * h0 + 21 * h1 + 15 * h2 + 8 * h3

private lemma dividedPower_hasDegreeGE (m : ℕ) {k : Support} (r : Root k) (n : ℕ) :
    HasDegreeGE cartanBasisDegree ((n : ℤ) * rootDegree r.val)
      (specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r.val n)) := by
  intro i j hij
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r.val n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := dividedPower_degree r.val n i j hint
  rw [corootHeight_eq_height (supported_isPos r), ← rootDegree_cast r] at hd
  omega

private lemma rootCurve_hasDegreeGE (m : ℕ) {k : Support} (r : Root k)
    (t : CoefficientField m) :
    HasDegreeGE cartanBasisDegree (rootDegree r.val)
      ((F4Chevalley.rootCurve r.val t).val - 1) := by
  have hr : (0 : ℤ) < rootDegree r.val := by exact_mod_cast rootDegree_pos r
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField m) :
      HasDegreeGE cartanBasisDegree (rootDegree r.val)
        (s • specializeMatrix (S := CoefficientField m)
          (F4Chevalley.integralOperators.rootDividedPower r.val n)) := by
    apply ((dividedPower_hasDegreeGE m r n).mono ?_).smul
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [F4Chevalley.rootCurve_matrix_formula]
  have he : (1 + t • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r.val 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r.val 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r.val 3)) - 1 =
      t • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r.val 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r.val 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r.val 3) := by abel
  rw [he]
  exact ((hs 1 (by decide) t).add (hs 2 (by decide) (t ^ 2))).add
    (hs 3 (by decide) (t ^ 3))

private lemma rootCurve_sub_hasDegreeGE (m : ℕ) {k : Support} (r : Root k)
    (t u : CoefficientField m) :
    HasDegreeGE cartanBasisDegree (rootDegree r.val)
      ((F4Chevalley.rootCurve r.val t).val - (F4Chevalley.rootCurve r.val u).val) := by
  have h := (rootCurve_hasDegreeGE m r t).sub (rootCurve_hasDegreeGE m r u)
  have he : ((F4Chevalley.rootCurve r.val t).val - 1) -
      ((F4Chevalley.rootCurve r.val u).val - 1) =
      (F4Chevalley.rootCurve r.val t).val - (F4Chevalley.rootCurve r.val u).val := by abel
  rwa [he] at h

private lemma dividedPower_one_cartan (m : ℕ) (s r : F4Chevalley.Root)
    (j : typeF4RootPairing_base.support) :
    specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower s 1) (Sum.inr r) (Sum.inl j) =
      if r = s then (typeF4RootPairing.pairingIn ℤ s j : CoefficientField m) else 0 := by
  classical
  have h := congrFun
    (WordRelations.Faithfulness.Adjoint.PositiveSimple.coordinateOperator_mulVec_cartan m s j)
    (Sum.inr r)
  rw [Matrix.mulVec_single_one] at h
  simpa [F4Chevalley.dividedPower_one, specializeMatrix,
    WordRelations.Faithfulness.Adjoint.coordinateOperator, Pi.single_apply] using h

private lemma rootCurve_sub_cartan (m : ℕ) {k : Support} (s r : Root k)
    (hs : rootDegree r.val ≤ rootDegree s.val) (t u : CoefficientField m)
    (j : typeF4RootPairing_base.support) :
    ((F4Chevalley.rootCurve s.val t).val - (F4Chevalley.rootCurve s.val u).val)
        (Sum.inr r.val) (Sum.inl j) =
      if r = s then (t - u) * (typeF4RootPairing.pairingIn ℤ r.val j : CoefficientField m)
      else 0 := by
  classical
  have hn (n : ℕ) (hn : 2 ≤ n) :
      specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower s.val n)
          (Sum.inr r.val) (Sum.inl j) = 0 := by
    apply dividedPower_hasDegreeGE m s n
    rw [cartanBasisDegree_root, cartanBasisDegree_cartan, sub_zero]
    have hp : (0 : ℤ) < rootDegree s.val := by exact_mod_cast rootDegree_pos s
    have hs' : (rootDegree r.val : ℤ) ≤ rootDegree s.val := by exact_mod_cast hs
    have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  simp only [Matrix.sub_apply, F4Chevalley.rootCurve_matrix_formula, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, hn 2 (by decide), hn 3 (by decide),
    dividedPower_one_cartan, mul_zero, add_zero]
  by_cases h : r = s
  · subst s
    simp only [ite_true]
    ring
  · have h' : r.val ≠ s.val := fun he => h (Subtype.ext he)
    simp [h, h']

private lemma word_matrix (m : ℕ) {k : Support} (e : RootOrder k) (t : Parameters m k) :
    (word m e t).val.val =
      ((List.ofFn e).map fun r => (F4Chevalley.rootCurve r.val (t r)).val).prod := by
  let f : SplitGroup m →* Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
      (CoefficientField m) := (Units.coeHom _).comp (SplitGroup m).subtype
  change f (word m e t) = _
  rw [word, map_list_prod, List.map_ofFn, List.map_ofFn]
  rfl

/-- Agreement below a root's height makes its Cartan-entry difference linear
in that root's parameter, for every ordering of each positive support. -/
public theorem wordCartanEntry_sub_of_lower_eq (m : ℕ) {k : Support}
    (e : RootOrder k) (t u : Parameters m k) (r : Root k)
    (htu : ∀ s : Root k, rootDegree s.val < rootDegree r.val → t s = u s)
    (j : typeF4RootPairing_base.support) :
    wordCartanEntry m e t r.val j - wordCartanEntry m e u r.val j =
      (t r - u r) * (typeF4RootPairing.pairingIn ℤ r.val j : CoefficientField m) := by
  classical
  let A (s : Root k) := (F4Chevalley.rootCurve s.val (t s)).val
  let B (s : Root k) := (F4Chevalley.rootCurve s.val (u s)).val
  have hA (s : Root k) : HasDegreeGE cartanBasisDegree 1 (A s - 1) :=
    (rootCurve_hasDegreeGE m s (t s)).mono (by exact_mod_cast rootDegree_pos s)
  have hB (s : Root k) : HasDegreeGE cartanBasisDegree 1 (B s - 1) :=
    (rootCurve_hasDegreeGE m s (u s)).mono (by exact_mod_cast rootDegree_pos s)
  have hD (s : Root k) :
      HasDegreeGE cartanBasisDegree (rootDegree r.val) (A s - B s) := by
    by_cases hs : rootDegree s.val < rootDegree r.val
    · dsimp only [A, B]
      rw [htu s hs, sub_self]
      exact HasDegreeGE.zero _ _
    · exact (rootCurve_sub_hasDegreeGE m s (t s) (u s)).mono (by exact_mod_cast Nat.le_of_not_gt hs)
  have h := (list_prod_difference cartanBasisDegree (rootDegree r.val) A B (List.ofFn e)
    (fun s _ => hA s) (fun s _ => hB s) (fun s _ => hD s)).2
  have he := h (Sum.inr r.val) (Sum.inl j) (by
    rw [cartanBasisDegree_root, cartanBasisDegree_cartan]
    omega)
  have hf (s : Root k) : (A s - B s) (Sum.inr r.val) (Sum.inl j) =
      if r = s then (t r - u r) * (typeF4RootPairing.pairingIn ℤ r.val j : CoefficientField m)
      else 0 := by
    by_cases hs : rootDegree s.val < rootDegree r.val
    · have hne : r ≠ s := by rintro rfl; omega
      simp [A, B, htu s hs, hne]
    · have hh := rootCurve_sub_cartan m s r (Nat.le_of_not_gt hs) (t s) (u s) j
      by_cases hrs : r = s
      · subst s
        exact hh
      · simpa only [if_neg hrs] using hh
  have hsum : ((List.ofFn e).map fun s => A s - B s).sum (Sum.inr r.val) (Sum.inl j) =
      (t r - u r) * (typeF4RootPairing.pairingIn ℤ r.val j : CoefficientField m) := by
    simp only [List.map_ofFn, Function.comp_apply, List.sum_ofFn, Matrix.sum_apply, hf]
    have hi (i : Fin (Nat.card (Root k))) : r = e i ↔ i = e.symm r := by
      constructor
      · intro hh
        rw [hh, e.symm_apply_apply]
      · rintro rfl
        simp
    simp only [hi]
    simp
  simp only [Matrix.sub_apply, hsum] at he
  simp only [wordCartanEntry, word_matrix]
  change ((List.ofFn e).map A).prod (Sum.inr r.val) (Sum.inl j) -
    ((List.ofFn e).map B).prod (Sum.inr r.val) (Sum.inl j) = _
  exact sub_eq_zero.mp he

end
end ReeF4.Parabolics.RadicalCoordinates
