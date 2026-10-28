module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.MatrixCoordinates
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.Columns
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex

/-!
# Literal unipotent matrices and subfield recovery for F4

A single ordering of the Cartan-plus-root basis by increasing root height
makes every positive root word lower unit triangular and every negative
root word upper unit triangular. The root factors may appear in any order.

The integral coroot combination `(11, 21, 15, 8)` gives ordinary root height.
Divided-power weight homogeneity then filters the actual root matrices.
At the first height where two parameter families differ, their Cartan-column
difference is linear in that parameter. The detecting-coroot coefficient
remains nonzero over every field of characteristic two: this follows from
the integer parity statement certified by the finite-coefficient calculation.
Comparing with the word truncated below each height recovers the parameters
over any subfield containing the matrix entries.

This adapts the filtration argument in
`ReeF4.Parabolics.RadicalCoordinates.CartanEntries` to arbitrary algebraic
points and both root signs. It uses literal `rootCurve` matrices throughout;
no finite split-group membership or Bruhat coverage is assumed.

Source: Steinberg, *Lectures on Chevalley Groups*, Lemma 17 and Theorem 7(b),
especially the coordinate-recovery calculation on p.65
(`refs/KGroup/GLS3/Chapter2St1.tex`, lines 1036–1038).
-/

open scoped BigOperators Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
public noncomputable section
local instance unipotentRecoveryRootNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg
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

private lemma corootHeight_neg (r : F4Chevalley.Root) :
    corootHeight (-r) = -corootHeight r := by
  simp only [corootHeight, typeF4RootPairing.indexNeg_neg,
    typeF4RootPairing.pairingIn_reflectionPerm_self_left]
  ring

private def signedWeight (s : ℤ) (i : F4Chevalley.BasisIndex) : ℤ :=
  s * cartanBasisDegree i

private def signedHeight (s : ℤ) (r : F4Chevalley.Root) : ℤ :=
  s * corootHeight r

private lemma signedWeight_root (s : ℤ) (r : F4Chevalley.Root) :
    signedWeight s (Sum.inr r) = signedHeight s r := rfl

private lemma signedWeight_cartan (s : ℤ) (j : typeF4RootPairing_base.support) :
    signedWeight s (Sum.inl j) = 0 := by
  simp [signedWeight, cartanBasisDegree_cartan]

variable {F : Type*} [Field F]

private lemma dividedPower_hasDegreeGE (s : ℤ) (r : F4Chevalley.Root) (n : ℕ) :
    HasDegreeGE (signedWeight s) ((n : ℤ) * signedHeight s r)
      (specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
  intro i j hij
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := dividedPower_degree r n i j hint
  have he : signedWeight s i - signedWeight s j = (n : ℤ) * signedHeight s r := by
    dsimp only [signedWeight, signedHeight]
    rw [← mul_sub, hd]
    ring
  omega

private lemma rootCurve_hasDegreeGE (s : ℤ) (r : F4Chevalley.Root)
    (hr : 0 < signedHeight s r) (t : F) :
    HasDegreeGE (signedWeight s) (signedHeight s r)
      ((F4Chevalley.rootCurve r t).val - 1) := by
  have hs (n : ℕ) (hn : 0 < n) (u : F) :
      HasDegreeGE (signedWeight s) (signedHeight s r)
        (u • specializeMatrix (S := F)
          (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    apply ((dividedPower_hasDegreeGE s r n).mono ?_).smul
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [F4Chevalley.rootCurve_matrix_formula]
  have he : (1 + t • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact ((hs 1 (by decide) t).add (hs 2 (by decide) (t ^ 2))).add
    (hs 3 (by decide) (t ^ 3))

private lemma rootCurve_sub_hasDegreeGE (s : ℤ) (r : F4Chevalley.Root)
    (hr : 0 < signedHeight s r) (t u : F) :
    HasDegreeGE (signedWeight s) (signedHeight s r)
      ((F4Chevalley.rootCurve r t).val - (F4Chevalley.rootCurve r u).val) := by
  have h := (rootCurve_hasDegreeGE s r hr t).sub (rootCurve_hasDegreeGE s r hr u)
  have he : ((F4Chevalley.rootCurve r t).val - 1) -
      ((F4Chevalley.rootCurve r u).val - 1) =
      (F4Chevalley.rootCurve r t).val - (F4Chevalley.rootCurve r u).val := by abel
  rwa [he] at h

variable [CharP F 2]

private lemma cast_eq_of_binary_cast_eq (a b : ℤ)
    (h : (a : CoefficientField 0) = (b : CoefficientField 0)) : (a : F) = (b : F) := by
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff F 2]
  rwa [← sub_eq_zero, ← Int.cast_sub,
    CharP.intCast_eq_zero_iff (CoefficientField 0) 2] at h

private lemma dividedPower_one_cartan (s r : F4Chevalley.Root)
    (j : typeF4RootPairing_base.support) :
    specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower s 1) (Sum.inr r) (Sum.inl j) =
      if r = s then (typeF4RootPairing.pairingIn ℤ s j : F) else 0 := by
  classical
  have h := congrFun
    (WordRelations.Faithfulness.Adjoint.PositiveSimple.coordinateOperator_mulVec_cartan 0 s j)
    (Sum.inr r)
  rw [Matrix.mulVec_single_one] at h
  have hh : (F4Chevalley.integralOperators.rootDividedPower s 1 (Sum.inr r) (Sum.inl j) :
      CoefficientField 0) =
      if r = s then (typeF4RootPairing.pairingIn ℤ s j : CoefficientField 0) else 0 := by
    simpa [F4Chevalley.dividedPower_one, specializeMatrix,
      WordRelations.Faithfulness.Adjoint.coordinateOperator, Pi.single_apply] using h
  change (_ : F) = _
  split_ifs with hrs
  · exact cast_eq_of_binary_cast_eq (F := F) _ _ (by simpa [hrs] using hh)
  · simpa only [specializeMatrix, Matrix.map_apply, Int.coe_castRingHom, Int.cast_zero] using
      cast_eq_of_binary_cast_eq (F := F) _ 0 (by simpa [hrs] using hh)

private lemma exists_detecting_coroot (r : F4Chevalley.Root) :
    ∃ j : typeF4RootPairing_base.support,
      (typeF4RootPairing.pairingIn ℤ r j : F) ≠ 0 := by
  obtain ⟨j, hj⟩ :=
    WordRelations.Faithfulness.Adjoint.PositiveSimple.exists_pairingIn_cast_ne_zero 0 r
  refine ⟨j, ?_⟩
  rw [Ne, CharP.intCast_eq_zero_iff F 2]
  simpa only [Ne, CharP.intCast_eq_zero_iff (CoefficientField 0) 2] using hj

private lemma rootCurve_sub_cartan (s : ℤ) (r t : F4Chevalley.Root)
    (ht : 0 < signedHeight s t) (hrt : signedHeight s r ≤ signedHeight s t)
    (a b : F) (j : typeF4RootPairing_base.support) :
    ((F4Chevalley.rootCurve t a).val - (F4Chevalley.rootCurve t b).val)
        (Sum.inr r) (Sum.inl j) =
      if r = t then (a - b) * (typeF4RootPairing.pairingIn ℤ r j : F) else 0 := by
  classical
  have hn (n : ℕ) (hn : 2 ≤ n) :
      specializeMatrix (S := F)
        (F4Chevalley.integralOperators.rootDividedPower t n)
          (Sum.inr r) (Sum.inl j) = 0 := by
    apply dividedPower_hasDegreeGE s t n
    rw [signedWeight_root, signedWeight_cartan, sub_zero]
    have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  simp only [Matrix.sub_apply, F4Chevalley.rootCurve_matrix_formula, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, hn 2 (by decide), hn 3 (by decide),
    dividedPower_one_cartan (F := F), mul_zero, add_zero]
  by_cases h : r = t
  · subst t
    simp only [ite_true]
    ring
  · simp [h]

variable [IsAlgClosed F]

omit [CharP F 2] in
private lemma rootProduct_matrix {n : ℕ} (p : Fin n → F4Chevalley.Root)
    (a : Fin n → F) :
    (pointMatrix (rootProduct p a)).val =
      (List.ofFn fun i => (F4Chevalley.rootCurve (p i) (a i)).val).prod := by
  let f : Variety.Point (F4Chevalley.Carrier (k := F)) →*
      Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F :=
    (Units.coeHom _).comp pointMatrix
  change f (rootProduct p a) = _
  rw [rootProduct, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact congrArg Units.val (pointMatrix_root (p i) (a i))

omit [CharP F 2] in
private lemma rootProduct_hasDegreeGE {n : ℕ} (s : ℤ)
    (p : Fin n → F4Chevalley.Root) (hp : ∀ i, 0 < signedHeight s (p i)) (a : Fin n → F) :
    HasDegreeGE (signedWeight s) 1 ((pointMatrix (rootProduct p a)).val - 1) := by
  rw [rootProduct_matrix]
  have h := unipotent_list_prod (signedWeight s)
    (fun i => (F4Chevalley.rootCurve (p i) (a i)).val) (List.ofFn id)
    (fun i _ => (rootCurve_hasDegreeGE s (p i) (hp i) (a i)).mono (by have := hp i; omega))
  simpa only [List.map_ofFn, Function.comp_id] using h

private lemma rootProduct_cartan_sub {n : ℕ} (s : ℤ)
    (p : Fin n → F4Chevalley.Root) (hp : ∀ i, 0 < signedHeight s (p i))
    (hinj : Function.Injective p) (a b : Fin n → F) (r : Fin n)
    (hab : ∀ i, signedHeight s (p i) < signedHeight s (p r) → a i = b i)
    (j : typeF4RootPairing_base.support) :
    (pointMatrix (rootProduct p a)).val (Sum.inr (p r)) (Sum.inl j) -
      (pointMatrix (rootProduct p b)).val (Sum.inr (p r)) (Sum.inl j) =
        (a r - b r) * (typeF4RootPairing.pairingIn ℤ (p r) j : F) := by
  classical
  let A i := (F4Chevalley.rootCurve (p i) (a i)).val
  let B i := (F4Chevalley.rootCurve (p i) (b i)).val
  have hA i : HasDegreeGE (signedWeight s) 1 (A i - 1) :=
    (rootCurve_hasDegreeGE s (p i) (hp i) (a i)).mono (by have := hp i; omega)
  have hB i : HasDegreeGE (signedWeight s) 1 (B i - 1) :=
    (rootCurve_hasDegreeGE s (p i) (hp i) (b i)).mono (by have := hp i; omega)
  have hD i : HasDegreeGE (signedWeight s) (signedHeight s (p r)) (A i - B i) := by
    by_cases hi : signedHeight s (p i) < signedHeight s (p r)
    · dsimp only [A, B]
      rw [hab i hi, sub_self]
      exact HasDegreeGE.zero _ _
    · exact (rootCurve_sub_hasDegreeGE s (p i) (hp i) (a i) (b i)).mono (by omega)
  have h := (list_prod_difference (signedWeight s) (signedHeight s (p r)) A B
    (List.ofFn id) (fun i _ => hA i) (fun i _ => hB i) (fun i _ => hD i)).2
  have he := h (Sum.inr (p r)) (Sum.inl j) (by
    rw [signedWeight_root, signedWeight_cartan]
    omega)
  have hf i : (A i - B i) (Sum.inr (p r)) (Sum.inl j) =
      if i = r then (a r - b r) * (typeF4RootPairing.pairingIn ℤ (p r) j : F) else 0 := by
    by_cases hi : signedHeight s (p i) < signedHeight s (p r)
    · have hne : i ≠ r := by rintro rfl; omega
      simp [A, B, hab i hi, hne]
    · have hh := rootCurve_sub_cartan s (p r) (p i) (hp i) (by omega) (a i) (b i) j
      by_cases hir : i = r
      · subst i
        simpa only [ite_true] using hh
      · have hri : p r ≠ p i := fun h => hir (hinj h).symm
        simpa only [if_neg hir, if_neg hri] using hh
  have hsum : ((List.ofFn id).map fun i => A i - B i).sum
      (Sum.inr (p r)) (Sum.inl j) =
      (a r - b r) * (typeF4RootPairing.pairingIn ℤ (p r) j : F) := by
    simp only [List.map_ofFn, Function.comp_apply, id_eq, List.sum_ofFn, Matrix.sum_apply, hf]
    simp
  simp only [List.map_ofFn, Function.comp_id] at hsum
  simp only [Matrix.sub_apply, List.map_ofFn, Function.comp_id] at he
  rw [hsum] at he
  rw [rootProduct_matrix, rootProduct_matrix]
  exact sub_eq_zero.mp he

omit [CharP F 2] in
private lemma rootProduct_entries (S : Subfield F) {n : ℕ}
    (p : Fin n → F4Chevalley.Root) (a : Fin n → F) (ha : ∀ i, a i ∈ S) :
    ∀ i j, (pointMatrix (rootProduct p a)).val i j ∈ S := by
  classical
  have hone : ∀ i j, (1 : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F) i j ∈ S := by
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> first | exact S.one_mem | exact S.zero_mem
  have hroot (k : Fin n) : ∀ i j, (F4Chevalley.rootCurve (p k) (a k)).val i j ∈ S := by
    intro i j
    have hint (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ) :
        specializeMatrix (S := F) A i j ∈ S := S.intCast_mem _
    rw [F4Chevalley.rootCurve_matrix_formula]
    exact S.add_mem (S.add_mem (S.add_mem (hone i j) (S.mul_mem (ha k) (hint _)))
      (S.mul_mem (S.pow_mem (ha k) 2) (hint _))) (S.mul_mem (S.pow_mem (ha k) 3) (hint _))
  have hlist (l : List (Fin n)) : ∀ i j,
      (l.map fun k => (F4Chevalley.rootCurve (p k) (a k)).val).prod i j ∈ S := by
    induction l with
    | nil => exact hone
    | cons k l ih =>
      intro i j
      exact S.sum_mem fun q _ => S.mul_mem (hroot k i q) (ih q j)
  rw [rootProduct_matrix]
  simpa only [List.map_ofFn, Function.comp_id] using hlist (List.ofFn id)

private lemma parameters_mem_of_entries (S : Subfield F) {n : ℕ} (s : ℤ)
    (p : Fin n → F4Chevalley.Root) (hp : ∀ i, 0 < signedHeight s (p i))
    (hinj : Function.Injective p) (a : Fin n → F)
    (ha : ∀ i j, (pointMatrix (rootProduct p a)).val i j ∈ S) :
    ∀ i, a i ∈ S := by
  classical
  have recover : ∀ d (r : Fin n), (signedHeight s (p r)).toNat = d → a r ∈ S := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro r hr
      let b : Fin n → F := fun i => if signedHeight s (p i) < signedHeight s (p r) then a i else 0
      have hb : ∀ i, b i ∈ S := by
        intro i
        dsimp only [b]
        split_ifs with hi
        · exact ih (signedHeight s (p i)).toNat (by have := hp i; have := hp r; omega) i rfl
        · exact S.zero_mem
      have hbr : b r = 0 := by simp [b]
      obtain ⟨j, hj⟩ := exists_detecting_coroot (F := F) (p r)
      have he := rootProduct_cartan_sub s p hp hinj a b r
        (fun i hi => by simp [b, hi]) j
      have hm := S.sub_mem (ha (Sum.inr (p r)) (Sum.inl j))
        (rootProduct_entries S p b hb (Sum.inr (p r)) (Sum.inl j))
      rw [he, hbr, sub_zero] at hm
      simpa only [mul_div_cancel_right₀ _ hj] using S.div_mem hm
        (S.intCast_mem (typeF4RootPairing.pairingIn ℤ (p r) j))
  exact fun r => recover _ r rfl

private lemma exists_monotone_basis_order :
    ∃ e : Fin (Fintype.card F4Chevalley.BasisIndex) ≃ F4Chevalley.BasisIndex,
      Monotone (fun i => cartanBasisDegree (e i)) := by
  classical
  let key (i : F4Chevalley.BasisIndex) :=
    toLex (cartanBasisDegree i, Fintype.equivFin F4Chevalley.BasisIndex i)
  have hk : Function.Injective key := by
    intro i j h
    exact (Fintype.equivFin F4Chevalley.BasisIndex).injective (congrArg (fun x => (ofLex x).2) h)
  let ord : LinearOrder F4Chevalley.BasisIndex := LinearOrder.lift' key hk
  let e := @Fintype.orderIsoFinOfCardEq F4Chevalley.BasisIndex ord _ _ rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have hh : key (e i) ≤ key (e j) :=
    (@OrderIso.le_iff_le _ _ _ ord.toLE e i j).mpr hij
  exact Prod.Lex.monotone_fst (key (e i)) (key (e j)) hh

/-- The single basis order used for both opposite unipotent factors. It orders
Cartan and root vectors by increasing integral root height, breaking ties by
an arbitrary finite enumeration. -/
public noncomputable def unipotentBasisOrder :
    Fin (Fintype.card F4Chevalley.BasisIndex) ≃ F4Chevalley.BasisIndex :=
  Classical.choose exists_monotone_basis_order

private lemma unipotentBasisOrder_monotone :
    Monotone (fun i => cartanBasisDegree (unipotentBasisOrder i)) :=
  Classical.choose_spec exists_monotone_basis_order

private lemma positive_height (o : PositiveOrdering) (i : Fin 24) :
    0 < signedHeight 1 (o i).val := by
  change 0 < 1 * corootHeight (o i).val
  rw [one_mul, corootHeight_eq_height (o i).property]
  exact (o i).property

private lemma negative_height (o : PositiveOrdering) (i : Fin 24) :
    0 < signedHeight (-1) (-(o i).val) := by
  simpa only [signedHeight, corootHeight_neg, neg_mul, one_mul, neg_neg] using
    positive_height o i

omit [CharP F 2] in
/-- Positive products are lower triangular in the common height order. -/
public theorem positive_rootProduct_lower (o : PositiveOrdering) (a : Fin 24 → F)
    (i j : Fin (Fintype.card F4Chevalley.BasisIndex)) (hij : i < j) :
    (pointMatrix (rootProduct (fun k => (o k).val) a)).val
      (unipotentBasisOrder i) (unipotentBasisOrder j) = 0 := by
  have h := rootProduct_hasDegreeGE 1 (fun k => (o k).val) (positive_height o) a
  have hle := unipotentBasisOrder_monotone hij.le
  dsimp only at hle
  have he := h (unipotentBasisOrder i) (unipotentBasisOrder j) (by
    simp only [signedWeight, one_mul]; omega)
  have hne : unipotentBasisOrder i ≠ unipotentBasisOrder j :=
    fun h => (ne_of_lt hij) (unipotentBasisOrder.injective h)
  simpa only [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] using he

omit [CharP F 2] in
/-- Negative products are upper triangular in exactly the same basis order. -/
public theorem negative_rootProduct_upper (o : PositiveOrdering) (a : Fin 24 → F)
    (i j : Fin (Fintype.card F4Chevalley.BasisIndex)) (hij : j < i) :
    (pointMatrix (rootProduct (fun k => -(o k).val) a)).val
      (unipotentBasisOrder i) (unipotentBasisOrder j) = 0 := by
  have h := rootProduct_hasDegreeGE (-1) (fun k => -(o k).val) (negative_height o) a
  have hle := unipotentBasisOrder_monotone hij.le
  dsimp only at hle
  have he := h (unipotentBasisOrder i) (unipotentBasisOrder j) (by
    simp only [signedWeight, neg_mul, one_mul]; omega)
  have hne : unipotentBasisOrder i ≠ unipotentBasisOrder j :=
    fun h => (ne_of_gt hij) (unipotentBasisOrder.injective h)
  simpa only [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] using he

omit [CharP F 2] in
/-- All positive-product diagonal entries are one. -/
public theorem positive_rootProduct_diagonal (o : PositiveOrdering) (a : Fin 24 → F)
    (i : Fin (Fintype.card F4Chevalley.BasisIndex)) :
    (pointMatrix (rootProduct (fun k => (o k).val) a)).val
      (unipotentBasisOrder i) (unipotentBasisOrder i) = 1 := by
  have h := rootProduct_hasDegreeGE 1 (fun k => (o k).val) (positive_height o) a
  have he := h (unipotentBasisOrder i) (unipotentBasisOrder i) (by omega)
  simpa only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] using he

omit [CharP F 2] in
/-- All negative-product diagonal entries are one. -/
public theorem negative_rootProduct_diagonal (o : PositiveOrdering) (a : Fin 24 → F)
    (i : Fin (Fintype.card F4Chevalley.BasisIndex)) :
    (pointMatrix (rootProduct (fun k => -(o k).val) a)).val
      (unipotentBasisOrder i) (unipotentBasisOrder i) = 1 := by
  have h := rootProduct_hasDegreeGE (-1) (fun k => -(o k).val) (negative_height o) a
  have he := h (unipotentBasisOrder i) (unipotentBasisOrder i) (by omega)
  simpa only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] using he

/-- Every positive root parameter descends when all literal matrix entries do. -/
public theorem positive_parameters_mem_range {m : ℕ} (f : CoefficientField m →+* F)
    (o : PositiveOrdering) (a : Fin 24 → F)
    (ha : ∀ i j, (pointMatrix (rootProduct (fun k => (o k).val) a)).val i j ∈ f.range) :
    ∀ i, a i ∈ f.range :=
  parameters_mem_of_entries f.fieldRange 1 (fun k => (o k).val) (positive_height o)
    (Subtype.val_injective.comp o.injective) a ha

/-- Every negative root parameter descends, for any ordering of the positive roots. -/
public theorem negative_parameters_mem_range {m : ℕ} (f : CoefficientField m →+* F)
    (o : PositiveOrdering) (a : Fin 24 → F)
    (ha : ∀ i j, (pointMatrix (rootProduct (fun k => -(o k).val) a)).val i j ∈ f.range) :
    ∀ i, a i ∈ f.range :=
  parameters_mem_of_entries f.fieldRange (-1) (fun k => -(o k).val) (negative_height o)
    (neg_injective.comp (Subtype.val_injective.comp o.injective)) a ha

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
