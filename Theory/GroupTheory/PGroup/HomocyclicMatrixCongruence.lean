module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Deep involutions in homocyclic two-groups

An involutory automorphism of `(ZMod (2^n))²`, for `n ≥ 3`, fixing the
four-torsion has coordinate matrix `I + 2^(n-1) M`. It commutes with every
automorphism fixing the two-torsion, and can invert only two-torsion elements.
The final transport theorem applies these facts to any group equipped with
an equivalence to the rank-two homocyclic model.

The proof is an elementary congruence calculation. Fixing four-torsion gives
`A - I = 4 C`. The identity `A² = I` gives
`2 (A - I) (I + 2 C) = 0`. Since `2 C` is nilpotent, `I + 2 C` is a unit,
so `2 (A - I) = 0`. Scalar cancellation in `ZMod` gives the stated matrix.
The linear argument works for any finite coordinate index.

This is a self-contained proof of the deep-involution coordinate lemma used
in the Thompson N-group development. The ring-theoretic input is Mathlib's
`IsNilpotent.isUnit_one_add`; no external proof text is ported.
-/

namespace HomocyclicMatrixCongruence

private lemma scalar_factor {N : ℕ} [NeZero N] (a b : ℕ) (ha : 0 < a) (hN : N = a * b)
    (x : ZMod N) (hx : (a : ZMod N) * x = 0) : ∃ y, x = (b : ZMod N) * y := by
  have h : a * b ∣ a * x.val := by
    rw [← hN]
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa using hx
  have hb : b ∣ x.val := Nat.dvd_of_mul_dvd_mul_left ha h
  obtain ⟨k, hk⟩ := hb
  refine ⟨k, ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x, hk]
  simp

private lemma ring_two_sub {R : Type*} [Ring R] (n : ℕ) (hn : (2 : R) ^ n = 0)
    (A C : R) (hA : A = 1 + 4 * C) (hAA : A ^ 2 = 1) : 2 * (A - 1) = 0 := by
  have hu : IsUnit (1 + 2 * C) :=
    ((Commute.ofNat_left 2 C).isNilpotent_mul_right ⟨n, hn⟩).isUnit_one_add
  apply hu.mul_left_eq_zero.mp
  calc
    2 * (A - 1) * (1 + 2 * C) = A ^ 2 - 1 := by rw [hA]; noncomm_ring
    _ = 0 := by rw [hAA]; simp

private lemma matrix_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} [NeZero N]
    (a b : ℕ) (ha : 0 < a) (hN : N = a * b) (D : Matrix ι ι (ZMod N))
    (hD : (a : ZMod N) • D = 0) : ∃ C, D = (b : ZMod N) • C := by
  have hentry (i j : ι) : ∃ y, D i j = (b : ZMod N) * y :=
    scalar_factor a b ha hN (D i j) (congrFun (congrFun hD i) j)
  choose C hC using hentry
  exact ⟨C, Matrix.ext fun i j => hC i j⟩

private lemma matrix_two_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (A : Matrix ι ι (ZMod (2 ^ n)))
    (hA : ∃ C, A - 1 = (4 : ZMod (2 ^ n)) • C) (hAA : A ^ 2 = 1) :
    (2 : ZMod (2 ^ n)) • (A - 1) = 0 := by
  obtain ⟨C, hC⟩ := hA
  have heq : A = 1 + 4 * C := by
    have : (4 : ZMod (2 ^ n)) • C = 4 * C := by rw [Algebra.smul_def, map_ofNat]
    rw [this] at hC
    exact (sub_eq_iff_eq_add.mp hC).trans (add_comm _ _)
  have hn : (2 : Matrix ι ι (ZMod (2 ^ n))) ^ n = 0 := by
    have hz : (2 : ZMod (2 ^ n)) ^ n = 0 := by
      exact_mod_cast (ZMod.natCast_eq_zero_iff (2 ^ n) (2 ^ n)).mpr dvd_rfl
    have := congrArg (algebraMap (ZMod (2 ^ n)) (Matrix ι ι (ZMod (2 ^ n)))) hz
    simpa only [map_pow, map_ofNat, map_zero] using this
  rw [Algebra.smul_def, map_ofNat]
  exact ring_two_sub n hn A C heq hAA

private lemma linear_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} [NeZero N]
    (a b : ℕ) (ha : 0 < a) (hN : N = a * b) (L : Module.End (ZMod N) (ι → ZMod N))
    (hL : ∀ x, (b : ZMod N) • x = 0 → L x = x) :
    ∃ C, LinearMap.toMatrix' L - 1 = (b : ZMod N) • C := by
  have hlin : (a : ZMod N) • (L - 1) = 0 := by
    apply LinearMap.ext
    intro x
    funext i
    have hx : (b : ZMod N) • ((a : ZMod N) • x) = 0 := by
      rw [smul_smul, ← Nat.cast_mul, Nat.mul_comm b a, ← hN]
      simp
    have hh := hL ((a : ZMod N) • x) hx
    rw [map_smul] at hh
    have : (a : ZMod N) • (L x - x) = 0 := by rw [smul_sub, hh, sub_self]
    exact congrFun this i
  apply matrix_factor a b ha hN
  have hh := congrArg (LinearMap.toMatrix' (R := ZMod N) (n := ι) (m := ι)) hlin
  simpa using hh

/-- The displacement of an involutory linear map fixing four-torsion is killed by two. -/
public lemma linearMap_two_smul_sub_one_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 2 ≤ n) (L : Module.End (ZMod (2 ^ n)) (ι → ZMod (2 ^ n)))
    (hLL : L ^ 2 = 1) (hL : ∀ x, (4 : ZMod (2 ^ n)) • x = 0 → L x = x) :
    (2 : ZMod (2 ^ n)) • (L - 1) = 0 := by
  have hN : 2 ^ n = 2 ^ (n - 2) * 4 := by
    conv_rhs => rw [show 4 = 2 ^ 2 from rfl, ← pow_add, Nat.sub_add_cancel hn]
  have hfac := linear_factor (2 ^ (n - 2)) 4 (by positivity) hN L hL
  have hmat : (LinearMap.toMatrix' L) ^ 2 = 1 := by
    rw [pow_two, ← LinearMap.toMatrix'_mul, ← pow_two, hLL, LinearMap.toMatrix'_one]
  have htwo := matrix_two_sub n (LinearMap.toMatrix' L) hfac hmat
  apply LinearMap.toMatrix'.injective
  simpa using htwo

/-- The coordinate matrix of a deep involution is congruent to the identity modulo `2 ^ (n - 1)`. -/
public lemma linearMap_matrix_eq_one_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 3 ≤ n) (L : Module.End (ZMod (2 ^ n)) (ι → ZMod (2 ^ n)))
    (hLL : L ^ 2 = 1) (hL : ∀ x, (4 : ZMod (2 ^ n)) • x = 0 → L x = x) :
    ∃ M, LinearMap.toMatrix' L = 1 + (2 ^ (n - 1) : ZMod (2 ^ n)) • M := by
  have htwo := linearMap_two_smul_sub_one_eq_zero n (by omega) L hLL hL
  have hN : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hmat : (2 : ZMod (2 ^ n)) • (LinearMap.toMatrix' L - 1) = 0 := by
    simpa using congrArg (LinearMap.toMatrix' (R := ZMod (2 ^ n))) htwo
  obtain ⟨M, hM⟩ := matrix_factor 2 (2 ^ (n - 1)) (by decide) hN (LinearMap.toMatrix' L - 1) hmat
  refine ⟨M, ?_⟩
  rw [Nat.cast_pow, Nat.cast_ofNat] at hM
  exact (sub_eq_iff_eq_add.mp hM).trans (add_comm _ _)

private lemma linear_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 3 ≤ n) (L K : Module.End (ZMod (2 ^ n)) (ι → ZMod (2 ^ n)))
    (hLL : L ^ 2 = 1) (hL : ∀ x, (4 : ZMod (2 ^ n)) • x = 0 → L x = x)
    (hK : ∀ x, (2 : ZMod (2 ^ n)) • x = 0 → K x = x) : Commute L K := by
  have htwo := linearMap_two_smul_sub_one_eq_zero n (by omega) L hLL hL
  have hN : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  obtain ⟨C, hC⟩ := linear_factor (2 ^ (n - 1)) 2 (by positivity) hN K hK
  let A := LinearMap.toMatrix' L
  let B := LinearMap.toMatrix' K
  have hA : (2 : ZMod (2 ^ n)) • (A - 1) = 0 := by
    simpa [A] using congrArg (LinearMap.toMatrix' (R := ZMod (2 ^ n))) htwo
  have hab : (A - 1) * (B - 1) = 0 := by
    change (A - 1) * (LinearMap.toMatrix' K - 1) = 0
    rw [hC, Nat.cast_ofNat, Matrix.mul_smul, ← Matrix.smul_mul, hA, zero_mul]
  have hba : (B - 1) * (A - 1) = 0 := by
    change (LinearMap.toMatrix' K - 1) * (A - 1) = 0
    rw [hC, Nat.cast_ofNat, Matrix.smul_mul, ← Matrix.mul_smul, hA, mul_zero]
  have hh : A * B - B * A = 0 := by
    calc
      A * B - B * A = (A - 1) * (B - 1) - (B - 1) * (A - 1) := by noncomm_ring
      _ = 0 := by rw [hab, hba, sub_self]
  apply LinearMap.toMatrix'.injective
  simpa only [LinearMap.toMatrix'_mul] using sub_eq_zero.mp hh

private lemma linear_inverted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 3 ≤ n) (L : Module.End (ZMod (2 ^ n)) (ι → ZMod (2 ^ n)))
    (hLL : L ^ 2 = 1) (hL : ∀ x, (4 : ZMod (2 ^ n)) • x = 0 → L x = x)
    (x : ι → ZMod (2 ^ n)) (hx : L x = -x) : (2 : ZMod (2 ^ n)) • x = 0 := by
  have htwo := linearMap_two_smul_sub_one_eq_zero n (by omega) L hLL hL
  have hx4 : (4 : ZMod (2 ^ n)) • x = 0 := by
    funext i
    have hh := congrFun (LinearMap.congr_fun htwo x) i
    change (2 : ZMod (2 ^ n)) * (L x i - x i) = 0 at hh
    rw [hx] at hh
    change (4 : ZMod (2 ^ n)) * x i = 0
    change (2 : ZMod (2 ^ n)) * (-x i - x i) = 0 at hh
    linear_combination -hh
  have hh := hL x hx4
  funext i
  have hi := congrFun (hx.symm.trans hh) i
  change -x i = x i at hi
  change (2 : ZMod (2 ^ n)) * x i = 0
  linear_combination -hi

private noncomputable def coordinateLinear {ι G : Type*} [Group G] (N : ℕ)
    (e : Multiplicative (ι → ZMod N) ≃* G) (A : MulAut G) :
    Module.End (ZMod N) (ι → ZMod N) :=
  AddMonoidHom.toZModLinearMap N {
    toFun := fun x => (e.symm (A (e (Multiplicative.ofAdd x)))).toAdd
    map_zero' := by change (e.symm (A (e 1))).toAdd = 0; simp
    map_add' := by
      intro x y
      change (e.symm (A (e (Multiplicative.ofAdd x * Multiplicative.ofAdd y)))).toAdd = _
      simp only [map_mul, toAdd_mul] }

private lemma coordinateLinear_apply {ι G : Type*} [Group G] (N : ℕ)
    (e : Multiplicative (ι → ZMod N) ≃* G) (A : MulAut G) (x : ι → ZMod N) :
    coordinateLinear N e A x = (e.symm (A (e (Multiplicative.ofAdd x)))).toAdd := rfl

private lemma coordinateLinear_sq {ι G : Type*} [Group G] (N : ℕ)
    (e : Multiplicative (ι → ZMod N) ≃* G) (A : MulAut G) (hA : A ^ 2 = 1) :
    (coordinateLinear N e A) ^ 2 = 1 := by
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun f : MulAut G => f (e (Multiplicative.ofAdd x))) hA
  simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at hh
  simp only [pow_two, Module.End.mul_apply, coordinateLinear_apply,
    ofAdd_toAdd, MulEquiv.apply_symm_apply, hh, MulEquiv.symm_apply_apply,
    toAdd_ofAdd, Module.End.one_apply]

private lemma coordinateLinear_fixes {ι G : Type*} [Group G] (N k : ℕ)
    (e : Multiplicative (ι → ZMod N) ≃* G) (A : MulAut G)
    (hA : ∀ x, x ^ k = 1 → A x = x) :
    ∀ x, (k : ZMod N) • x = 0 → coordinateLinear N e A x = x := by
  intro x hx
  have hx' : (e (Multiplicative.ofAdd x)) ^ k = 1 := by
    rw [← map_pow]
    have hh : (Multiplicative.ofAdd x) ^ k = 1 := by
      apply Multiplicative.toAdd.injective
      change k • x = 0
      simpa only [Nat.cast_smul_eq_nsmul] using hx
    rw [hh, map_one]
  rw [coordinateLinear_apply, hA _ hx', MulEquiv.symm_apply_apply]
  rfl

private lemma coordinateLinear_injective {ι G : Type*} [Group G] (N : ℕ)
    (e : Multiplicative (ι → ZMod N) ≃* G) :
    Function.Injective (coordinateLinear N e) := by
  intro A B h
  ext g
  obtain ⟨x, rfl⟩ := e.surjective g
  have hh := LinearMap.congr_fun h x.toAdd
  simp only [coordinateLinear_apply, ofAdd_toAdd] at hh
  exact e.symm.injective (Multiplicative.toAdd.injective hh)

private lemma coordinateLinear_mul {ι G : Type*} [Group G] (N : ℕ)
    (e : Multiplicative (ι → ZMod N) ≃* G) (A B : MulAut G) :
    coordinateLinear N e (A * B) = coordinateLinear N e A * coordinateLinear N e B := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, coordinateLinear_apply, MulAut.mul_apply,
    ofAdd_toAdd, MulEquiv.apply_symm_apply]

/-- Transport the commutation conclusion through any finite homocyclic coordinate equivalence. -/
public lemma commute_of_equiv {ι G : Type*} [Fintype ι] [DecidableEq ι] [Group G]
    (n : ℕ) (hn : 3 ≤ n) (e : Multiplicative (ι → ZMod (2 ^ n)) ≃* G)
    (A B : MulAut G) (hAA : A ^ 2 = 1) (hA : ∀ x, x ^ 4 = 1 → A x = x)
    (hB : ∀ x, x ^ 2 = 1 → B x = x) : Commute A B := by
  apply coordinateLinear_injective (2 ^ n) e
  simp only [coordinateLinear_mul]
  exact linear_commute n hn _ _ (coordinateLinear_sq _ e A hAA)
    (by simpa only [Nat.cast_ofNat] using coordinateLinear_fixes _ 4 e A hA)
    (by simpa only [Nat.cast_ofNat] using coordinateLinear_fixes _ 2 e B hB)

/-- An element inverted by a deep involution has square one, in arbitrary homocyclic coordinates. -/
public lemma sq_eq_one_of_inverted_of_equiv {ι G : Type*} [Fintype ι] [DecidableEq ι] [Group G]
    (n : ℕ) (hn : 3 ≤ n) (e : Multiplicative (ι → ZMod (2 ^ n)) ≃* G)
    (A : MulAut G) (hAA : A ^ 2 = 1) (hA : ∀ x, x ^ 4 = 1 → A x = x)
    (x : G) (hx : A x = x⁻¹) : x ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := e.surjective x
  have hi : coordinateLinear (2 ^ n) e A v.toAdd = -v.toAdd := by
    rw [coordinateLinear_apply, ofAdd_toAdd, hx, map_inv, MulEquiv.symm_apply_apply]
    rfl
  have htwo := linear_inverted n hn _ (coordinateLinear_sq _ e A hAA)
    (by simpa only [Nat.cast_ofNat] using coordinateLinear_fixes _ 4 e A hA) _ hi
  rw [← map_pow]
  have hv : v ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    change (2 : ℕ) • v.toAdd = 0
    simpa only [← Nat.cast_smul_eq_nsmul (ZMod (2 ^ n)), Nat.cast_ofNat] using htwo
  rw [hv, map_one]

/-- The standard ordered two-coordinate equivalence to the product of cyclic groups. -/
public noncomputable def rankTwoEquiv (n : ℕ) :
    Multiplicative (Fin 2 → ZMod (2 ^ n)) ≃*
      (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) :=
  (AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow (ZMod (2 ^ n)) (ZMod (2 ^ n))).toAddEquiv).trans
    (MulEquiv.prodMultiplicative _ _)

private lemma linear_fixes_of_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (b : ZMod N) (L : Module.End (ZMod N) (ι → ZMod N))
    (hL : ∃ C, LinearMap.toMatrix' L = 1 + b • C) :
    ∀ x, b • x = 0 → L x = x := by
  obtain ⟨C, hC⟩ := hL
  intro x hx
  rw [← LinearMap.toMatrix'_mulVec L x, hC, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_smul, hx, Matrix.mulVec_zero, add_zero]

private lemma coordinateLinear_fixes_iff {ι G : Type*} [Group G] (N k : ℕ)
    (e : Multiplicative (ι → ZMod N) ≃* G) (A : MulAut G) :
    (∀ x, (k : ZMod N) • x = 0 → coordinateLinear N e A x = x) ↔
      (∀ x, x ^ k = 1 → A x = x) := by
  constructor
  · intro h x hx
    obtain ⟨v, rfl⟩ := e.surjective x
    have hv : v ^ k = 1 := e.injective (by simpa only [map_pow, map_one] using hx)
    have hz : (k : ZMod N) • v.toAdd = 0 := by
      rw [Nat.cast_smul_eq_nsmul]
      exact congrArg Multiplicative.toAdd hv
    have hh := h v.toAdd hz
    rw [coordinateLinear_apply, ofAdd_toAdd] at hh
    exact e.symm.injective (by simpa only [MulEquiv.symm_apply_apply] using
      Multiplicative.toAdd.injective hh)
  · exact coordinateLinear_fixes N k e A

/-- The rank-two homocyclic group of exponent `2 ^ n`. -/
public abbrev RankTwo (n : ℕ) := Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))

/-- The matrix of an automorphism in the standard ordered additive coordinates. -/
public noncomputable def autMatrix (n : ℕ) (A : MulAut (RankTwo n)) :
    Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n)) :=
  LinearMap.toMatrix' (coordinateLinear (2 ^ n) (rankTwoEquiv n) A)

/-- Classification of involutory rank-two automorphisms fixing every element of fourth power one. -/
public lemma matrix_eq_one_add (n : ℕ) (hn : 3 ≤ n) (A : MulAut (RankTwo n))
    (hAA : A ^ 2 = 1) (hA : ∀ x, x ^ 4 = 1 → A x = x) :
    ∃ M, autMatrix n A = 1 + (2 ^ (n - 1) : ZMod (2 ^ n)) • M := by
  exact linearMap_matrix_eq_one_add n hn _ (coordinateLinear_sq _ _ A hAA)
    (by simpa only [Nat.cast_ofNat] using coordinateLinear_fixes _ 4 (rankTwoEquiv n) A hA)

/-- Fixing all elements of square one is equivalent to matrix congruence to the identity modulo two. -/
public lemma fixes_involutions_iff (n : ℕ) (hn : 1 ≤ n) (B : MulAut (RankTwo n)) :
    (∀ x, x ^ 2 = 1 → B x = x) ↔ ∃ M, autMatrix n B = 1 + (2 : ZMod (2 ^ n)) • M := by
  constructor
  · intro hB
    have hN : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    obtain ⟨M, hM⟩ := linear_factor (2 ^ (n - 1)) 2 (by positivity) hN
      (coordinateLinear (2 ^ n) (rankTwoEquiv n) B)
      (coordinateLinear_fixes _ 2 (rankTwoEquiv n) B hB)
    refine ⟨M, ?_⟩
    rw [Nat.cast_ofNat] at hM
    exact (sub_eq_iff_eq_add.mp hM).trans (add_comm _ _)
  · intro hB
    apply (coordinateLinear_fixes_iff (2 ^ n) 2 (rankTwoEquiv n) B).mp
    simpa only [Nat.cast_ofNat] using linear_fixes_of_matrix (2 : ZMod (2 ^ n)) _ hB

/-- A deep involution commutes with every automorphism fixing all elements of square one. -/
public lemma aut_commute (n : ℕ) (hn : 3 ≤ n) (A B : MulAut (RankTwo n))
    (hAA : A ^ 2 = 1) (hA : ∀ x, x ^ 4 = 1 → A x = x) (hB : ∀ x, x ^ 2 = 1 → B x = x) :
    Commute A B :=
  commute_of_equiv n hn (rankTwoEquiv n) A B hAA hA hB

/-- A deep involution can invert only elements of square one. -/
public lemma sq_eq_one_of_inverted (n : ℕ) (hn : 3 ≤ n) (A : MulAut (RankTwo n))
    (hAA : A ^ 2 = 1) (hA : ∀ x, x ^ 4 = 1 → A x = x) (x : RankTwo n) (hx : A x = x⁻¹) :
    x ^ 2 = 1 :=
  sq_eq_one_of_inverted_of_equiv n hn (rankTwoEquiv n) A hAA hA x hx

/-- The coordinate equivalence sends a vector to its ordered pair of entries. -/
public lemma rankTwoEquiv_apply (n : ℕ) (x : Fin 2 → ZMod (2 ^ n)) :
    rankTwoEquiv n (Multiplicative.ofAdd x) =
      (Multiplicative.ofAdd (x 0), Multiplicative.ofAdd (x 1)) := by
  unfold rankTwoEquiv
  rfl

/-- Matrix multiplication represents the original automorphism on additive coordinates. -/
public lemma autMatrix_mulVec (n : ℕ) (A : MulAut (RankTwo n)) (x : Fin 2 → ZMod (2 ^ n)) :
    rankTwoEquiv n (Multiplicative.ofAdd ((autMatrix n A).mulVec x)) =
      A (rankTwoEquiv n (Multiplicative.ofAdd x)) := by
  rw [autMatrix, LinearMap.toMatrix'_mulVec, coordinateLinear_apply, ofAdd_toAdd,
    MulEquiv.apply_symm_apply]

/-- Both deep-involution conclusions for a group identified with two cyclic groups of order `2 ^ n`. -/
public lemma deep_involution_of_equiv_prod_zmod {G : Type*} [Group G]
    (n : ℕ) (hn : 3 ≤ n) (e : G ≃* RankTwo n) (A : MulAut G)
    (hAA : A ^ 2 = 1) (hA : ∀ x, x ^ 4 = 1 → A x = x) :
    (∀ B : MulAut G, (∀ x, x ^ 2 = 1 → B x = x) → Commute A B) ∧
      (∀ x : G, A x = x⁻¹ → x ^ 2 = 1) := by
  let f := (rankTwoEquiv n).trans e.symm
  exact ⟨fun B hB => commute_of_equiv n hn f A B hAA hA hB,
    fun x hx => sq_eq_one_of_inverted_of_equiv n hn f A hAA hA x hx⟩

end HomocyclicMatrixCongruence
