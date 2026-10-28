module

public import Theory.ElementaryAbelian.Basic
public import Theory.LinearAlgebra.Matrix.BinaryIdempotentPlane
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Compatible full and normalized homocyclic actions

An elementary abelian automorphism group fixing the involutions of a rank-two
homocyclic two-group has full coordinate matrices `I + 2M`. Reduction of `M`
modulo two is an additive, idempotent matrix action, faithful whenever the
original action is faithful on four-torsion. The coordinate representation and
the normalized action use the same matrices, including before reduction.

The coordinate and modulo-eight calculations below adapt the private proofs in
`HomocyclicFourTorsionCoordinates` and `HomocyclicElementaryFourTorsion`.
The compatibility bridge reduces the full displacement to twice its half modulo
eight. Source context: the homocyclic MacWilliams–Sah bound quoted in
Janko–Thompson, Math. Z. 113 (1970), 1.1, printed p.385.
-/

namespace HomocyclicNormalizedBinaryAction

open Matrix
noncomputable section

private theorem reduction_zero_iff {N k t : ℕ} [NeZero N]
    (ht : 0 < t) (hN : N = t * k) (hdiv : k ∣ N) (z : ZMod N) :
    ZMod.castHom hdiv (ZMod k) z = 0 ↔ (t : ZMod N) * z = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  conv_rhs => rw [← ZMod.natCast_zmod_val z, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff]
  conv_rhs => lhs; rw [hN]
  exact (Nat.mul_dvd_mul_iff_left ht).symm

private theorem kernel_annihilates {N k : ℕ} [NeZero N] (hdiv : k ∣ N)
    (c x : ZMod N) (hc : ZMod.castHom hdiv (ZMod k) c = 0)
    (hx : (k : ZMod N) * x = 0) : c * x = 0 := by
  have hd : k ∣ c.val := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hc
    exact hc
  obtain ⟨y, hy⟩ := hd
  rw [← ZMod.natCast_zmod_val c, hy, Nat.cast_mul]
  calc
    (k : ZMod N) * y * x = (y : ZMod N) * ((k : ZMod N) * x) := by ring
    _ = 0 := by rw [hx, mul_zero]

variable {D : Type*} [Group D] {N : ℕ}

private def coordinateAdd (E : D ≃* Multiplicative (Fin 2 → ZMod N)) (a : MulAut D) :
    (Fin 2 → ZMod N) →+ (Fin 2 → ZMod N) where
  toFun x := (E (a (E.symm (Multiplicative.ofAdd x)))).toAdd
  map_zero' := by simp
  map_add' x y := by
    change (E (a (E.symm (Multiplicative.ofAdd x * Multiplicative.ofAdd y)))).toAdd = _
    simp

private def coordinateAction (E : D ≃* Multiplicative (Fin 2 → ZMod N)) :
    MulAut D →* Module.End (ZMod N) (Fin 2 → ZMod N) where
  toFun a := (coordinateAdd E a).toZModLinearMap N
  map_one' := by apply LinearMap.ext; intro x; funext i; simp [coordinateAdd]
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    funext i
    change (E ((a * b) (E.symm (Multiplicative.ofAdd x)))).toAdd i =
      (E (a (E.symm (E (b (E.symm (Multiplicative.ofAdd x))))))).toAdd i
    simp

private def coordinates (n : ℕ)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    D ≃* Multiplicative (Fin 2 → ZMod (2 ^ n)) :=
  e.trans ((MulEquiv.prodMultiplicative _ _).symm.trans
    (AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow (ZMod (2 ^ n)) (ZMod (2 ^ n))).symm))

private theorem matrix_reduction_of_fix {N k t : ℕ} [NeZero N]
    (ht : 0 < t) (hN : N = t * k) (hdiv : k ∣ N)
    (F : Module.End (ZMod N) (Fin 2 → ZMod N))
    (hfix : ∀ x, k • x = 0 → F x = x) :
    (LinearMap.toMatrix' F).map (ZMod.castHom hdiv (ZMod k)) = 1 := by
  ext i j
  let u : Fin 2 → ZMod N := Pi.single j 1
  have hx : k • ((t : ZMod N) • u) = 0 := by
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.zero_apply]
    rw [← mul_assoc, ← Nat.cast_mul, mul_comm k t, ← hN, ZMod.natCast_self, zero_mul]
  have hf := congrFun (hfix ((t : ZMod N) • u) hx) i
  rw [map_smul] at hf
  change (t : ZMod N) * F u i = (t : ZMod N) * u i at hf
  have hz : ZMod.castHom hdiv (ZMod k) (F u i - u i) = 0 :=
    (reduction_zero_iff ht hN hdiv _).mpr (by rw [mul_sub, hf, sub_self])
  have he := sub_eq_zero.mp (by simpa only [map_sub] using hz)
  simpa [u, Matrix.map_apply, LinearMap.toMatrix'_apply, Pi.single_apply,
    Matrix.one_apply, eq_comm] using he

private theorem fix_of_matrix_reduction {N k : ℕ} [NeZero N] (hdiv : k ∣ N)
    (F : Module.End (ZMod N) (Fin 2 → ZMod N))
    (hF : (LinearMap.toMatrix' F).map (ZMod.castHom hdiv (ZMod k)) = 1)
    (x : Fin 2 → ZMod N) (hx : k • x = 0) : F x = x := by
  let A := LinearMap.toMatrix' F
  let r := ZMod.castHom hdiv (ZMod k)
  have hz : r.mapMatrix (A - 1) = 0 := by
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr hF
  have hv : (A - 1) *ᵥ x = 0 := by
    funext i
    change ∑ j, (A - 1) i j * x j = 0
    apply Finset.sum_eq_zero
    intro j _hj
    exact kernel_annihilates hdiv ((A - 1) i j) (x j)
      (congrFun (congrFun hz i) j)
      (by simpa only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] using congrFun hx j)
  apply sub_eq_zero.mp
  simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.toMatrix'_mulVec, A] using hv

private theorem coordinateAction_fix_of_fix
    (E : D ≃* Multiplicative (Fin 2 → ZMod N)) (a : MulAut D) (k : ℕ)
    (hfix : ∀ d : D, d ^ k = 1 → a d = d)
    (x : Fin 2 → ZMod N) (hx : k • x = 0) : coordinateAction E a x = x := by
  have ht : (E.symm (Multiplicative.ofAdd x)) ^ k = 1 := by
    apply E.injective
    rw [map_pow, E.apply_symm_apply, map_one]
    exact congrArg Multiplicative.ofAdd hx
  change (E (a (E.symm (Multiplicative.ofAdd x)))).toAdd = x
  rw [hfix _ ht, E.apply_symm_apply]
  rfl

private theorem fix_of_coordinateAction_fix
    (E : D ≃* Multiplicative (Fin 2 → ZMod N)) (a : MulAut D) (k : ℕ)
    (hfix : ∀ x, k • x = 0 → coordinateAction E a x = x)
    (d : D) (hd : d ^ k = 1) : a d = d := by
  have hx : k • (E d).toAdd = 0 := by
    have he := congrArg (fun d => (E d).toAdd) hd
    simpa only [map_pow, map_one, toAdd_pow, toAdd_one] using he
  have hf := hfix (E d).toAdd hx
  change (E (a (E.symm (E d)))).toAdd = (E d).toAdd at hf
  rw [E.symm_apply_apply] at hf
  exact E.injective (Multiplicative.toAdd.injective hf)

private abbrev BM := BinaryIdempotentPlane.Mat

private def r2 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide) _
private def r4 : ZMod 8 →+* ZMod 4 := ZMod.castHom (by decide) _
private def half (x : ZMod 8) : ZMod 2 := (x.val / 2 : ℕ)

set_option maxRecDepth 4096 in
private theorem half_add : ∀ x y : ZMod 8, r2 x = 0 → r2 y = 0 →
    half (x + y) = half x + half y := by decide
set_option maxRecDepth 4096 in
private theorem half_mul : ∀ x y : ZMod 8, r2 x = 0 → r2 y = 0 →
    half (x * y) = 0 := by decide
set_option maxRecDepth 4096 in
private theorem half_diag : ∀ a b c : ZMod 8, r2 a = 0 → r2 b = 0 → r2 c = 0 →
    2*a + a*a + b*c = 0 → half a * half a + half b * half c = half a := by decide
set_option maxRecDepth 4096 in
private theorem half_offdiag : ∀ a b d : ZMod 8, r2 a = 0 → r2 b = 0 → r2 d = 0 →
    2*b + a*b + b*d = 0 → half a * half b + half b * half d = half b := by decide
set_option maxRecDepth 4096 in
private theorem half_zero : ∀ x : ZMod 8, r2 x = 0 → (half x = 0 ↔ r4 x = 0) := by decide

private abbrev M8 := Matrix (Fin 2) (Fin 2) (ZMod 8)
private def halves (N : M8) : BM := N.map half
private def EvenM (N : M8) : Prop := ∀ i j, r2 (N i j) = 0

private theorem even_add (N P : M8) (hn : EvenM N) (hp : EvenM P) : EvenM (N+P) := by
  intro i j
  change r2 (N i j + P i j) = 0
  rw [map_add, hn, hp, add_zero]

private theorem even_mul (N P : M8) (hn : EvenM N) : EvenM (N*P) := by
  intro i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, hn i 0, hn i 1]

private theorem halves_add (N P : M8) (hn : EvenM N) (hp : EvenM P) :
    halves (N+P) = halves N + halves P := by
  ext i j
  exact half_add _ _ (hn i j) (hp i j)

private theorem halves_mul (N P : M8) (hn : EvenM N) (hp : EvenM P) :
    halves (N*P) = 0 := by
  ext i j
  change half ((N*P) i j) = 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, half_add]
  · rw [half_mul _ _ (hn i 0) (hp 0 j), half_mul _ _ (hn i 1) (hp 1 j), add_zero]
  · rw [map_mul, hn, zero_mul]
  · rw [map_mul, hn, zero_mul]

private theorem halves_idempotent (N : M8) (hn : EvenM N) (hs : N + N + N*N = 0) :
    halves N * halves N = halves N := by
  have hs' (i j : Fin 2) := congrFun (congrFun hs i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at hs'
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, halves, Matrix.map_apply]
  fin_cases i <;> fin_cases j
  · apply half_diag _ _ _ (hn 0 0) (hn 0 1) (hn 1 0)
    linear_combination hs' 0 0
  · apply half_offdiag _ _ _ (hn 0 0) (hn 0 1) (hn 1 1)
    linear_combination hs' 0 1
  · have he : 2*N 1 0 + N 0 0*N 1 0 + N 1 0*N 1 1 = 0 := by
      linear_combination hs' 1 0
    change half (N 1 0) * half (N 0 0) + half (N 1 1) * half (N 1 0) = half (N 1 0)
    calc
      _ = half (N 0 0) * half (N 1 0) + half (N 1 0) * half (N 1 1) := by ring
      _ = _ := half_offdiag _ _ _ (hn 0 0) (hn 1 0) (hn 1 1) he
  · have he : 2*N 1 1 + N 1 1*N 1 1 + N 0 1*N 1 0 = 0 := by
      linear_combination hs' 1 1
    change half (N 1 0) * half (N 0 1) + half (N 1 1) * half (N 1 1) = half (N 1 1)
    calc
      _ = half (N 1 1) * half (N 1 1) + half (N 0 1) * half (N 1 0) := by ring
      _ = _ := half_diag _ _ _ (hn 1 1) (hn 0 1) (hn 1 0) he

private theorem even_sub_one (A : M8) (hA : A.map r2 = 1) : EvenM (A-1) := by
  change r2.mapMatrix A = 1 at hA
  have hh : (A-1).map r2 = 0 := by
    change r2.mapMatrix (A-1) = 0
    rw [map_sub, hA, map_one, sub_self]
  intro i j
  exact congrFun (congrFun hh i) j

private theorem normalized_mul (A B : M8) (hA : A.map r2 = 1) (hB : B.map r2 = 1) :
    halves (A*B-1) = halves (A-1) + halves (B-1) := by
  have hn := even_sub_one A hA
  have hp := even_sub_one B hB
  have he : A*B-1 = ((A-1)+(B-1))+(A-1)*(B-1) := by noncomm_ring
  rw [he, halves_add _ _ (even_add _ _ hn hp) (even_mul _ _ hn),
    halves_add _ _ hn hp, halves_mul _ _ hn hp, add_zero]

private theorem matrix_half {N : ℕ} [NeZero N] (h2 : 2 ∣ N)
    (T : Matrix (Fin 2) (Fin 2) (ZMod N))
    (hT : T.map (ZMod.castHom h2 (ZMod 2)) = 1) :
    ∃ M, T = 1 + (2 : ZMod N) • M := by
  let r := ZMod.castHom h2 (ZMod 2)
  have hz : r.mapMatrix (T - 1) = 0 := by
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr hT
  have hd (i j : Fin 2) : 2 ∣ ((T - 1) i j).val := by
    have h := congrFun (congrFun hz i) j
    change ZMod.castHom h2 (ZMod 2) ((T - 1) i j) = 0 at h
    rwa [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h
  choose m hm using hd
  refine ⟨fun i j => (m i j : ZMod N), ?_⟩
  apply (sub_eq_iff_eq_add.mp ?_).trans (add_comm _ _)
  ext i j
  change (T - 1) i j = (2 : ZMod N) * (m i j : ZMod N)
  conv_lhs => rw [← ZMod.natCast_zmod_val ((T - 1) i j), hm i j]
  simp

set_option maxRecDepth 4096 in
private theorem half_two : ∀ x : ZMod 8, half (2 * x) = r2 x := by decide

private theorem compatible_half {N : ℕ} (h8 : 8 ∣ N)
    (T M : Matrix (Fin 2) (Fin 2) (ZMod N))
    (hM : T = 1 + (2 : ZMod N) • M) :
    halves ((T.map (ZMod.castHom h8 (ZMod 8))) - 1) =
      M.map (ZMod.castHom (dvd_trans (by decide : 2 ∣ 8) h8) (ZMod 2)) := by
  let r8 := ZMod.castHom h8 (ZMod 8)
  have he : T.map r8 - 1 = (2 : ZMod 8) • M.map r8 := by
    change r8.mapMatrix T - 1 = _
    rw [hM, map_add, map_one, add_sub_cancel_left]
    ext i j
    exact map_mul r8 2 (M i j) |>.trans (by rw [map_ofNat]; rfl)
  rw [he]
  ext i j
  change half (2 * r8 (M i j)) = _
  rw [half_two]
  change (r2.comp r8) (M i j) = _
  rw [show r2 = ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) from rfl,
    ZMod.castHom_comp]
  rfl

/-- Full coordinates and their faithful binary normalization, with compatible
halves of the full matrix displacement. -/
public theorem exists_compatible_actions
    {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (A : Subgroup (MulAut D)) [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ d : D, d ^ 2 = 1 → a d = d)
    (hfaith : ∀ a ∈ A, (∀ d : D, d ^ 4 = 1 → a d = d) → a = 1) :
    ∃ (E : D ≃* Multiplicative (Fin 2 → ZMod (2 ^ n)))
      (T : A →* Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n)))
      (f : A →* Multiplicative BinaryIdempotentPlane.Mat),
      Function.Injective f ∧
      (∀ a, (f a).toAdd * (f a).toAdd = (f a).toAdd) ∧
      (∀ (a : A) (d : D), (E ((a : MulAut D) d)).toAdd =
        (T a).mulVec (E d).toAdd) ∧
      (∀ a, ∃ M : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n)),
        T a = 1 + (2 : ZMod (2 ^ n)) • M ∧
        M.map (ZMod.castHom (show 2 ∣ 2 ^ n from
          dvd_trans (by decide : 2 ∣ 8) (pow_dvd_pow 2 hn)) (ZMod 2)) = (f a).toAdd) := by
  let : NeZero (2 ^ n) := ⟨pow_ne_zero n (by decide)⟩
  have h8 : 8 ∣ 2 ^ n := pow_dvd_pow 2 hn
  have h2 : 2 ∣ 2 ^ n := dvd_trans (by decide : 2 ∣ 8) h8
  have h4 : 4 ∣ 2 ^ n := dvd_trans (by decide : 4 ∣ 8) h8
  let E := coordinates n e
  let L := coordinateAction E
  let T : A →* Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n)) :=
    LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp (L.comp A.subtype)
  let r8 := ZMod.castHom h8 (ZMod 8)
  let g : A →* M8 := r8.mapMatrix.toMonoidHom.comp T
  have hcomp (k : ℕ) (hk : k ∣ 8) (a : A) :
      (g a).map (ZMod.castHom hk (ZMod k)) =
        (T a).map (ZMod.castHom (dvd_trans hk h8) (ZMod k)) := by
    ext i j
    change (ZMod.castHom hk (ZMod k)).comp r8 (T a i j) = _
    rw [ZMod.castHom_comp]
    rfl
  have hT (a : A) : (T a).map (ZMod.castHom h2 (ZMod 2)) = 1 := by
    change (LinearMap.toMatrix' (L a.val)).map (ZMod.castHom h2 (ZMod 2)) = 1
    have hN : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    apply matrix_reduction_of_fix (pow_pos (by decide) _) hN
    exact coordinateAction_fix_of_fix E a.val 2 (hfix a.val a.property)
  have hmod2 (a : A) : (g a).map r2 = 1 := by
    rw [r2, hcomp]
    exact hT a
  have hmod4 (a : A) : (g a).map r4 = 1 → a = 1 := by
    intro ha
    apply Subtype.ext
    apply hfaith a.val a.property
    apply fix_of_coordinateAction_fix E a.val 4
    intro x hx
    apply fix_of_matrix_reduction h4 (L a.val) _ x hx
    rw [r4, hcomp] at ha
    exact ha
  let f : A →* Multiplicative BM :=
    { toFun := fun a => Multiplicative.ofAdd (halves (g a - 1))
      map_one' := by simp [halves, half]
      map_mul' := by
        intro a b
        exact congrArg Multiplicative.ofAdd
          (by rw [map_mul]; exact normalized_mul _ _ (hmod2 a) (hmod2 b)) }
  refine ⟨E, T, f, ?_, ?_, ?_, ?_⟩
  · apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    change a = 1
    apply hmod4 a
    have ht : halves (g a - 1) = 0 := ha
    have hz : (g a - 1).map r4 = 0 := by
      ext i j
      apply (half_zero _ (even_sub_one _ (hmod2 a) i j)).mp
      exact congrFun (congrFun ht i) j
    change r4.mapMatrix (g a - 1) = 0 at hz
    rwa [map_sub, map_one, sub_eq_zero] at hz
  · intro a
    apply halves_idempotent _ (even_sub_one _ (hmod2 a))
    have ha : a ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : MulAut D) a.property
    have hs : g a * g a = 1 := by simpa [pow_two] using congrArg g ha
    calc
      (g a-1)+(g a-1)+(g a-1)*(g a-1) = g a*g a-1 := by noncomm_ring
      _ = 0 := by rw [hs, sub_self]
  · intro a d
    change _ = (LinearMap.toMatrix' (L a.val)).mulVec (E d).toAdd
    rw [LinearMap.toMatrix'_mulVec]
    change _ = (E (a.val (E.symm (E d)))).toAdd
    rw [E.symm_apply_apply]
  · intro a
    obtain ⟨M, hM⟩ := matrix_half h2 (T a) (hT a)
    exact ⟨M, hM, (compatible_half h8 (T a) M hM).symm⟩

end
end HomocyclicNormalizedBinaryAction
