module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-!
# Coordinates for homocyclic actions faithful on four-torsion

For a group with coordinates in two equal cyclic groups of order at least eight,
transport its automorphisms to linear maps over the corresponding residue ring.
Their matrices reduce modulo eight. Fixing all involutions forces the reduced
matrices to be the identity modulo two; a matrix that is the identity modulo
four fixes all four-torsion. Thus faithfulness on four-torsion detects the
identity through the reduction modulo four.

The scalar argument uses the elementary identity: for a positive factorization
N = t * k, reduction of z modulo k vanishes exactly when t * z = 0 modulo N.
Conversely, a scalar in the reduction kernel annihilates every k-torsion scalar.
No elementary-abelian hypothesis on the automorphism group is needed here.

Source context: the coordinate step in the homocyclic case of the
MacWilliams–Sah bound, quoted in Janko–Thompson, Math. Z. 113 (1970), 1.1,
printed p.385; see
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
The linear-map and matrix identifications use Mathlib's residue-module API.
-/

namespace HomocyclicFourTorsion

open scoped IsMulCommutative
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

/-- An action on a rank-two homocyclic two-group fixing involutions and faithful
on four-torsion has matrix coordinates modulo eight, trivial modulo two and
with trivial kernel after reduction modulo four. -/
public theorem exists_mod_eight_matrix_action {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (B : Subgroup (MulAut D))
    (hfix : ∀ a ∈ B, ∀ d : D, d ^ 2 = 1 → a d = d)
    (hfaith : ∀ a ∈ B, (∀ d : D, d ^ 4 = 1 → a d = d) → a = 1) :
    ∃ f : B →* Matrix (Fin 2) (Fin 2) (ZMod 8),
      (∀ b, (f b).map (ZMod.castHom (show 2 ∣ 8 by decide) (ZMod 2)) = 1) ∧
      (∀ b, (f b).map (ZMod.castHom (show 4 ∣ 8 by decide) (ZMod 4)) = 1 → b = 1) := by
  let : NeZero (2 ^ n) := ⟨pow_ne_zero n (by decide)⟩
  have h8 : 8 ∣ 2 ^ n := by
    change 2 ^ 3 ∣ 2 ^ n
    exact pow_dvd_pow 2 hn
  have h2 : 2 ∣ 2 ^ n := dvd_trans (by decide : 2 ∣ 8) h8
  have h4 : 4 ∣ 2 ^ n := dvd_trans (by decide : 4 ∣ 8) h8
  let E := coordinates n e
  let L := coordinateAction E
  let A : B →* Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n)) :=
    LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp (L.comp B.subtype)
  let r8 := ZMod.castHom h8 (ZMod 8)
  let f : B →* Matrix (Fin 2) (Fin 2) (ZMod 8) := r8.mapMatrix.toMonoidHom.comp A
  have hcomp (k : ℕ) (hk : k ∣ 8) (b : B) :
      (f b).map (ZMod.castHom hk (ZMod k)) =
        (A b).map (ZMod.castHom (dvd_trans hk h8) (ZMod k)) := by
    ext i j
    change (ZMod.castHom hk (ZMod k)).comp r8 (A b i j) = _
    rw [ZMod.castHom_comp]
    rfl
  refine ⟨f, ?_, ?_⟩
  · intro b
    rw [hcomp]
    change (LinearMap.toMatrix' (L b.val)).map (ZMod.castHom h2 (ZMod 2)) = 1
    have hN : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    apply matrix_reduction_of_fix (pow_pos (by decide) _) hN
    exact coordinateAction_fix_of_fix E b.val 2 (hfix b.val b.property)
  · intro b hb
    apply Subtype.ext
    apply hfaith b.val b.property
    apply fix_of_coordinateAction_fix E b.val 4
    intro x hx
    apply fix_of_matrix_reduction h4 (L b.val) _ x hx
    rw [hcomp] at hb
    exact hb

end

end HomocyclicFourTorsion
