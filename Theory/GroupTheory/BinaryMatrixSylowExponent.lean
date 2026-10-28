module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.Sylow

/-!
# Two-elements in binary matrix groups of dimension at most four

For a two-element A in characteristic two, A−1 is nilpotent. The kernel
stabilization bound makes its fourth power zero in dimension at most four,
hence A⁴=1. Surjective Sylow transport gives the same exponent bound in
any quotient of a faithfully represented finite group.

This elementary matrix bound supplies the binary exclusions in
Aschbacher–Smith F.6.18(12)–(13), printed p.310.
-/

public section
open Matrix
namespace Theory.GroupTheory
private theorem matrix_nilpotent_dim {F : Type*} [Field F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (k : ℕ) (hk : M ^ k = 0) : M ^ n = 0 := by
  apply Matrix.toLin'.injective
  rw [map_zero,Matrix.toLin'_pow]
  apply LinearMap.ext
  intro x
  have hh := Module.End.ker_pow_le_ker_pow_finrank (Matrix.toLin' M) k
  have hx : x ∈ LinearMap.ker ((Matrix.toLin' M)^k) := by
    rw [← Matrix.toLin'_pow,hk,map_zero]
    simp
  have hx' := hh hx
  simpa only [Module.finrank_fin_fun,LinearMap.mem_ker,LinearMap.zero_apply] using hx'

theorem small_char_two_matrix_pow_four {F : Type*} [Field F] [CharP F 2]
    {n : ℕ} [NeZero n] (hn : n ≤ 4) (A : Matrix (Fin n) (Fin n) F)
    {k : ℕ} (hk : A ^ (2 ^ k) = 1) : A ^ 4 = 1 := by
  let : CharP (Matrix (Fin n) (Fin n) F) 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by
      have h := congrArg (algebraMap F (Matrix (Fin n) (Fin n) F)) (CharP.cast_eq_zero F 2)
      simpa only [map_natCast,map_zero] using h)
  have hz : (A-1) ^ (2^k) = 0 := by
    rw [sub_pow_char_pow_of_commute 2 k (Commute.one_right A),hk,one_pow,sub_self]
  have hd := matrix_nilpotent_dim (A-1) (2^k) hz
  have hfour : (A-1)^4 = 0 := pow_eq_zero_of_le hn hd
  change (A-1)^(2^2) = 0 at hfour
  rw [sub_pow_char_pow_of_commute 2 2 (Commute.one_right A),one_pow] at hfour
  exact sub_eq_zero.mp hfour


theorem small_char_two_sylow_pow_four {F A : Type*} [Field F] [CharP F 2] [Group A]
    {n : ℕ} [NeZero n] (hn : n ≤ 4) (ρ : A →* Matrix (Fin n) (Fin n) F)
    (hρ : Function.Injective ρ) (P : Sylow 2 A) (x : P) : x ^ 4 = 1 := by
  obtain ⟨k,hk⟩ := P.isPGroup' x
  have hpow : ρ (x : A) ^ (2^k) = 1 := by
    rw [← map_pow]
    exact (congrArg (fun y : P => ρ (y : A)) hk).trans (map_one ρ)
  apply Subtype.ext
  change (x : A) ^ 4 = 1
  apply hρ
  rw [map_pow,map_one]
  exact small_char_two_matrix_pow_four hn _ hpow

theorem small_char_two_quotient_sylow_pow_four {F A B : Type*}
    [Field F] [CharP F 2] [Group A] [Finite A] [Group B]
    {n : ℕ} [NeZero n] (hn : n ≤ 4) (ρ : A →* Matrix (Fin n) (Fin n) F)
    (hρ : Function.Injective ρ) (f : A →* B) (hf : Function.Surjective f)
    (P : Sylow 2 B) (x : P) : x ^ 4 = 1 := by
  obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective hf 2 P
  have hx : (x : B) ∈ (R : Subgroup A).map f := by
    change (x : B) ∈ (R.mapSurjective hf : Subgroup B)
    rw [hR]
    exact x.property
  obtain ⟨a,ha,he⟩ := hx
  have hp := small_char_two_sylow_pow_four hn ρ hρ R ⟨a,ha⟩
  apply Subtype.ext
  change (x : B) ^ 4 = 1
  rw [← he,← map_pow]
  rw [show a ^ 4 = 1 from congrArg Subtype.val hp,map_one]
end Theory.GroupTheory
