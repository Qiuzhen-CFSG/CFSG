module

public import Stellmacher.Recognition.NGroupCentralizer
public import Stellmacher.Recognition.NGroupTransport
public import BenderSuzuki.Converse.PSU3
public import BenderSuzuki.MatrixGroups.UnitarySL2Centralizer
public import BenderSuzuki.FinalTheorem
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Even unitary models do not satisfy the all-prime N condition

For `n ≥ 2`, the actual projective antidiagonal matrix model `PSU3Model n`
is not an N-group. In the quadratic field of order `q²`, where `q = 2^n`,
choose a norm-one torus element whose cube is nonidentity. Its projective
image is nonidentity, and its centralizer contains an injective copy of
SL₂ over the fixed field of order `q`. The field has at least four elements,
so SL₂ is perfect and nonsolvable. This contradicts the solvability of
nonidentity element centralizers in an all-prime N-group.

The existing norm-one torus theorem includes `q = 8`, where an order-nine
torus has projective image of order three. No prime divisor different from
three is selected. The final transport uses the proved equivalence from the
standard Hermitian form to the unchanged `PSU3Model` definition.

This removes the even projective unitary family when passing from the N₂
models to Thompson's all-prime N catalogue; see Kurzweil–Stellmacher,
Appendix, p. 370, and GLS1 (28.1). The proof uses the explicit unitary torus
and block matrices, together with Mathlib's SL₂ perfectness theorem.
-/

namespace Stellmacher.Recognition

open scoped Matrix

open BenderSuzuki BenderSuzuki.MatrixGroups

private theorem not_isSolvable_sl2_of_four_le_card
    {F : Type*} [Field F] [Finite F] (hcard : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ)
    (by decide : (2 : ℕ) ≠ 0) (by rw [Nat.card_units]; omega : 2 < Nat.card Fˣ)
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro h
    apply ha
    exact Units.ext (by simpa using h)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero a) hasq⟩
  intro hs
  let := hs
  exact Group.IsPerfect.not_isSolvable
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) inferInstance

private theorem not_isNGroup_unitary
    (n : ℕ) (hn : 2 ≤ n) [NeZero n] : ¬ IsNGroup (Converse.PSU3 n) := by
  intro hN
  let J := Converse.uform n
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card (Converse.UField n) = (2 ^ n) ^ 2 :=
    Converse.card_UField n hn0
  have hfixed : Nat.card {x : Converse.UField n // J.conj x = x} = 2 ^ n :=
    Converse.card_fixed_UField n hn0
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hq : 4 ≤ 2 ^ n := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  obtain ⟨k, _, _, hkne, hkconj⟩ :=
    External.exists_hermitian_norm_one_torus_cube_ne_one
      J (2 ^ n) hcard hfixed hJ (by omega)
  let t := External.hermitianTorusPSU J hJ k
  have hsolv : Group.IsSolvable (Subgroup.centralizer ({t} : Set (Converse.PSU3 n))) :=
    hN.isSolvable_centralizer hkne
  obtain ⟨f, hf⟩ := exists_sl2_embedding_centralizing_norm_one_torus J hJ k hkconj
  have hFcard : Nat.card (FixedBy.subfield (Converse.UField n) J.conj) = 2 ^ n := by
    let hset : ((FixedBy.subfield (Converse.UField n) J.conj) : Set (Converse.UField n)) =
        {x : Converse.UField n | J.conj x = x} := by ext x; rfl
    exact (Nat.card_congr (Equiv.setCongr hset)).trans hfixed
  exact (not_isSolvable_sl2_of_four_le_card (by rw [hFcard]; exact hq))
    (Group.isSolvable_of_isSolvable_injective hf)

/-- Every even-field PSU₃ model with `q ≥ 4` fails the all-prime N condition. -/
public theorem not_isNGroup_PSU3Model (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsNGroup (PSU3Model n) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨e⟩ := projectiveSpecialUnitary_equiv_psu3Model (Converse.uform n) n hn
    (Converse.uform_form n) (Converse.card_UField n (by omega))
    (Converse.card_fixed_UField n (by omega))
  exact fun hN => not_isNGroup_unitary n hn ((isNGroup_iff_of_mulEquiv e).mpr hN)

end Stellmacher.Recognition
