module

public import BenderSuzuki.External.Huppert.XI.theorem_11_16
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.ActionBasics
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.SevenDivisor
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity

/-!
# Recognition from the degree-nine Zassenhaus action

A nonabelian simple group acting faithfully and doubly transitively on nine
points, with no nonidentity element fixing three points, is isomorphic to
the actual PSL₂(8) matrix group. Huppert–Blackburn XI.11.16 constructs the
projective-model equivalence. Degree nine forces the field order to be eight
and excludes the odd-characteristic and Suzuki alternatives. Every unit in
an eight-element field has a square root, so the natural inclusion of PSL₂
in PGL₂ is an isomorphism; a field equivalence then gives the specified
`GaloisField 2 3` carrier.

The no-regular-normal-subgroup premise of XI.11.16 is discharged here:
simplicity would make such a subgroup the whole group, of order nine,
contrary to noncommutativity.

For a nonabelian simple normal subgroup of a proper primitive subgroup of
A₉, `SevenDivisor` proves seven-divisibility, `ActionBasics` upgrades the
action to triple transitivity, and `TripleRigidity` proves the fixed-point
bound. The final theorem therefore gives the actual PSL₂(8) equivalence
from the original subgroup and action hypotheses, with no additional inputs.

This proves the simple-normal-subgroup recognition step for condition K in
the alternating case of Aschbacher–Smith, Theorem 0.1.2(3), printed pp.4 and
482. Existence of such a normal subgroup and the full primitive structural
alternative belong to the parent argument.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction
open MulAction BenderSuzuki.MatrixGroups

private theorem simple_nine_no_regular_normal
    {G : Type*} [Group G] [MulAction G (Fin 9)] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) :
    ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
      ∀ a b : Fin 9, ∃! r : R, (r : G) • a = b := by
  rintro ⟨R, hn, hR, hr⟩
  have htop := (IsSimpleGroup.eq_bot_or_eq_top_of_normal R hn).resolve_left hR
  have hbij : Function.Bijective (fun r : R => (r : G) • (0 : Fin 9)) := by
    constructor
    · intro r s he
      obtain ⟨t, ht, hu⟩ := hr 0 ((r : G) • 0)
      exact (hu r rfl).trans (hu s he.symm).symm
    · intro b
      obtain ⟨r, hr, _⟩ := hr 0 b
      exact ⟨r, hr⟩
  have hcard : Nat.card G = 3 ^ 2 := by
    have h := Nat.card_congr (Equiv.ofBijective _ hbij)
    simpa [htop] using h
  exact hna (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard)

private noncomputable def pglEightEquivPSL
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 8) :
    Matrix.ProjGenLinGroup (Fin 2) K ≃* PSL2MatrixGroup K :=
  (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
      Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots (by
        intro r
        refine ⟨r ^ 4, ?_⟩
        have hr : r ^ 7 = 1 := by
          simpa [Nat.card_units, hK] using (pow_card_eq_one' (x := r))
        calc
          (r ^ 4) ^ Fintype.card (Fin 2) = r ^ (7 + 1) := by norm_num [← pow_mul]
          _ = r := by rw [pow_succ, hr, one_mul])⟩).symm

/-- Recognition from the actual nine-point action and its two fixed-point bound. -/
public theorem simple_pslTwoEight_of_zassenhaus_action
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)]
    (hna : ¬ IsMulCommutative G)
    (htwo : IsMultiplyPretransitive G (Fin 9) 2)
    (hfixed : ∀ g : G, g ≠ 1 → ∀ a b c : Fin 9,
      a ≠ b → a ≠ c → b ≠ c →
      ¬ (g • a = a ∧ g • b = b ∧ g • c = c)) :
    Nonempty (G ≃* PSL2MatrixGroup (GaloisField 2 3)) := by
  classical
  let D := fixingSubgroup G ({0, 1} : Set (Fin 9))
  have hindex : D.index = 9 * 8 := by
    have hcard : ({0, 1} : Set (Fin 9)).ncard = 2 := by simp
    have h := IsMultiplyPretransitive.index_of_fixingSubgroup_eq
      (G := G) ({0, 1} : Set (Fin 9)) (hcard ▸ htwo)
    norm_num [hcard, Nat.choose] at h ⊢
    exact h
  have horder : Nat.card G = (8 + 1) * 8 * Nat.card D := by
    rw [← D.index_mul_card, hindex]
  obtain ⟨p, f, hp, hf, hpf, hcases⟩ :=
    BenderSuzuki.External.huppert_blackburn_XI_11_16_zassenhaus_classification.{_, 0, 0}
      (G := G) (Omega := Fin 9) 8 (Nat.card D) (by simp) horder htwo hfixed
      (simple_nine_no_regular_normal hna)
  have hp2 : p = 2 := by
    have hpd : p ∣ 2 ^ 3 := by
      change p ∣ 8
      rw [hpf]
      exact dvd_pow_self p (by omega)
    exact (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd) |>.resolve_left hp.ne_one
  rcases hcases with ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ | ⟨hodd, _⟩ | ⟨hodd, _⟩ | ⟨_, m, hm, heq, _⟩
  · let := hKf
    let := hKfin
    let := Fintype.ofFinite K
    let := Fintype.ofFinite (GaloisField 2 3)
    let eF : K ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
        GaloisField.card 2 3 (by decide)]
      norm_num)
    exact ⟨e.trans ((pglEightEquivPSL hK).trans (Atlas.fieldEquivPSL 2 eF))⟩
  · norm_num [hp2] at hodd
  · norm_num [hp2] at hodd
  · have hl : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    nlinarith

/-- A nonabelian simple normal subgroup of a proper primitive subgroup of A₉
is isomorphic to the actual PSL₂(8) matrix group. -/
public theorem primitive_simple_normal_pslTwoEight
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    (hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N]
    (hna : ¬ IsMulCommutative N) :
    Nonempty (N ≃* PSL2MatrixGroup (GaloisField 2 3)) := by
  have hseven := seven_dvd_card_primitive_simple_normal H hH hp N hna
  have hthree := primitive_simple_normal_three_pretransitive_of_seven H hp N hseven
  let : IsMultiplyPretransitive N (Fin 9) 3 := hthree
  exact simple_pslTwoEight_of_zassenhaus_action hna
    (isMultiplyPretransitive_of_le (by decide : 2 ≤ 3) (by simp))
    (primitive_simple_normal_fixed_triple_bound H hH hp N hna hthree)

end CFSG.Quasithin.MainConverse.NineReduction
