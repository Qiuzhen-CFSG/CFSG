module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel

/-!
# Squared commutators in the actual projective unitary Borel

In characteristic two a Heisenberg root element can have square one only
when its first coordinate vanishes. For b = u t in the root–torus Borel,
the first coordinate of [r,b], with r of first coordinate one, is
1 - k conjugate(k)⁻². If this vanishes, the three diagonal entries of t
are equal, so t is trivial in the genuine projective quotient.

Consequently an element of the Borel whose commutators with all root
elements have square one belongs to the root group. The fixed field has
order 2^n, the matrix field has order (2^n)^2, and nontriviality of the
stored involution follows from those exact cardinalities. The concrete
SU₃ Sylow subgroup is mapped through the actual SU₃ → PSU₃ projection.

Source: Aschbacher–Smith, E.6.8, printed pp.247–248 (PDF pp.258–259),
and the root–torus formulas of Huppert II.10.12.
-/

public section

open Subgroup
open scoped commutatorElement
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryIntrinsic

private theorem root_first_zero_of_square {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J)
    (hz : (hermitianUnipotentPSU J hJ z) ^ 2 = 1) : z.1.1 = 0 := by
  by_contra h
  apply hermitianUnipotentPSU_ne_one_of_snd_ne_zero J hJ (z ^ 2) ?_
  · simpa only [map_pow] using hz
  · rw [pow_two]
    change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 ≠ 0
    rw [CharTwo.add_self_eq_zero, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero h ((map_ne_zero J.conj).2 h))

private theorem root_first_mul {F : Type*} [Field F] (J : HermitianForm 3 F)
    (z w : hermitianUnipotentCoord J) : (z * w).1.1 = z.1.1 + w.1.1 := rfl

private theorem root_first_inv {F : Type*} [Field F] (J : HermitianForm 3 F)
    (z : hermitianUnipotentCoord J) : z⁻¹.1.1 = -z.1.1 := rfl

private theorem torus_eq_one_of_scale {F : Type*} [Field F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Fˣ)
    (hk : (k : F) * (J.conj (k : F))⁻¹ ^ 2 = 1) :
    hermitianTorusPSU J hJ k = 1 := by
  have hk0 : (k : F) ≠ 0 := Units.ne_zero k
  have hc0 : J.conj (k : F) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have hkc : (k : F) = (J.conj (k : F)) ^ 2 := by
    have h := congrArg (fun x : F => x * (J.conj (k : F)) ^ 2) hk
    field_simp at h
    simpa [hc0] using h
  have hck : J.conj (k : F) = (k : F) ^ 2 := by
    simpa only [map_pow, J.conj_involutive (k : F)] using congrArg J.conj hkc
  have hcube : (k : F) ^ 3 = 1 := by
    rw [hck] at hkc
    have he : (k : F) * (k : F) ^ 3 = (k : F) * 1 := by
      calc
        _ = ((k : F) ^ 2) ^ 2 := by ring
        _ = (k : F) := hkc.symm
        _ = _ := by ring
    exact mul_left_cancel₀ hk0 he
  have hnorm : J.conj (k : F) = (k : F)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hck]
    simpa [pow_succ] using hcube
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) = 1
  apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  refine ⟨(k : F), ?_⟩
  have hmiddle : J.conj (k : F) * (k : F)⁻¹ = (k : F) := by
    rw [hck, pow_two, mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, Matrix.scalar_apply]
  · rw [hnorm, inv_inv]
  · exact hmiddle.symm

private theorem exists_first_one {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 3 F)
    (hnon : ∃ t : F, J.conj t ≠ t) :
    ∃ z : hermitianUnipotentCoord J, z.1.1 = 1 := by
  obtain ⟨t, ht⟩ := hnon
  have hd : t + J.conj t ≠ 0 := by
    intro h
    apply ht
    calc
      J.conj t = t + (t + J.conj t) := by simp [← add_assoc, CharTwo.add_self_eq_zero]
      _ = t := by rw [h, add_zero]
  have hb : t / (t + J.conj t) + J.conj (t / (t + J.conj t)) = 1 := by
    rw [map_div₀, map_add, J.conj_involutive, add_comm (J.conj t) t,
      ← add_div, div_self hd]
  exact ⟨⟨(1, t / (t + J.conj t)), by
    change (t / (t + J.conj t) + J.conj (t / (t + J.conj t))) + 1 * J.conj 1 = 0
    rw [hb, map_one, mul_one, CharTwo.add_self_eq_zero]⟩, rfl⟩

private theorem root_torus_square_test {F : Type*} [Field F] [CharP F 2]
    (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hnon : ∃ t : F, J.conj t ≠ t)
    (u : hermitianUnipotentCoord J) (k : Fˣ)
    (h : ∀ z : hermitianUnipotentCoord J,
      ⁅hermitianUnipotentPSU J hJ z,
        hermitianUnipotentPSU J hJ u * hermitianTorusPSU J hJ k⁆ ^ 2 = 1) :
    hermitianTorusPSU J hJ k = 1 := by
  obtain ⟨z, hz⟩ := exists_first_one J hnon
  let w := z * u * hermitianTorusAction J k z⁻¹ * u⁻¹
  have hw : hermitianUnipotentPSU J hJ w =
      ⁅hermitianUnipotentPSU J hJ z,
        hermitianUnipotentPSU J hJ u * hermitianTorusPSU J hJ k⁆ := by
    dsimp only [w]
    simp only [map_mul, map_inv]
    have he := hermitianTorusPSU_mul_unipotent J hJ k z⁻¹
    rw [map_inv] at he
    rw [← mul_inv_eq_iff_eq_mul] at he
    rw [← he]
    simp only [commutatorElement_def]
    group
  have hf : w.1.1 = 0 := root_first_zero_of_square J hJ w (by rw [hw]; exact h z)
  dsimp only [w] at hf
  simp only [root_first_mul, root_first_inv, hermitianTorusAction_fst, hz] at hf
  apply torus_eq_one_of_scale J hJ k
  linear_combination -hf

open scoped Pointwise

private theorem standard_square_test {F : Type*} [Field F] [CharP F 2]
    (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hnon : ∃ t : F, J.conj t ≠ t)
    (hN : normalizer ((hermitianUnipotentPSU J hJ).range : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (hermitianUnipotentPSU J hJ).range ⊔ (hermitianTorusPSU J hJ).range)
    (b : normalizer ((hermitianUnipotentPSU J hJ).range : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hb : ∀ r ∈ (hermitianUnipotentPSU J hJ).range.subgroupOf
      (normalizer ((hermitianUnipotentPSU J hJ).range : Set (ProjectiveSpecialUnitaryMatrixGroup J))), ⁅r, b⁆ ^ 2 = 1) :
    b ∈ (hermitianUnipotentPSU J hJ).range.subgroupOf
      (normalizer ((hermitianUnipotentPSU J hJ).range : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let R := (hermitianUnipotentPSU J hJ).range
  let D := (hermitianTorusPSU J hJ).range
  have hDN : D ≤ normalizer (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := hN ▸ le_sup_right
  have hmem : b.val ∈ (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (D : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← coe_mul_of_right_le_normalizer_left R D hDN, ← hN]
    exact b.property
  obtain ⟨r, ⟨u, rfl⟩, d, ⟨k, rfl⟩, he⟩ := hmem
  have hk : hermitianTorusPSU J hJ k = 1 := by
    apply root_torus_square_test J hJ hnon u k
    intro z
    have hz : hermitianUnipotentPSU J hJ z ∈ R := ⟨z, rfl⟩
    have hh := congrArg Subtype.val (hb
      ⟨hermitianUnipotentPSU J hJ z, R.le_normalizer hz⟩ hz)
    change ⁅hermitianUnipotentPSU J hJ z, b.val⁆ ^ 2 = 1 at hh
    rwa [← he] at hh
  change b.val ∈ R
  rw [← he, hk]
  simpa only [mul_one] using (show hermitianUnipotentPSU J hJ u ∈ R from ⟨u, rfl⟩)

/-- The specified quadratic Frobenius is a nontrivial involution. -/
theorem exists_nonfixed {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) : ∃ t : F, J.conj t ≠ t := by
  have hfixed := fixed_card J n hn hcard hconj
  by_contra! h
  have hc : Nat.card {x : F // J.conj x = x} = Nat.card F :=
    Nat.card_congr (Equiv.subtypeUnivEquiv h)
  rw [hcard, hfixed] at hc
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  nlinarith

/-- The actual standard projective Sylow normalizer satisfies the root square test. -/
theorem standard_sylow_square_test {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      ∀ b : normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
        (∀ r ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subgroupOf (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))),
          ⁅r, b⁆ ^ 2 = 1) →
        b ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subgroupOf (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let _ : CharP F 2 := charP_two n hn hcard
  obtain ⟨_, _, T, hT, _⟩ := standard_su_borel_data J n hn hcard hconj hJ
  let S := T.mapSurjective (suProjection_surjective J)
  have hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = (hermitianUnipotentPSU J hJ).range := by
    change (T : Subgroup J.specialSubgroup).map (suProjection J) = _
    rw [hT, suRoot_map_projection]
  obtain ⟨_, _, _, _, _, _, hB, hN, _⟩ :=
    standard_projective_matrix_borel J n hn hcard hconj hJ
  refine ⟨S, ?_⟩
  let test (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
    ∀ b : normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      (∀ r ∈ P.subgroupOf (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))),
        ⁅r, b⁆ ^ 2 = 1) →
      b ∈ P.subgroupOf (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
  change test (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  rw [hS]
  exact standard_square_test J hJ (exists_nonfixed J hn hcard hconj) (hN.trans hB.symm)


end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryIntrinsic
end
