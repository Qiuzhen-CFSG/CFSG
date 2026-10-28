module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Contracts
public import Theory.SpecificGroups.SU3.OddPrimeRootConfiguration

/-!
# The extraspecial root inside the special unitary group

The special and projective root images are compared through their common
Hermitian coordinates. Projective injectivity makes this a genuine group
isomorphism, so the extraspecial structure transfers to the literal special
root. The same norm calculation as in `OddPrimeRootConfiguration` realizes
central fusion by special-unitary torus elements, before projectivizing.

Source: Huppert II.10.4 and II.10.12; the root-group calculation underlying
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3.
-/

noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity

variable {F : Type*} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private theorem specialRoot_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w h
  apply Coverage.root_injective J hJ
  apply Subtype.ext
  exact congrArg ProjGenLinGroup.mk (congrArg Subtype.val h)

private def coordinateSpecialEquiv : hermitianUnipotentCoord J ≃* specialRoot J hJ :=
  MulEquiv.ofBijective (hermitianUnipotentSU J hJ).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (specialRoot_injective J hJ),
      (hermitianUnipotentSU J hJ).rangeRestrict_surjective⟩

/-- The two literal root images have the same injective coordinate model. -/
public def specialProjectiveRootEquiv : specialRoot J hJ ≃* Coverage.rootGroup J hJ :=
  (coordinateSpecialEquiv J hJ).symm.trans
    (MulEquiv.ofBijective (Coverage.root J hJ).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (Coverage.root_injective J hJ),
        (Coverage.root J hJ).rangeRestrict_surjective⟩)

/-- The comparison is induced by the actual special-to-projective map. -/
public theorem specialProjectiveRootEquiv_val (z : specialRoot J hJ) :
    (specialProjectiveRootEquiv J hJ z : ProjectiveSpecialUnitaryMatrixGroup J) =
      J.specialToProjective z := by
  obtain ⟨w, rfl⟩ := (coordinateSpecialEquiv J hJ).surjective z
  simp only [specialProjectiveRootEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [J.specialToProjective_apply_val]
  rfl

private theorem fixed_card [Finite F] (hc : Nat.card F = 5 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 5) : Nat.card {x : F // J.conj x = x} = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
    J.conj 5 1 (by decide) (by simpa only [pow_one] using hc)
    (by simpa only [pow_one] using hconj)

/-- The special root, with its original embedding, is extraspecial of order 125. -/
public theorem specialRoot_structure [Finite F] (hc : Nat.card F = 5 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 5) :
    IsExtraspecial 5 (specialRoot J hJ) ∧ Nat.card (specialRoot J hJ) = 5 ^ 3 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hf := fixed_card J hc hconj
  exact ⟨IsExtraspecial.of_mulEquiv (specialProjectiveRootEquiv J hJ).symm
      (HermitianForm.OddPrimeRootConfiguration.rootGroup_isExtraspecial J hJ
        (by decide) hc hf),
    (Nat.card_congr (specialProjectiveRootEquiv J hJ).toEquiv).trans
      (Coverage.rootGroup_card J hJ 5 hc hf)⟩

private theorem coord_center (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    z ∈ center (hermitianUnipotentCoord J) := by
  apply mem_center_iff.mpr
  intro w
  apply Subtype.ext
  apply Prod.ext
  · exact add_comm _ _
  · change w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 =
      z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1
    simp [hz, add_comm]

private theorem central_pow (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) (i : ℕ) :
    (z ^ i).val = (0, (i : F) * z.val.2) := by
  induction i with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; rfl
  | succ i ih =>
    rw [pow_succ]
    change ((z ^ i).val.1 + z.val.1,
      (z ^ i).val.2 + z.val.2 - (z ^ i).val.1 * J.conj z.val.1) = _
    rw [ih, hz]
    simp [Nat.cast_succ, add_mul]

/-- A nonidentity root-central element is fused to every nonidentity power
by actual SU torus elements. -/
public theorem specialRoot_central_fusion [Finite F] (hc : Nat.card F = 5 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 5) :
    ∃ z : specialRoot J hJ, z ∈ center (specialRoot J hJ) ∧ z ≠ 1 ∧
      ∀ i : ℕ, 0 < i → i < 5 → ∃ g : J.specialSubgroup,
        g * (z : J.specialSubgroup) * g⁻¹ = (z : J.specialSubgroup) ^ i := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hf := fixed_card J hc hconj
  have hn : ∃ x : F, J.conj x ≠ x := by
    by_contra! hn
    let e : {x : F // J.conj x = x} ≃ F :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, hn x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hh := Nat.card_congr e
    rw [hc, hf] at hh
    norm_num at hh
  obtain ⟨x, hx⟩ := hn
  let z : hermitianUnipotentCoord J := ⟨(0, x - J.conj x), by
    change (x - J.conj x) + J.conj (x - J.conj x) + 0 * J.conj 0 = 0
    rw [map_sub, J.conj_involutive]
    ring⟩
  have hz : z.val.1 = 0 := rfl
  have hz1 : z ≠ 1 := by
    intro he
    exact hx.symm (sub_eq_zero.mp (congrArg (fun w : hermitianUnipotentCoord J => w.val.2) he))
  refine ⟨coordinateSpecialEquiv J hJ z,
    (centerCongr (coordinateSpecialEquiv J hJ) ⟨z, coord_center J z hz⟩).property,
    (coordinateSpecialEquiv J hJ).map_ne_one_iff.mpr hz1, ?_⟩
  intro i hi0 hi5
  have hi : (i : F) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt hi0 hi5 ((CharP.cast_eq_zero_iff F 5 i).mp he)
  obtain ⟨k, hk0, hk⟩ := huppert_II_10_4_norm_surjective J 5 hc hf
    (i : F)⁻¹ (by simp) (inv_ne_zero hi)
  let ku : Fˣ := Units.mk0 k hk0
  have ha : hermitianTorusAction J ku z = z ^ i := by
    apply Subtype.ext
    rw [central_pow J z hz i]
    apply Prod.ext
    · rw [hermitianTorusAction_fst, hz]; simp
    · rw [hermitianTorusAction_snd]
      change z.val.2 * (J.conj k)⁻¹ * k⁻¹ = (i : F) * z.val.2
      calc
        _ = z.val.2 * (k * J.conj k)⁻¹ := by rw [mul_inv]; ring
        _ = (i : F) * z.val.2 := by rw [hk, inv_inv, mul_comm]
  refine ⟨hermitianTorusSU J hJ ku, ?_⟩
  change hermitianTorusSU J hJ ku * hermitianUnipotentSU J hJ z * _ =
    hermitianUnipotentSU J hJ z ^ i
  apply (mul_inv_eq_iff_eq_mul).mpr
  rw [← map_pow, ← ha]
  exact Subtype.ext (hermitianTorusGL_mul_unipotent J ku z)

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity
