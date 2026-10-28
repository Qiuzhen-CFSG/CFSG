module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots
public import Theory.GroupTheory.PGroup.RationalExtraspecial
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Rational extraspecial root subgroups of prime-field PSU₃

The genuine Hermitian root coordinates satisfy
`b + conj b + a * conj a = 0`. Their projective image has order p³,
with derived subgroup equal to its center of order p, by Huppert II.10.12.
The first coordinate is additive; in characteristic p its pth power
vanishes, proving that the central quotient is elementary abelian.

A nonzero trace-zero second coordinate gives a nonidentity central root.
The diagonal torus scales this coordinate by the inverse norm. Norm
surjectivity therefore realizes every nonzero prime-field scalar by
conjugation in the actual projective special unitary group. A Hermitian
basis change transports the entire configuration to an arbitrary form.

Sources: Huppert, *Endliche Gruppen I*, II.10.4 and II.10.12. This is the
local geometry for the rational-extraspecial proof of the degree bound
used in Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
and Aschbacher–Smith K.2, printed p.453. No representation or covering
classification is assumed here.
-/

noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeRootConfiguration
open OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private def rootEquiv : hermitianUnipotentCoord J ≃* rootGroup J hJ :=
  MulEquiv.ofBijective (root J hJ).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (root_injective J hJ),
      (root J hJ).rangeRestrict_surjective⟩

private theorem rootEquiv_val (z : hermitianUnipotentCoord J) :
    (rootEquiv J hJ z : ProjectiveSpecialUnitaryMatrixGroup J) = root J hJ z := rfl

private theorem root_structure [Finite F] {q : ℕ}
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Nat.card (rootGroup J hJ) = q ^ 3 ∧
    commutator (rootGroup J hJ) = center (rootGroup J hJ) ∧
    Nat.card (center (rootGroup J hJ)) = q := by
  obtain ⟨_, _, _, _, _, _, hroot, _⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, _, _, _, _, _, _, _, hc, hd, hdc, _, _, ⟨e, he⟩, _⟩ := hroot
  have heq (z : hermitianUnipotentCoord J) :
      (e z : ProjectiveSpecialUnitaryMatrixGroup J) = root J hJ z := by
    obtain ⟨M, hM, heM⟩ := he z
    apply Subtype.ext
    rw [heM]
    change ProjGenLinGroup.mk M = ProjGenLinGroup.mk (hermitianUnipotentGL J z)
    congr 1
    exact Units.ext hM
  have hR : R = rootGroup J hJ := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
      exact ⟨z, (heq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro ⟨z, rfl⟩
      rw [← heq z]
      exact (e z).property
  subst R
  exact ⟨hc, hd, hd ▸ hdc⟩

private theorem coord_center_of_fst_zero (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    z ∈ center (hermitianUnipotentCoord J) := by
  apply mem_center_iff.mpr
  intro w
  apply Subtype.ext
  apply Prod.ext
  · change w.val.1 + z.val.1 = z.val.1 + w.val.1
    exact add_comm _ _
  · change w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 =
      z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1
    simp [hz, add_comm]

private def firstCoordinate : hermitianUnipotentCoord J →* Multiplicative F where
  toFun z := Multiplicative.ofAdd z.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem coord_pow_fst {p : ℕ} [CharP F p] (z : hermitianUnipotentCoord J) :
    (z ^ p).val.1 = 0 := by
  have h := congrArg Multiplicative.toAdd (map_pow (firstCoordinate J) z p)
  change (z ^ p).val.1 = p • z.val.1 at h
  simpa [nsmul_eq_mul, CharP.cast_eq_zero F p] using h

/-- The actual projective root image is extraspecial in prime characteristic.
The elementary abelian quotient is proved using the first additive coordinate. -/
public theorem rootGroup_isExtraspecial [Finite F] {p : ℕ} [CharP F p]
    (hp : p.Prime) (hcard : Nat.card F = p ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p) :
    IsExtraspecial p (rootGroup J hJ) := by
  obtain ⟨hc, hd, hzc⟩ := root_structure J hJ hcard hfixed
  refine ⟨hzc, ?_, ?_⟩
  · refine
      { toIsMulCommutative :=
          Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hd.le
        exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center (rootGroup J hJ)) x
    obtain ⟨z, rfl⟩ := (rootEquiv J hJ).surjective y
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← map_pow]
    exact (centerCongr (rootEquiv J hJ)
      ⟨z ^ p, coord_center_of_fst_zero J _ (coord_pow_fst J z)⟩).property
  · apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let : Subsingleton (rootGroup J hJ ⧸ center (rootGroup J hJ)) := hs
    have hh := card_eq_card_quotient_mul_card_subgroup (center (rootGroup J hJ))
    rw [hc, hzc, Nat.card_unique, one_mul] at hh
    have hp3 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by decide)
    simp [hh] at hp3

private theorem pow_fst (z : hermitianUnipotentCoord J) (i : ℕ) :
    (z ^ i).val.1 = (i : F) * z.val.1 := by
  have h := congrArg Multiplicative.toAdd (map_pow (firstCoordinate J) z i)
  change (z ^ i).val.1 = i • z.val.1 at h
  simpa [nsmul_eq_mul] using h

private theorem central_pow_snd (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) (i : ℕ) :
    (z ^ i).val.2 = (i : F) * z.val.2 := by
  induction i with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; rfl
  | succ i hi =>
    rw [pow_succ]
    change (z ^ i).val.2 + z.val.2 - (z ^ i).val.1 * J.conj z.val.1 = _
    rw [hz, map_zero, mul_zero, sub_zero, hi, Nat.cast_succ]
    ring

private theorem central_fusion [Finite F] {p : ℕ} [CharP F p]
    (hcard : Nat.card F = p ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p)
    (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0)
    (i : ℕ) (hi0 : 0 < i) (hip : i < p) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      g * root J hJ z * g⁻¹ = (root J hJ z) ^ i := by
  have hi : (i : F) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt hi0 hip ((CharP.cast_eq_zero_iff F p i).mp h)
  obtain ⟨k, hk0, hk⟩ := huppert_II_10_4_norm_surjective J p hcard hfixed
    (i : F)⁻¹ (by simp) (inv_ne_zero hi)
  let ku : Fˣ := Units.mk0 k hk0
  have ha : hermitianTorusAction J ku z = z ^ i := by
    apply Subtype.ext
    apply Prod.ext
    · rw [hermitianTorusAction_fst, pow_fst, hz]
      simp
    · rw [hermitianTorusAction_snd, central_pow_snd J z hz]
      change z.val.2 * (J.conj k)⁻¹ * k⁻¹ = (i : F) * z.val.2
      calc
        _ = z.val.2 * (k * J.conj k)⁻¹ := by rw [mul_inv]; ring
        _ = (i : F) * z.val.2 := by rw [hk, inv_inv, mul_comm]
  refine ⟨hermitianTorusPSU J hJ ku, ?_⟩
  change hermitianTorusPSU J hJ ku * hermitianUnipotentPSU J hJ z * _ = _
  rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right, ha, map_pow]

private theorem exists_trace_zero_ne_zero [Finite F] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p) :
    ∃ b : F, b ≠ 0 ∧ b + J.conj b = 0 := by
  have hn : ∃ x : F, J.conj x ≠ x := by
    by_contra! hn
    let e : {x : F // J.conj x = x} ≃ F :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, hn x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hh := Nat.card_congr e
    rw [hcard, hfixed] at hh
    nlinarith [hp.one_lt]
  obtain ⟨x, hx⟩ := hn
  refine ⟨x - J.conj x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, J.conj_involutive]
  ring

include hJ in
private theorem standard_configuration [Finite F] {p : ℕ} [CharP F p]
    (hp : p.Prime) (hcard : Nat.card F = p ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p) :
    Theory.GroupTheory.HasRationalExtraspecialSubgroup
      (ProjectiveSpecialUnitaryMatrixGroup J) p := by
  obtain ⟨b, hb0, hb⟩ := exists_trace_zero_ne_zero J hp hcard hfixed
  let z : hermitianUnipotentCoord J := ⟨(0, b), by simpa using hb⟩
  have hz : z.val.1 = 0 := rfl
  have hz1 : z ≠ 1 := by
    intro hh
    exact hb0 (congrArg (fun w : hermitianUnipotentCoord J => w.val.2) hh)
  refine ⟨rootGroup J hJ, rootGroup_isExtraspecial J hJ hp hcard hfixed,
    (root_structure J hJ hcard hfixed).1, rootEquiv J hJ z, ?_, ?_, ?_⟩
  · exact (centerCongr (rootEquiv J hJ) ⟨z, coord_center_of_fst_zero J z hz⟩).property
  · exact (rootEquiv J hJ).map_ne_one_iff.mpr hz1
  · intro i hi0 hip
    exact central_fusion J hJ hcard hfixed z hz i hi0 hip

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeRootConfiguration

namespace Theory.GroupTheory
open Subgroup

/-- An ambient group equivalence transports both the extraspecial subgroup
and the literal rational conjugacy equations. -/
public theorem HasRationalExtraspecialSubgroup.of_mulEquiv
    {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H)
    (h : HasRationalExtraspecialSubgroup G p) : HasRationalExtraspecialSubgroup H p := by
  obtain ⟨P, hP, hc, z, hz, hz1, hf⟩ := h
  let Q := P.map e.toMonoidHom
  let f : P ≃* Q := P.equivMapOfInjective e.toMonoidHom e.injective
  have hfv (x : P) : (f x : H) = e x := rfl
  refine ⟨Q, IsExtraspecial.of_mulEquiv f hP,
    (Nat.card_congr f.toEquiv).symm.trans hc, f z, ?_, f.map_ne_one_iff.mpr hz1, ?_⟩
  · exact (centerCongr f ⟨z, hz⟩).property
  · intro i hi0 hip
    obtain ⟨g, hg⟩ := hf i hi0 hip
    refine ⟨e g, ?_⟩
    simpa only [map_mul, map_inv, map_pow, hfv] using congrArg e hg
end Theory.GroupTheory

namespace BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter.FormTransport

/-- Every ternary unitary projective group over a quadratic prime field has
an order-p³ rational extraspecial subgroup, for the original Hermitian form. -/
public theorem hasRationalExtraspecialSubgroup_of_prime
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p) :
    Theory.GroupTheory.HasRationalExtraspecialSubgroup
      (ProjectiveSpecialUnitaryMatrixGroup J) p := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj p 1 (by decide) (by simpa only [pow_one] using hcard)
      (by simpa only [pow_one] using hconj)
  obtain ⟨e⟩ := exists_projectiveEquiv J p hcard hfixed
  exact (OddPrimeRootConfiguration.standard_configuration (standardForm J)
    rfl hp hcard hfixed).of_mulEquiv e.symm

end BenderSuzuki.MatrixGroups.HermitianForm
