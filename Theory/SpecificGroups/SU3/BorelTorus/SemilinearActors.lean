module

public import Theory.SpecificGroups.SU3.BorelTorus.FieldActors
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
import Mathlib.Data.Nat.Factorization.Basic

/-!+# Two-power parameters for concrete unitary semilinear actors

The special-unitary formula below is an equality on actual matrix
representatives. Its projective counterpart is the existing
`HasUnitarySemilinearForm`, an equality in the actual PGL image.

A two-power-order actor with any semilinear formula has a formula whose
field parameter also has two-power order. Take the two-primary part of
the pair consisting of the actor and its field parameter, then a further
power restoring the first coordinate. This does not require uniqueness
of field parameters, an automorphism classification, or any assertion
about an involution power remaining outer.

Source: the semilinear description in GLS3, Theorem 2.5.12(a,d,f) and
Section 2.7; the two-primary calculation needed in Aschbacher–Smith,
proof of 13.8.20, printed p.954. Semilinear coverage itself remains an
explicit earlier classification input.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The special-unitary analogue of the concrete projective semilinear
formula, retaining equality of the actual GL representatives. -/
@[expose] public def HasSpecialUnitarySemilinearForm
    (a : MulAut J.specialSubgroup) (σ : E ≃+* E) : Prop :=
  ∃ u : J.unitarySubgroup, ∀ x : J.specialSubgroup,
    (a x).val = u.val * Matrix.GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹

private theorem field_map_unitary [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (σ : E ≃+* E) (u : J.unitarySubgroup) :
    Matrix.GeneralLinearGroup.map σ.toRingHom u.val ∈ J.unitarySubgroup := by
  have hform : J.form.map σ = J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hadj : J.conjTranspose (u.val.val.map σ) = (J.conjTranspose u.val.val).map σ := by
    let := finiteFieldAut_isCyclic (E := E)
    let := IsCyclic.commGroup (α := E ≃+* E)
    ext i j
    exact congrArg (fun f : E ≃+* E => f (u.val.val j i)) (Commute.all J.conj σ).eq
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (u.val.val.map σ) * J.form * u.val.val.map σ = J.form
  rw [hadj, ← hform, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A.map σ)
    ((J.mem_unitarySubgroup_iff _).mp u.property)

/-- The identity has the identity-field special-unitary formula. -/
public theorem HasSpecialUnitarySemilinearForm.one :
    J.HasSpecialUnitarySemilinearForm 1 1 := by
  refine ⟨1, fun x => ?_⟩
  change x.val = 1 * Matrix.GeneralLinearGroup.map (RingHom.id E) x.val * 1⁻¹
  simp

/-- Composition multiplies the field parameters on actual special-unitary
matrix representatives. -/
public theorem HasSpecialUnitarySemilinearForm.mul [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {a b : MulAut J.specialSubgroup} {σ τ : E ≃+* E}
    (ha : J.HasSpecialUnitarySemilinearForm a σ)
    (hb : J.HasSpecialUnitarySemilinearForm b τ) :
    J.HasSpecialUnitarySemilinearForm (a * b) (σ * τ) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  let w : J.unitarySubgroup :=
    ⟨Matrix.GeneralLinearGroup.map σ.toRingHom v.val, field_map_unitary J hJ σ v⟩
  refine ⟨u * w, fun x => ?_⟩
  change (a (b x)).val =
    (u.val * Matrix.GeneralLinearGroup.map σ.toRingHom v.val) *
      Matrix.GeneralLinearGroup.map (σ * τ).toRingHom x.val *
      (u.val * Matrix.GeneralLinearGroup.map σ.toRingHom v.val)⁻¹
  have hcomp : Matrix.GeneralLinearGroup.map (σ * τ).toRingHom x.val =
      Matrix.GeneralLinearGroup.map σ.toRingHom
        (Matrix.GeneralLinearGroup.map τ.toRingHom x.val) := by
    apply Units.ext
    rfl
  rw [hu, hv, hcomp]
  simp [map_mul, map_inv, mul_assoc]

/-- Powers preserve the special-unitary formula with the matching field power. -/
public theorem HasSpecialUnitarySemilinearForm.pow [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {a : MulAut J.specialSubgroup} {σ : E ≃+* E}
    (ha : J.HasSpecialUnitarySemilinearForm a σ) (k : ℕ) :
    J.HasSpecialUnitarySemilinearForm (a ^ k) (σ ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using HasSpecialUnitarySemilinearForm.one J
  | succ k ih => simpa only [pow_succ] using ih.mul J hJ ha

/-- Powers preserve the projective formula without choosing lifts of the
projective group or assuming uniqueness of the field parameter. -/
public theorem HasUnitarySemilinearForm.pow [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} {σ : E ≃+* E}
    (ha : J.HasUnitarySemilinearForm a σ) (k : ℕ) :
    J.HasUnitarySemilinearForm (a ^ k) (σ ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    refine ⟨1, fun x => ?_⟩
    change x.val = Matrix.ProjGenLinGroup.mk 1 *
      Matrix.ProjGenLinGroup.map (RingHom.id E) x.val * (Matrix.ProjGenLinGroup.mk 1)⁻¹
    simp [Matrix.ProjGenLinGroup.map_id]
  | succ k ih => simpa only [pow_succ] using ih.mul J hJ ha

private theorem two_power_lift {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (x : G) {r : ℕ} (hx : (f x) ^ (2 ^ r) = 1) :
    ∃ k s : ℕ, (f x) ^ k = f x ∧ (x ^ k) ^ (2 ^ s) = 1 := by
  obtain ⟨s, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 2 (by decide)
  have hcop : m.Coprime (orderOf (f x)) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hm).symm.pow_right r).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨m * b, s, ?_, ?_⟩
  · simpa only [pow_mul] using hb
  · rw [← pow_mul, show m * b * 2 ^ s = 2 ^ s * m * b by ring,
      ← he, pow_mul, pow_orderOf_eq_one, one_pow]

/-- A two-power special-unitary actor admits a two-power field parameter
whenever it admits any semilinear formula. -/
public theorem HasSpecialUnitarySemilinearForm.exists_twoPower_field [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {a : MulAut J.specialSubgroup} {σ : E ≃+* E}
    (ha : J.HasSpecialUnitarySemilinearForm a σ)
    {r : ℕ} (hr : a ^ (2 ^ r) = 1) :
    ∃ τ : E ≃+* E, J.HasSpecialUnitarySemilinearForm a τ ∧
      ∃ s : ℕ, τ ^ (2 ^ s) = 1 := by
  let : Finite (E ≃+* E) := Finite.of_injective
    (fun τ : E ≃+* E => (τ : E → E)) DFunLike.coe_injective
  let : Finite (MulAut J.specialSubgroup) := Finite.of_injective
    (fun b : MulAut J.specialSubgroup => (b : J.specialSubgroup → J.specialSubgroup))
    DFunLike.coe_injective
  obtain ⟨k, s, hk, hs⟩ := two_power_lift
    (MonoidHom.fst (MulAut J.specialSubgroup) (E ≃+* E)) (a, σ) hr
  change a ^ k = a at hk
  refine ⟨σ ^ k, ?_, s, ?_⟩
  · simpa only [hk] using ha.pow J hJ k
  · exact congrArg Prod.snd hs

/-- A two-power projective actor admits a two-power field parameter. The
argument retains the genuine projective formula, including its scalar kernel. -/
public theorem HasUnitarySemilinearForm.exists_twoPower_field [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} {σ : E ≃+* E}
    (ha : J.HasUnitarySemilinearForm a σ) {r : ℕ} (hr : a ^ (2 ^ r) = 1) :
    ∃ τ : E ≃+* E, J.HasUnitarySemilinearForm a τ ∧
      ∃ s : ℕ, τ ^ (2 ^ s) = 1 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Finite (E ≃+* E) := Finite.of_injective
    (fun τ : E ≃+* E => (τ : E → E)) DFunLike.coe_injective
  let : Finite (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) := Finite.of_injective
    (fun b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) =>
      (b : ProjectiveSpecialUnitaryMatrixGroup J → ProjectiveSpecialUnitaryMatrixGroup J))
    DFunLike.coe_injective
  obtain ⟨k, s, hk, hs⟩ := two_power_lift
    (MonoidHom.fst (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (E ≃+* E)) (a, σ) hr
  change a ^ k = a at hk
  refine ⟨σ ^ k, ?_, s, ?_⟩
  · simpa only [hk] using ha.pow J hJ k
  · exact congrArg Prod.snd hs

end BenderSuzuki.MatrixGroups.HermitianForm
