module

public import Theory.SpecificGroups.SU3.ExtensionBorel.Actors
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.FieldFaithfulness
public import Theory.SpecificGroups.SU3.BinaryRootFrattini

/-!
# Removing outer two-elements above the full unitary root

A two-subgroup containing the inner root and preserving that root has an
outer involution whenever it has an outer element. Semilinear coverage gives
a power with involutory field part. Triangular factorization removes its root
factor inside the original subgroup. The remaining diagonal-field actor has
diagonal square of odd order, so its square is one. Field faithfulness shows
that this involution is still outer. This includes elements of order eight
and higher without inferring innerness from their involution powers.

Source: Huppert II.10.12; GLS3 Theorem 2.5.12 and Section 2.7. The application
is the nested strongly closed unitary branch of Aschbacher (1975), Lemma 3.4.
-/

public section
open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure
open BorelTorus BorelTorus.SemilinearActors ExtensionBorel
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

private theorem field_of_inner {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} {σ : E ≃+* E}
    (hsem : J.HasUnitarySemilinearForm a σ)
    (ha : a ∈ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range) : σ = 1 := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  have hi : J.HasUnitarySemilinearForm (MulAut.conj (J.specialToProjective u)) 1 :=
    (HasUnitarySemilinearForm.one_iff J).mpr ⟨⟨u.val, u.property.1⟩,
      (J.unitaryConj_special_is_inner u).symm⟩
  have hh := (hi.inv J hJ).mul J hJ hsem
  simp only [inv_mul_cancel, inv_one, one_mul] at hh
  exact J.semilinear_identity_field_eq_one n hn hJ hcard hfixed σ hh

private theorem diagonal_pow (d : GL (Fin 3) E)
    (hd : ∀ i j, i ≠ j → d.val i j = 0) : d ^ (Nat.card E - 1) = 1 := by
  let : Fintype E := Fintype.ofFinite E
  have he : d.val = Matrix.diagonal (fun i => d.val i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [hd i j hij, hij]
  have hn (i : Fin 3) : d.val i i ≠ 0 := by
    have ht := d.det_ne_zero
    rw [he, Matrix.det_diagonal] at ht
    exact (Finset.prod_ne_zero_iff.mp ht i (Finset.mem_univ i))
  apply Units.ext
  change d.val ^ (Nat.card E - 1) = 1
  rw [he, Matrix.diagonal_pow]
  have hp : (fun i => d.val i i ^ (Nat.card E - 1)) = fun _ => (1 : E) := by
    funext i
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card_sub_one_eq_one _ (hn i)
  change Matrix.diagonal (fun i => d.val i i ^ (Nat.card E - 1)) = 1
  rw [hp, Matrix.diagonal_one]

private theorem actor_pow {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (a : MulAut G) (d : H)
    (ha : ∀ x, f (a x) = d * f x * d⁻¹) {m : ℕ} (hd : d^m = 1) : a^m = 1 := by
  have hp (k : ℕ) (x : G) : f ((a^k) x) = d^k * f x * (d^k)⁻¹ := by
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, ih, ha, pow_succ]
      group
  apply MulEquiv.ext
  intro x
  apply hf
  simpa only [MulAut.one_apply, hd, one_mul, inv_one, mul_one] using hp m x

private theorem diagonal_field_square_one
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (σ : E ≃+* E)
    (d : J.unitarySubgroup) (hd : ∀ i j, i ≠ j → d.val.val i j = 0)
    (hσ : σ^2 = 1)
    (ha : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk d.val * ProjGenLinGroup.map σ.toRingHom x.val *
        (ProjGenLinGroup.mk d.val)⁻¹)
    {r n : ℕ} (hr : a ^ (2^r) = 1) (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2) : a^2 = 1 := by
  let v := d.val * GeneralLinearGroup.map σ.toRingHom d.val
  have hv : ∀ i j, i ≠ j → v.val i j = 0 := by
    intro i j hij
    change (d.val.val * d.val.val.map σ) i j = 0
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst k
      simp [hd i j hij]
    · simp [hd i k hik]
  have hp : (a^2) ^ (Nat.card E - 1) = 1 := by
    apply actor_pow (ProjectiveSpecialUnitaryMatrixGroup J).subtype Subtype.val_injective
      (a^2) (ProjGenLinGroup.mk v) ?_ (by rw [← map_pow, diagonal_pow v hv, map_one])
    intro x
    have hss : ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.map σ.toRingHom x.val) = x.val := by
      rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp]
      have hcomp : σ.toRingHom.comp σ.toRingHom = RingHom.id E := by
        have hh := congrArg RingEquiv.toRingHom hσ
        exact hh
      rw [hcomp, ProjGenLinGroup.map_id, MonoidHom.id_apply]
    change (a (a x)).val = _
    rw [ha, ha, map_mul, map_mul, map_inv, hss]
    simp only [v, map_mul, ProjGenLinGroup.map_mk, Subgroup.subtype_apply]
    group
  have hc : Nat.Coprime 2 (Nat.card E - 1) := by
    apply Nat.coprime_two_left.mpr
    rw [hcard]
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity))
      ((even_two.pow_of_ne_zero (by omega)).pow_of_ne_zero (by decide)) odd_one
  apply (pow_eq_one_iff_of_coprime (hc.pow_left r)).mp
  refine ⟨?_, hp⟩
  rw [← pow_mul, Nat.mul_comm 2, pow_mul, hr, one_pow]

private theorem involution_power {G : Type*} [Group G] (a : G)
    {r : ℕ} (hr : a^(2^r) = 1) (ha : a ≠ 1) :
    ∃ k : ℕ, (a^k)^2 = 1 ∧ a^k ≠ 1 := by
  induction r with
  | zero => simp only [pow_zero, pow_one] at hr; exact (ha hr).elim
  | succ r ih =>
    by_cases h : a^(2^r) = 1
    · exact ih h
    · exact ⟨2^r, by simpa only [← pow_mul, ← pow_succ] using hr, h⟩

/-- A two-subgroup containing the root inner group and preserving the root
has an outer involution whenever it has any outer element. -/
theorem root_containing_inner_of_involutions {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (B : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hB : IsPGroup 2 B)
    (hroot : (projectiveRoot J hJ).map MulAut.conj ≤ B)
    (hstable : ∀ a ∈ B, (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hi : ∀ a ∈ B, a^2 = 1 →
      a ∈ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range) :
    B ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
  intro a ha
  obtain ⟨σ, hσ⟩ := J.semilinear_coverage n hn hJ hcard hfixed a
  obtain ⟨r, hr⟩ := hB ⟨a, ha⟩
  have hr' : a^(2^r) = 1 := congrArg Subtype.val hr
  obtain ⟨τ, hτ, s, hs⟩ := hσ.exists_twoPower_field J hJ hr'
  by_cases ht : τ = 1
  · rw [ht] at hτ
    obtain ⟨u, hu⟩ := hτ
    have hu' : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        (a x).val = ProjGenLinGroup.mk u.val * x.val * (ProjGenLinGroup.mk u.val)⁻¹ := by
      intro x
      simpa only [show (1 : E ≃+* E).toRingHom = RingHom.id E from rfl,
        ProjGenLinGroup.map_id, MonoidHom.id_apply] using hu x
    obtain ⟨h10, h20, h21⟩ := projective_semilinear_upper J hJ hcard hfixed a 1 u hu (hstable a ha)
    obtain ⟨x, _, hx⟩ := projective_identity_field_mem_root_inner J hJ hcard
      (by omega) B hB hroot a ha u h10 h20 h21 hu'
    exact ⟨x, hx⟩
  · obtain ⟨k, hk, hkne⟩ := involution_power τ hs ht
    have hpow := hτ.pow J hJ k
    obtain ⟨u, hu⟩ := hpow
    obtain ⟨h10, h20, h21⟩ := projective_semilinear_upper J hJ hcard hfixed
      (a^k) (τ^k) u hu (hstable _ (B.pow_mem ha k))
    obtain ⟨z, d, hf, hd, _⟩ := upper_unitary_factorization J hJ u h10 h20 h21
    let c := MulAut.conj (hermitianUnipotentPSU J hJ z)
    have hc : c ∈ B := hroot ⟨_, ⟨z, rfl⟩, rfl⟩
    let b := c⁻¹ * a^k
    have hb : b ∈ B := B.mul_mem (B.inv_mem hc) (B.pow_mem ha k)
    have hform (x : ProjectiveSpecialUnitaryMatrixGroup J) :
        (b x).val = ProjGenLinGroup.mk d.val *
          ProjGenLinGroup.map (τ^k).toRingHom x.val * (ProjGenLinGroup.mk d.val)⁻¹ := by
      change ((MulAut.conj (hermitianUnipotentPSU J hJ z))⁻¹ ((a^k) x)).val = _
      rw [← map_inv, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu,
        hermitianUnipotentPSU_val, hf, map_mul]
      group
    obtain ⟨l, hl⟩ := hB ⟨b, hb⟩
    have hb2 := diagonal_field_square_one J b (τ^k) d hd hk hform
      (congrArg Subtype.val hl) (by omega : 0 < n) hcard
    exact False.elim (hkne (field_of_inner J hn hJ hcard hfixed ⟨d, hform⟩ (hi b hb hb2)))

end BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure
