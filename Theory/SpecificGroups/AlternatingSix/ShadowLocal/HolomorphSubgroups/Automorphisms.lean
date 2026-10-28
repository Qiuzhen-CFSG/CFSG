module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Coordinates
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrder
public import Theory.GroupTheory.PGroup.AbelianOmegaFrattini

/-!
# Automorphism primes of normal subgroups of the cyclic-eight holomorph

Every prime dividing the automorphism-group order of a normal subgroup of
C₈ ⋊ (Z/8)ˣ is two or three. For an abelian normal subgroup, conjugation by
the rotation confines its involutions to an explicit elementary four.
Its Frattini quotient therefore has order at most four, detecting every odd
prime automorphism. For a nonabelian subgroup, the small-two-group
odd-automorphism bound applies; the whole model contains an elementary eight,
which supplies the additional witness needed at order thirty-two.

Source: the local calculation used in Aschbacher–Smith, *The Classification
of Quasithin Groups*, Lemma 2.5.22, printed p.567. This direct proof avoids the
false unrestricted derived-subgroup dichotomy in the printed argument.
Transport to a Sylow subgroup of Aut(A₆) is a separate step.
-/

open Subgroup
open scoped IsMulCommutative
namespace AlternatingSix.ShadowLocal.Holomorph
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem two_group : IsPGroup 2 Model :=
  IsPGroup.of_card (by simpa using card_model : Nat.card Model = 2 ^ 5)

private def eightEmbedding : (E4 × C2) →* Model where
  toFun i := centralTranspositionEmbedding i.1 * reflection ^ i.2.toAdd.val
  map_one' := rfl
  map_mul' := by decide +kernel

private theorem eightEmbedding_injective : Function.Injective eightEmbedding := by decide +kernel

private theorem elementary_eight : ∃ E : Subgroup Model,
    IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
  let E := eightEmbedding.range
  have hE : IsElementaryAbelian 2 E := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · infer_instance
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      rintro ⟨x, i, rfl⟩
      apply Subtype.ext
      change eightEmbedding i ^ 2 = 1
      rw [← map_pow]
      have h : i ^ 2 = 1 := by revert i; decide +kernel
      rw [h, map_one]
  refine ⟨E, hE, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective eightEmbedding_injective).toEquiv]
  simp [E4, C2]

private theorem abelian_normal_omega_le (R : Subgroup Model) [R.Normal]
    [IsMulCommutative R] :
    (omega₁ R (p := 2)).map R.subtype ≤ centralTranspositionEmbedding.range := by
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  intro x hx
  have hx2 : (x : Model) ^ 2 = 1 :=
    congrArg Subtype.val (by simpa using hx : x ^ 2 = 1)
  have hconj := (inferInstance : R.Normal).conj_mem (x : Model) x.property rotation
  have hcomm : (x : Model) * (rotation * (x : Model) * rotation⁻¹) =
      (rotation * (x : Model) * rotation⁻¹) * (x : Model) :=
    congrArg Subtype.val (mul_comm x (⟨_, hconj⟩ : R))
  have table : ∀ x : Model, x ^ 2 = 1 →
      x * (rotation * x * rotation⁻¹) = (rotation * x * rotation⁻¹) * x →
      ∃ i, centralTranspositionEmbedding i = x := by decide +kernel
  exact table x hx2 hcomm

private theorem abelian_normal_frattini_card_le_four (R : Subgroup Model) [R.Normal]
    [IsMulCommutative R] : Nat.card (R ⧸ frattini R) ≤ 4 := by
  rw [(two_group.to_subgroup R).card_frattini_quotient_eq_card_omega_one]
  have h := Subgroup.card_le_of_le (abelian_normal_omega_le R)
  rw [Subgroup.card_map_of_injective R.subtype_injective,
    ← Nat.card_congr (MonoidHom.ofInjective centralTranspositionEmbedding_injective).toEquiv] at h
  simpa [E4, C2] using h

/-- Every prime in the automorphism group of a normal subgroup is two or three. -/
public theorem normal_subgroup_automorphism_primes (R : Subgroup Model) [R.Normal]
    {p : ℕ} (hp : p.Prime) (hdiv : p ∣ Nat.card (MulAut R)) : p = 2 ∨ p = 3 := by
  classical
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  right
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := MulAut R) p hdiv
  let A := zpowers a
  have hA : Nat.card A = p := (Nat.card_zpowers a).trans ha
  have hodd : Odd (Nat.card A) := by rw [hA]; exact hp.odd_of_ne_two hp2
  by_cases hcomm : IsMulCommutative R
  · let := hcomm
    let V := R ⧸ frattini R
    let f : A →* MulAut V := (Subgroup.quotientAut (frattini R)).comp A.subtype
    have hf : Function.Injective f :=
      SmallNonabelianTwoGroup.odd_frattini_action_injective (two_group.to_subgroup R) A hodd
    let g : MulAut V →* Equiv.Perm V := MulAction.toPermHom (MulAut V) V
    have hg : Function.Injective g := MulAction.toPerm_injective
    have hpd : p ∣ Nat.card (Equiv.Perm V) := by
      rw [← hA]
      exact Subgroup.card_dvd_of_injective (g.comp f) (hg.comp hf)
    let := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card] at hpd
    have h24 : p ∣ 24 := hpd.trans
      (Nat.factorial_dvd_factorial (abelian_normal_frattini_card_le_four R))
    have hcases : p = 2 ∨ p = 3 := by
      have : p ∣ 2 ^ 3 * 3 := h24
      rcases hp.dvd_mul.mp this with h | h
      · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
      · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one)
    exact hcases.resolve_left hp2
  · have hbound : Nat.card R ≤ 32 := by
      exact card_model ▸ R.card_le_card_group
    have heights : Nat.card R = 32 → ∃ E : Subgroup R,
        IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
      intro hR
      have htop : R = ⊤ := R.eq_top_of_card_eq (hR.trans card_model.symm)
      obtain ⟨E, hE, hcard⟩ := elementary_eight
      let := hE
      let e : Model ≃* R := (Subgroup.topEquiv (G := Model)).symm.trans
        (MulEquiv.subgroupCongr htop.symm)
      refine ⟨E.map e.toMonoidHom, IsElementaryAbelian.map _, ?_⟩
      rw [Subgroup.card_map_of_injective e.injective, hcard]
    have h := SmallNonabelianTwoGroup.small_nonabelian_two_group_odd_order_bound
      (two_group.to_subgroup R) hcomm hbound heights A hodd
    rw [hA] at h
    have hp9 : p ∣ 3 ^ 2 := h.trans (by split_ifs <;> norm_num)
    exact ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow hp9)).resolve_left hp.ne_one

end AlternatingSix.ShadowLocal.Holomorph
