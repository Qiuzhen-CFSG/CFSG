module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound
public import Theory.GroupTheory.CoveringComparisonKernelCard
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Unitary descent to a cover with three-group kernel

The constructed universal cover maps onto both the actual SU₃ scalar cover
and the prescribed quasisimple cover. Its kernel over SU₃ has order prime
to three: if the scalar kernel is cubic this follows from exclusion of nine
in the universal kernel; otherwise it follows from exclusion of three.
The image of this comparison kernel in the prescribed three-group kernel
therefore vanishes. Descent gives SU₃ → L over the original projective map.

At prime parameter, the defining-prime calculation and cyclic Sylow transfer
already exclude three outside the scalar-cubic congruence. Only the possible
extra three-primary factor remains an input. If the target kernel is
nontrivial, scalar-kernel cardinalities make the descended map an isomorphism.
No other primary part of the universal kernel is bounded here.

Source: Aschbacher–Smith F.6.18, printed pp.309–310; the covering convention
and the canonical scalar kernel are I.1.1–I.1.4, printed pp.407–408.
-/

public section
noncomputable section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.ThreeCentralDescent

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem comparison_kernel_le
    {U H L S : Type*} [Group U] [Finite U] [Group H] [Group L] [Group S]
    (π : H →* S) (f : L →* S) (a : U →* H) (b : U →* L)
    (hfac : π.comp a = f.comp b) (hnot3 : ¬ 3 ∣ Nat.card a.ker)
    (hthree : IsPGroup 3 f.ker) : a.ker ≤ b.ker := by
  intro x hx
  have hbx : b x ∈ f.ker := by
    change f (b x) = 1
    rw [← MonoidHom.comp_apply, ← hfac, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp hx, map_one]
  let z : f.ker := ⟨b x, hbx⟩
  have hxpow : x ^ Nat.card a.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : a.ker)))
  have hzpow : z ^ Nat.card a.ker = 1 := by
    apply Subtype.ext
    change b x ^ Nat.card a.ker = 1
    rw [← map_pow, hxpow, map_one]
  have hz : z = 1 := by
    apply (hthree.powEquiv' hnot3).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hzpow
  exact congrArg Subtype.val hz

universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

private theorem exists_lift_of_three_primary {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hnot3 : q % 3 ≠ 2 →
      ¬ 3 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnine : q % 3 = 2 →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    {L : Type v} [Group L] [Finite L] [IsQuasisimple L]
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hthree : IsPGroup 3 f.ker) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      f.comp k = J.specialToProjective := by
  let := special_isQuasisimple J hq hcard hconj
  let := projective_isQuasisimple J hq hcard hconj
  let c := universalQuasisimpleCover (ProjectiveSpecialUnitaryMatrixGroup J)
  let π := covering J
  have hcH : Covering.IsUniversal.{u,u,u} c := universalQuasisimpleCover_isUniversal _
  let a := hcH.lift π
  have hπa : π.toMonoidHom.comp a.toMonoidHom = c.toMonoidHom :=
    congrArg Covering.toMonoidHom (hcH.lift_fac π)
  have hcount : Nat.card c.toMonoidHom.ker =
      Nat.card a.toMonoidHom.ker * Nat.gcd 3 (q + 1) := by
    have h := kernel_card_eq_mul_of_surjective_factor
      c.toMonoidHom π.toMonoidHom a.toMonoidHom π.surjective a.surjective hπa
    change Nat.card c.toMonoidHom.ker =
      Nat.card a.toMonoidHom.ker * Nat.card (covering J).toMonoidHom.ker at h
    simpa only [covering_toMonoidHom, card_kernel J hcard hconj] using h
  have hnot : ¬ 3 ∣ Nat.card a.toMonoidHom.ker := by
    intro hd
    by_cases hm : q % 3 = 2
    · apply hnine hm
      change 9 ∣ Nat.card c.toMonoidHom.ker
      have hg : Nat.gcd 3 (q + 1) = 3 := by
        rw [Nat.gcd_comm]
        exact Nat.gcd_eq_right_iff_dvd.mpr (Nat.dvd_of_mod_eq_zero (by omega))
      rw [hcount, hg]
      exact Nat.mul_dvd_mul hd (dvd_refl 3)
    · apply hnot3 hm
      change 3 ∣ Nat.card c.toMonoidHom.ker
      rw [hcount]
      exact dvd_mul_of_dvd_left hd _
  let g : Covering L (ProjectiveSpecialUnitaryMatrixGroup J) := ⟨f, hf⟩
  have hcL : Covering.IsUniversal.{u,u,v} c := universalQuasisimpleCover_isUniversal _
  let b := hcL.lift g
  have hfb : f.comp b.toMonoidHom = c.toMonoidHom :=
    congrArg Covering.toMonoidHom (hcL.lift_fac g)
  have hkill : a.toMonoidHom.ker ≤ b.toMonoidHom.ker :=
    comparison_kernel_le π.toMonoidHom f a.toMonoidHom b.toMonoidHom
      (hπa.trans hfb.symm) hnot hthree
  let k : J.specialSubgroup →* L :=
    a.toMonoidHom.liftOfSurjective a.surjective ⟨b.toMonoidHom, hkill⟩
  have hk : k.comp a.toMonoidHom = b.toMonoidHom :=
    MonoidHom.liftOfRightInverse_comp _ _ _ _
  have hks : Function.Surjective k := by
    intro y
    obtain ⟨x, rfl⟩ := b.surjective y
    exact ⟨a x, DFunLike.congr_fun hk x⟩
  have hfac : f.comp k = π.toMonoidHom := by
    apply (MonoidHom.cancel_right a.surjective).mp
    rw [MonoidHom.comp_assoc, hk, hfb]
    exact hπa.symm
  refine ⟨k, hks, ?_⟩
  change f.comp k = (covering J).toMonoidHom at hfac
  simpa only [covering_toMonoidHom] using hfac

/-- At prime parameter, a three-group source kernel needs only the possible
extra cubic factor excluded from the universal kernel. The descended map
commutes with the given projective projection, in the original Hermitian basis. -/
theorem exists_lift_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hnine : p % 3 = 2 →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    {L : Type v} [Group L] [Finite L] [IsQuasisimple L]
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hthree : IsPGroup 3 f.ker) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      f.comp k = J.specialToProjective := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  apply exists_lift_of_three_primary J hp2 hcard hconj _ hnine f hf hthree
  intro hm
  by_cases hp3 : p = 3
  · have h := OddKernelBound.not_defining_prime_dvd_universal_kernel
      J hp hodd hcard hconj
    simpa only [hp3] using h
  · have hm0 : p % 3 ≠ 0 := by
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_of_mod_eq_zero h)).symm
    let := projective_isQuasisimple J hp2 hcard hconj
    exact OddKernelBound.not_three_dvd_kernel_of_mod_one J (by omega)
      hcard hconj (by omega) (universalCover _)

/-- If the given three-group kernel is nontrivial, the descended SU₃ map
is an actual isomorphism over the prescribed projective projection. -/
theorem exists_equiv_prime_of_nontrivial_kernel {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hnine : p % 3 = 2 →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    {L : Type v} [Group L] [Finite L] [IsQuasisimple L]
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hthree : IsPGroup 3 f.ker) (hne : f.ker ≠ ⊥) :
    ∃ e : J.specialSubgroup ≃* L, f.comp e.toMonoidHom = J.specialToProjective := by
  obtain ⟨k, hks, hfac⟩ := exists_lift_prime J hp hodd hcard hconj hnine f hf hthree
  have hcount := kernel_card_eq_mul_of_surjective_factor
    J.specialToProjective f k hf hks hfac
  have hdiv : Nat.card f.ker ∣ Nat.card J.specialToProjective.ker :=
    kernel_card_dvd_of_surjective_factor J.specialToProjective f k hks hfac
  have hdπ : Nat.card J.specialToProjective.ker ∣ 3 := by
    rw [card_kernel J hcard hconj]
    exact Nat.gcd_dvd_left _ _
  have hfc : Nat.card f.ker = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (hdiv.trans hdπ) with hc | hc
    · exact (hne ((eq_bot_iff_card f.ker).mpr hc)).elim
    · exact hc
  have hb : Nat.card J.specialToProjective.ker ≤ 3 :=
    Nat.le_of_dvd (by decide : 0 < 3) hdπ
  have hkpos : 0 < Nat.card k.ker := Nat.card_pos
  have hkcard : Nat.card k.ker = 1 := by
    rw [hcount, hfc] at hb
    omega
  have hki : Function.Injective k :=
    k.ker_eq_bot_iff.mp ((eq_bot_iff_card k.ker).mpr hkcard)
  exact ⟨MulEquiv.ofBijective k ⟨hki, hks⟩, hfac⟩

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.ThreeCentralDescent
