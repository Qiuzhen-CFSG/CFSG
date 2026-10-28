module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.Construction
public import Theory.Mathieu.M12.Properties.SylowAutomorphisms
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# The Aut(M₁₂) Sylow omega-center

The faithful inner-automorphism image of the known M₁₂ Sylow subgroup lies
in an actual Sylow two-subgroup of `MulAut M12`. Its center centralizes that
image, hence fixes the original Sylow subgroup pointwise. The intrinsic
rigidity calculation bounds this center by the distinguished involution
group. Nontriviality of the omega-center in a nontrivial finite two-group
then gives order two. Sylow conjugacy transports the result to every Sylow
subgroup of the full automorphism group.

This proves the concrete exclusion needed in Aschbacher–Smith, Lemma 15.4.15,
printed p.1161, for F.1.12(13), printed p.263. It uses the actual Witt-design
M₁₂ carrier and does not rely on the inconsistent printed core description.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair

private theorem inner_injective : Function.Injective (MulAut.conj : M12 →* MulAut M12) :=
  Theory.GroupTheory.conj_injective_of_center_eq_bot m12_center_eq_bot

private theorem fixes_of_commutes_inner (f : MulAut M12) (x : M12)
    (h : MulAut.conj x * f = f * MulAut.conj x) : f x = x := by
  apply inner_injective
  apply MulEquiv.ext
  intro y
  have he := congrArg (fun g : MulAut M12 => g (f⁻¹ y)) h
  change x * f (f⁻¹ y) * x⁻¹ = f (x * f⁻¹ y * x⁻¹) at he
  change f x * y * (f x)⁻¹ = x * y * x⁻¹
  simpa only [map_mul, map_inv, MulAut.apply_inv_self] using he.symm

private theorem omega_nontrivial {A : Type*} [Group A] [Finite A]
    (P : Subgroup A) (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    Stellmacher.omegaOneCenterAmbient P ≠ ⊥ := by
  let _ : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  let _ : Nontrivial (center P) := hP.center_nontrivial
  have hC : IsPGroup 2 (center P) := hP.to_subgroup (center P)
  obtain ⟨n, hn, hc⟩ := hC.nontrivial_iff_card.mp inferInstance
  have htwo : 2 ∣ Nat.card (center P) := by
    rw [hc]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot (G := P) (center P) 2 htwo
  intro heq
  apply hinner
  apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
  simpa [Stellmacher.omegaOneCenterAmbient] using heq

/-- Every Sylow two-subgroup of the full automorphism group of the actual
Witt-design M₁₂ has omega-center of order two. -/
theorem autm12_sylow_omega_center_card
    (P : Sylow 2 (MulAut M12)) :
    Nat.card (Stellmacher.omegaOneCenterAmbient (P : Subgroup (MulAut M12))) = 2 := by
  have hIS : IsPGroup 2 (sylowCandidate.map MulAut.conj) :=
    commonSylow.isPGroup'.map MulAut.conj
  obtain ⟨Q, hQ⟩ := hIS.exists_le_sylow
  have hupper : Stellmacher.omegaOneCenterAmbient (Q : Subgroup (MulAut M12)) ≤
      distinguished.map MulAut.conj := by
    intro f hf
    have hc := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hf).2.2
    have hfix (x : M12) (hx : x ∈ sylowCandidate) : f x = x :=
      fixes_of_commutes_inner f x (hc (MulAut.conj x) (hQ (mem_map_of_mem _ hx)))
    rcases SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow f hfix with rfl | rfl
    · exact one_mem _
    · exact mem_map_of_mem MulAut.conj (mem_zpowers z)
  have hcard : Nat.card (distinguished.map MulAut.conj) = 2 := by
    rw [← Nat.card_congr (distinguished.equivMapOfInjective MulAut.conj
      inner_injective).toEquiv, card_distinguished]
  have hle := card_le_of_le hupper
  rw [hcard] at hle
  have hS : sylowCandidate ≠ ⊥ := by
    intro he
    have hh := card_sylowCandidate
    rw [he, card_bot] at hh
    omega
  have hQne : (Q : Subgroup (MulAut M12)) ≠ ⊥ := by
    intro he
    have hm : sylowCandidate.map MulAut.conj = ⊥ := le_bot_iff.mp (he ▸ hQ)
    exact hS ((map_eq_bot_iff_of_injective _ inner_injective).mp hm)
  have hlo := (Stellmacher.omegaOneCenterAmbient (Q : Subgroup (MulAut M12))).one_lt_card_iff_ne_bot.mpr
    (omega_nontrivial _ Q.isPGroup' hQne)
  have hresult : Nat.card (Stellmacher.omegaOneCenterAmbient (Q : Subgroup (MulAut M12))) = 2 := by omega
  rw [← omega_center_card_eq_of_equiv (Q : Subgroup (MulAut M12))
    (P : Subgroup (MulAut M12)) (Q.equiv P)]
  exact hresult

/-- F.1.12(13)'s actual automorphism-group Sylow overlap cannot have the
omega-center order four supplied by 15.4.14. -/
theorem not_autm12_overlap {G : Type*} [Group G] (T : Subgroup G)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient T) = 4)
    (P : Sylow 2 (MulAut M12)) : ¬ Nonempty (T ≃* P) := by
  rintro ⟨e⟩
  have he := omega_center_card_eq_of_equiv T (P : Subgroup (MulAut M12)) e
  have hp := autm12_sylow_omega_center_card P
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
