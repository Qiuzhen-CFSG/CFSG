module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreCenter
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticLargeCoreMarking
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveNormalizerLift
public import Theory.SpecificGroups.ReeTwo.CoreFiveActionNormalization
public import Theory.SpecificGroups.ReeTwo.SquaringActionCensus

/-!
# The fourth power of an actual quintic squaring lift

The genuine original core marking transports the five-action to the native
Ree core. Its complete automorphism census makes every squaring automorphism
have fourth power one. Thus the fourth power of the actual ambient lift lies
in the original core center, and its eighth power is one. This excludes the
order-sixteen possibility while retaining both split and nonsplit lifts.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
private theorem squaring_order_four (ρ σ : MulAut ReeTwo.Core)
    (hρ : orderOf ρ = 5) (hsq : σ * ρ * σ⁻¹ = ρ ^ 2) : σ ^ 4 = 1 := by
  obtain ⟨e,he⟩ := ReeTwo.Core.exists_conjugator_c_of_orderOf_eq_five ρ hρ
  let c := MulAut.conj e
  have hβ : c σ * ReeTwo.Core.c * (c σ)⁻¹ = ReeTwo.Core.c ^ 2 := by
    have hh := congrArg c hsq
    simp only [map_mul,map_inv,map_pow] at hh
    change c ρ = ReeTwo.Core.c at he
    rwa [he] at hh
  have hh := ReeTwo.Core.squaring_action_four (c σ) hβ
  apply c.injective
  simpa only [map_pow,map_one] using hh

/-- Every actual five-squaring lift has fourth power in the original central
line and order four or eight. -/
theorem source_quintic_large_five_squaring_eighth
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5)
    (s : G) (hsH : s ∈ H) (hsA : s ∈ normalizer (A : Set G))
    (hs : ∀ a ∈ A, s * a * s⁻¹ = a ^ 2) :
    s ^ 4 ∈ centralInvolutions T ∧ s ^ 8 = 1 ∧
      (orderOf s = 4 ∨ orderOf s = 8) := by
  let Q := H.pCoreIn 2
  let R := ⁅Q,A⁆
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  obtain ⟨eQ,_,_⟩ := source_quintic_large_five_core_marking_of_original
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  let τ : normalizer (Q : Set G) →* MulAut ReeTwo.Core :=
    (MulAut.congr eQ.symm).toMonoidHom.comp Q.normalizerMonoidHom
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 5
    (hA ▸ (by decide : 5 ∣ 5))
  have ha5 : orderOf (a : G) = 5 := (orderOf_coe a).trans ha
  have hagen : zpowers (a : G) = A := eq_of_le_of_card_ge
    (zpowers_le.mpr a.property) (by rw [Nat.card_zpowers,ha5,hA])
  let aN : normalizer (Q : Set G) := ⟨a,hHQ (hAH a.property)⟩
  let sN : normalizer (Q : Set G) := ⟨s,hHQ hsH⟩
  have hρne : τ aN ≠ 1 := by
    intro hh
    have hact : Q.normalizerMonoidHom aN = 1 :=
      (MulAut.congr eQ.symm).injective (hh.trans (map_one _).symm)
    have haC : (a : G) ∈ centralizer (Q : Set G) := by
      intro q hq
      have he := congrArg (fun f : MulAut Q => (f ⟨q,hq⟩ : G)) hact
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hAC : A ≤ centralizer (Q : Set G) := by
      rw [←hagen]
      exact zpowers_le.mpr haC
    have hRb : R = ⊥ := by
      rw [show R = ⁅Q,A⁆ from rfl,commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hAC
    have hRcard : Nat.card R = 512 := (source_quintic_large_five_residual
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.2.2.1
    rw [hRb,card_bot] at hRcard
    contradiction
  have hρ : orderOf (τ aN) = 5 := orderOf_eq_prime
    (by rw [←map_pow,show aN ^ 5 = 1 from Subtype.ext
      (by change (a : G) ^ 5 = 1; simpa only [ha5] using pow_orderOf_eq_one (a : G)),map_one]) hρne
  have hsqN : sN * aN * sN⁻¹ = aN ^ 2 := Subtype.ext (hs a a.property)
  have hσsq : τ sN * τ aN * (τ sN)⁻¹ = (τ aN) ^ 2 := by
    simpa only [map_mul,map_inv,map_pow] using congrArg τ hsqN
  have hσfour : (τ sN) ^ 4 = 1 := squaring_order_four (τ aN) (τ sN) hρ hσsq
  have hact4 : Q.normalizerMonoidHom (sN ^ 4) = 1 := by
    apply (MulAut.congr eQ.symm).injective
    change τ (sN ^ 4) = _
    rw [map_pow,hσfour,map_one]
  obtain ⟨hs4,_,horders⟩ := source_quintic_large_five_squaring_power
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA s hsH hsA hs
  have hs4Z : s ^ 4 ∈ centralInvolutions T := by
    rw [←source_quintic_full_core_center hG T hempty hM hu hmany hcard e H hH hi]
    refine ⟨⟨s ^ 4,hs4.1⟩,mem_center_iff.mpr (fun q => ?_),rfl⟩
    have he := congrArg (fun f : MulAut Q => (f q : G)) hact4
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  have hs8 : s ^ 8 = 1 := by
    have hZcard : Nat.card (centralInvolutions T) = 2 :=
      plane_centralInvolutions_card T M hM.1.2 hcard e
    have hd : orderOf (⟨s ^ 4,hs4Z⟩ : centralInvolutions T) ∣ 2 :=
      hZcard ▸ orderOf_dvd_natCard (⟨s ^ 4,hs4Z⟩ : centralInvolutions T)
    have he : (⟨s ^ 4,hs4Z⟩ : centralInvolutions T) ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hd
    have hg : (s ^ 4) ^ 2 = 1 := congrArg Subtype.val he
    simpa only [←pow_mul] using hg
  refine ⟨hs4Z,hs8,?_⟩
  rcases horders with h4 | h8 | h16
  · exact Or.inl h4
  · exact Or.inr h8
  · have hd := orderOf_dvd_of_pow_eq_one hs8
    rw [h16] at hd
    norm_num at hd

end CFSG.Quasithin.Chapter14.Section06
