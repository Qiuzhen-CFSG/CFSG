module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveNormalizerEight

/-!
# Native coordinates aligned with the actual quintic actor

The marked core equivalence can be chosen so that the prescribed original
element of order five acts by the native automorphism `Core.c`, while the
two original root markings are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Align the native five-action with an actual source actor without changing
either the central-line mark or the cyclic-four fixed-root mark. -/
theorem source_quintic_large_marked_five_action
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
    (c : G) (hcH : c ∈ H) (hc5 : orderOf c = 5) :
    ∃ eQ : ReeTwo.Core ≃* H.pCoreIn 2,
      zpowers (eQ (ReeTwo.Core.root 9) : G) = centralInvolutions T ∧
      zpowers (eQ (ReeTwo.Core.root 2) : G) =
        H.pCoreIn 2 ⊓ centralizer (zpowers c : Set G) ∧
      ∀ q, (eQ (ReeTwo.Core.c q) : G) = c * (eQ q : G) * c⁻¹ := by
  let Q := H.pCoreIn 2
  let A := zpowers c
  have hAH : A ≤ H := zpowers_le.mpr hcH
  have hA : Nat.card A = 5 := (Nat.card_zpowers c).trans hc5
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  obtain ⟨eQ,hz,ht⟩ := source_quintic_large_five_core_marking_of_original
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  let τ : normalizer (Q : Set G) →* MulAut ReeTwo.Core :=
    (MulAut.congr eQ.symm).toMonoidHom.comp Q.normalizerMonoidHom
  let cN : normalizer (Q : Set G) := ⟨c,hHQ hcH⟩
  have hτ (q : ReeTwo.Core) :
      (eQ (τ cN q) : G) = c * (eQ q : G) * c⁻¹ := by
    simp only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.congr_apply,
      MulEquiv.symm_symm,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
    rfl
  have hρne : τ cN ≠ 1 := by
    intro hh
    have hact : Q.normalizerMonoidHom cN = 1 :=
      (MulAut.congr eQ.symm).injective (hh.trans (map_one _).symm)
    have hcC : c ∈ centralizer (Q : Set G) := by
      intro q hq
      have he := congrArg (fun f : MulAut Q => (f ⟨q,hq⟩ : G)) hact
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hAC : A ≤ centralizer (Q : Set G) := zpowers_le.mpr hcC
    have hRb : ⁅Q,A⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hAC
    have hRcard : Nat.card (⁅Q,A⁆ : Subgroup G) = 512 := (source_quintic_large_five_residual
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.2.2.1
    rw [hRb,card_bot] at hRcard
    contradiction
  have hρ : orderOf (τ cN) = 5 := orderOf_eq_prime
    (by rw [←map_pow,show cN ^ 5 = 1 from Subtype.ext
      (by change c ^ 5 = 1; simpa only [hc5] using pow_orderOf_eq_one c),map_one]) hρne
  have hroot : τ cN (ReeTwo.Core.root 2) = ReeTwo.Core.root 2 := by
    apply eQ.injective
    have hm : (eQ (ReeTwo.Core.root 2) : G) ∈ centralizer (A : Set G) := by
      exact (ht ▸ mem_zpowers (eQ (ReeTwo.Core.root 2) : G)).2
    apply Subtype.ext
    rw [hτ]
    exact mul_inv_eq_iff_eq_mul.mpr (hm c (mem_zpowers c))
  obtain ⟨d,hd2,hd9,hd⟩ :=
    ReeTwo.Core.exists_marked_conjugator_of_orderOf_eq_five (τ cN) hρ hroot
  let e' : ReeTwo.Core ≃* Q := d.symm.trans eQ
  have hd2' : d.symm (ReeTwo.Core.root 2) = ReeTwo.Core.root 2 :=
    d.symm_apply_eq.mpr hd2.symm
  have hd9' : d.symm (ReeTwo.Core.root 9) = ReeTwo.Core.root 9 :=
    d.symm_apply_eq.mpr hd9.symm
  refine ⟨e',?_,?_,?_⟩
  · simpa only [e',MulEquiv.trans_apply,hd9'] using hz
  · simpa only [e',MulEquiv.trans_apply,hd2'] using ht
  · intro q
    have he := congrArg (fun a : MulAut ReeTwo.Core => d.symm (a q)) hd
    have he' : τ cN (d.symm q) = d.symm (ReeTwo.Core.c q) := by
      simpa only [MulAut.mul_apply,MulAut.inv_apply,MulEquiv.symm_apply_apply] using he
    have hh := congrArg (fun q => (eQ q : G)) he'
    rw [hτ] at hh
    exact hh.symm

end CFSG.Quasithin.Chapter14.Section06
