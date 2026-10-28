module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The central line in a moved support

The proof of 14.6.2 applies to any nonzero commutator [B,X] inside U, provided
B and X are normalized by Q_H. If [B,X] centralized Q_H, it would lie in
Omega_1(Z(Q_H)); generalized-Fitting centrality and coprime commutator
idempotence would then force it to vanish. Its nonzero commutator with Q_H
therefore contains the original central line Z.

The source application keeps H=Mc and X=O^2(C_H(u mod Z)). This is the lift
needed for the moving dual plane on printed p.1042, not a claim that the
whole dual support is an eight-group.

Source: Aschbacher--Smith, 14.6.1(5), 14.6.2 and printed p.1042.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
variable {G : Type*} [Group G] [Finite G]

theorem point_le_support_commutator
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (B X : Subgroup G)
    (hBU : B ≤ D.UH) (hp : IsPPerfect 2 X)
    (hXB : X ≤ normalizer (B : Set G))
    (hQB : D.QH ≤ normalizer (B : Set G))
    (hQX : D.QH ≤ normalizer (X : Set G))
    (hne : ⁅B,X⁆ ≠ ⊥)
    (hcent : X ≤ centralizer (omegaOneCenterAmbient D.QH : Set G)) :
    D.V₁ ≤ ⁅B,X⁆ := by
  let W := ⁅B,X⁆
  have hWB : W ≤ B := le_normalizer_iff_commutator_le_left.mp hXB
  have hWU : W ≤ D.UH := hWB.trans hBU
  have hWQ : W ≤ D.QH := hWU.trans h.UH_le_QH
  have hQW : D.QH ≤ normalizer (W : Set G) := by
    intro q hq
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅B,X⁆).map (MulAut.conj q).toMonoidHom = _
    have hb : B.map (MulAut.conj q).toMonoidHom = B :=
      mem_normalizer_iff_map_conj_eq.mp (hQB hq)
    have hx : X.map (MulAut.conj q).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp (hQX hq)
    rw [map_commutator, hb, hx]
  have hcommne : ⁅W,D.QH⁆ ≠ ⊥ := by
    intro hz
    have hWomega : W ≤ omegaOneCenterAmbient D.QH := by
      intro w hw
      exact (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hWQ hw,elemPow_eq_one_of_isElementaryAbelian w (hWU hw),
          (commutator_eq_bot_iff_le_centralizer.mp hz) hw⟩
    have hbot : ⁅W,X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hcent.trans (centralizer_le hWomega)))
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBU
    exact hne ((commutator_isPPerfect_idempotent X B hp
      (IsElementaryAbelian.isPGroup 2 _) hXB).symm.trans hbot)
  have hAZ : ⁅W,D.QH⁆ ≤ D.V₁ :=
    (commutator_mono hWU le_rfl).trans h.commutator_UH_QH_le_point
  have hAW : ⁅W,D.QH⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hQW
  have hc : Nat.card (⁅W,D.QH⁆ : Subgroup G) = 2 := by
    have hd : Nat.card (⁅W,D.QH⁆ : Subgroup G) ∣ 2 := by
      simpa only [h.point_card] using card_dvd_of_le hAZ
    exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
      (fun he => hcommne (card_eq_one.mp he))
  have he : ⁅W,D.QH⁆ = D.V₁ := eq_of_le_of_card_ge hAZ (by rw [hc,h.point_card])
  exact he ▸ hAW

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The 14.6.2 argument on the particular dual support in the final paragraph.
The residual and the original point centralizer are not replaced by abstract copies. -/
theorem source_point_le_dual_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (B : Subgroup G) (hBU : B ≤ conjugateSpanBy (localModule T M) Mc) (u : G)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u)
    (hn : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).kernel
      (zpowers u) ≤ normalizer (B : Set G))
    (hRF : ((pResidual 2 ((ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany
      hcard e hab).kernel (zpowers u))).map ((ComponentSupports.terminal_hypothesis hG T hempty
      hM hunique hmany hcard e hab).kernel (zpowers u)).subtype) ≤
      ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hne : ⁅B,((pResidual 2 ((ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany
      hcard e hab).kernel (zpowers u))).map ((ComponentSupports.terminal_hypothesis hG T hempty
      hM hunique hmany hcard e hab).kernel (zpowers u)).subtype)⁆ ≠ ⊥) :
    centralInvolutions T ≤ ⁅B,((pResidual 2 ((ComponentSupports.terminal_hypothesis hG T hempty hM
      hunique hmany hcard e hab).kernel (zpowers u))).map ((ComponentSupports.terminal_hypothesis
      hG T hempty hM hunique hmany hcard e hab).kernel (zpowers u)).subtype)⁆ := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let P := h.kernel (zpowers u)
  let R := (pResidual 2 P).map P.subtype
  let := h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hQP : Mc.pCoreIn 2 ≤ P := by
    intro x hx
    exact (h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu.1))).mpr
      ⟨pCoreIn_le 2 Mc hx, fun v hv => h.commutator_UH_QH_le_point
        (commutator_mem_commutator ((zpowers_le.mpr hu.1) hv) hx)⟩
  have hout := ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e
  have hHZ := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
    Mc hout.1 hout.2).2
  exact point_le_support_commutator h B R hBU (isPPerfect_embedded_pResidual 2 P)
    ((map_subtype_le _).trans hn) (hQP.trans hn)
    (hQP.trans (le_normalizer_embedded_pResidual 2 P)) hne
    (hRF.trans (source_generalizedFittingPreimage_centralizes_omegaCore hG T hempty hout hHZ))

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
