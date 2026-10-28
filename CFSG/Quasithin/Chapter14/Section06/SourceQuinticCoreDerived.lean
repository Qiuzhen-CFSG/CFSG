module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanInterval
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanStrongFull

/-!
# The original quintic span lies in the derived full core

The genuine invariant interval leaves a central-line alternative for the
intersection of U with the derived full core. In that alternative the same
selected span W has central-line commutators with both conjugate cores.
The original middle-core product and rank-one generation then put [W,X]
in the original four-plane, hence in R. Thus X normalizes R and W=R≤U,
contrary to the retained nonzero reciprocal commutator.

The same critical conjugator and all full cores are retained throughout.
No positive Suzuki parameter or identification of the full centralizer
kernel with the root span is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

/-- The original quintic root span is contained in the derived subgroup
of its full two-core. -/
theorem source_quintic_core_derived_contains_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    conjugateSpanBy (localModule T M) H ≤ ⁅H.pCoreIn 2,H.pCoreIn 2⁆ := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let V := localModule T M
  let Z := centralInvolutions T
  let U := conjugateSpanBy V H
  let QH := H.pCoreIn 2
  let Q := X.pCoreIn 2
  rcases (source_quintic_span_interval_and_derived
    hG T hempty hM hu hmany hcard e H hH hi).2 with hcentral | hderived
  · exfalso
    change U ⊓ ⁅QH,QH⁆ = Z at hcentral
    obtain ⟨g,hg,hDQ,hDne,hVI,_,hprod,_,_,hWel,hWQ,hXW,hWU,hWUstar,
      hRstarW,hmove,_,_,_,_,_,_,_,_,hWQcomm⟩ :=
      source_quintic_second_kernel_span_strong_full hG T hempty hM hu hmany hcard e H hH hi
    let c := (MulAut.conj g).toMonoidHom
    let D := U.map c
    let Y := QH.map c
    let R := U ⊓ Y
    let Rstar := D ⊓ QH
    let W := conjugateSpanBy R X
    change (QH ⊓ Q) ⊔ (Y ⊓ Q) = Q at hprod
    have hTX : (T : Subgroup G) ≤ X := le_sup_right
    have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
    have hQT : Q ≤ (T : Subgroup G) :=
      (pCoreIn_le_sylow X (T.subtype hTX)).trans_eq (map_subgroupOf_eq_of_le hTX)
    have hQHT : QH ≤ (T : Subgroup G) :=
      (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq (map_subgroupOf_eq_of_le hTH)
    have hQX : Q ≤ X := hQT.trans hTX
    have hQHX : QH ≤ X := hQHT.trans hTX
    have hQN : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    have hmapQ : Q.map c = Q := mem_normalizer_iff_map_conj_eq.mp (hQN hg)
    have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
    have hUQH : U ≤ QH := by
      obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
        hG T hempty hM hu hmany hcard e
      let := he
      obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
      have hh := hl.U_le_core
      change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
      simpa only [Section02.rankTwoSeed_eq_localModule] using hh
    have hYX : Y ≤ X := by
      have hh := map_mono (f := c) hQHX
      have he : X.map c = X := mem_normalizer_iff_map_conj_eq.mp (X.le_normalizer hg)
      exact hh.trans he.le
    have hXV : X ≤ normalizer (V : Set G) := by
      rw [←InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
      exact sup_le (sourceResidual_le M Mc) hM.1.2
    have hZV : Z ≤ V := le_conjugateSpanBy _ _
    have hmapV : V.map c = V := mem_normalizer_iff_map_conj_eq.mp (hXV hg)
    have hZgV : Z.map c ≤ V := (map_mono hZV).trans hmapV.le
    have hWg : W.map c = W := mem_normalizer_iff_map_conj_eq.mp (hXW hg)
    have hWQH : ⁅W,QH⁆ ≤ Z :=
      (le_inf hWQcomm (commutator_mono (hWQ.trans inf_le_left) le_rfl)).trans hcentral.le
    have hWY : ⁅W,Y⁆ ≤ Z.map c := by
      have hh := map_mono (f := c) hWQH
      rw [map_commutator,hWg] at hh
      exact hh
    have hWQV : ⁅W,Q⁆ ≤ V := by
      rw [←hprod,commutator_comm]
      apply commutator_sup_le_of_relative_normal X (QH ⊓ Q) (Y ⊓ Q) W V
        hXV (inf_le_right.trans hQX) (inf_le_right.trans hQX)
      · rw [commutator_comm]
        exact (commutator_mono le_rfl inf_le_left).trans (hWQH.trans hZV)
      · rw [commutator_comm]
        exact (commutator_mono le_rfl inf_le_left).trans (hWY.trans hZgV)
    have hgen : X = (QH ⊔ Y) ⊔ Q := by
      have hT : QH ⊔ Q = (T : Subgroup G) :=
        (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).1
      have hgT : g ∉ (T : Subgroup G) := by
        intro ht
        have hm : U.map c = U := mem_normalizer_iff_map_conj_eq.mp (hHU (hTH ht))
        exact hDne (hm.le.trans hUQH)
      obtain ⟨hF,_,_,hNX,_⟩ := Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
        hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)
      let S := T.subtype hTX
      let gx : X := ⟨g,hg⟩
      have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hTX
      have hR : ((gx • S : Sylow 2 X) : Subgroup X).map X.subtype =
          (T : Subgroup G).map c := by
        change ((S : Subgroup X).map (MulAut.conj gx).toMonoidHom).map X.subtype = _
        rw [←hS,Subgroup.map_map,Subgroup.map_map]
        rfl
      have hne : S ≠ gx • S := by
        intro he
        have hm := congrArg (fun R : Sylow 2 X => (R : Subgroup X).map X.subtype) he
        rw [hS,hR] at hm
        have hn : g ∈ normalizer (T : Set G) := mem_normalizer_iff_map_conj_eq.mpr hm.symm
        exact hgT (hNX ▸ (show g ∈ X ⊓ normalizer (T : Set G) from ⟨hg,hn⟩))
      have hh := CommutingThreeProfile.rankOne_sylow_pair_generates X (hF.quotient 1) S (gx • S) hne
      rw [hS,hR,←hT,Subgroup.map_sup,hmapQ] at hh
      rw [sup_sup_sup_comm,sup_idem] at hh
      exact hh.symm
    have hWX : ⁅W,X⁆ ≤ V := by
      rw [hgen,commutator_comm]
      apply commutator_sup_le_of_relative_normal X (QH ⊔ Y) Q W V hXV
        (sup_le hQHX hYX) hQX
      · apply commutator_sup_le_of_relative_normal X QH Y W V hXV hQHX hYX
        · rw [commutator_comm]; exact hWQH.trans hZV
        · rw [commutator_comm]; exact hWY.trans hZgV
      · rw [commutator_comm]; exact hWQV
    have hVR : V ≤ R := le_inf (hVI.trans inf_le_left)
      ((hVI.trans inf_le_right).trans (map_mono hUQH))
    have hXR : X ≤ normalizer (R : Set G) :=
      le_normalizer_iff_commutator_le_left.mpr
        ((commutator_mono (le_conjugateSpanBy R X) le_rfl).trans (hWX.trans hVR))
    have hWR : W = R := le_antisymm (conjugateSpanBy_le le_rfl hXR) (le_conjugateSpanBy R X)
    let : IsElementaryAbelian 2 U :=
      (Section02.SolvableAmalgam.source_index_five_closure_structure
        hG T hempty hM hu hmany hcard e H hH.1 hi).1
    have hRU : Rstar ≤ U := hRstarW.trans (hWR.le.trans inf_le_left)
    exact hmove (commutator_eq_bot_iff_le_centralizer.mpr (hRU.trans (le_centralizer U)))
  · exact hderived

end CFSG.Quasithin.Chapter14.Section06
