module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanStrongFull
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelFrattiniCentralizer
public import Theory.Frattini.QuadraticCentralizer
public import Theory.GroupTheory.AlmostSpecialIntersection

/-!
# Same-conjugator reciprocal Frattini control

The full quintic span source supplies one actual escaping conjugator.  We
rebuild the original H-orbit supplement for that witness, rather than taking
the independent existential witness from the earlier Frattini theorem.  The
embedded Frattini subgroup of the literal centralizer therefore centralizes
the reciprocal hyperplane `Rstar = Ustar ∩ Q` in the same original
configuration.  No quotient model is strengthened, so the FullRee branch is
retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original StrongFull witness gives a reciprocal hyperplane centralized
by the Frattini subgroup of the literal full kernel. -/
theorem source_quintic_same_conjugator_frattini_reciprocal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := Q.map (MulAut.conj g).toMonoidHom
      let Rstar := Ustar ⊓ Q
      let W := conjugateSpanBy (U ⊓ Qstar) X
      let J := conjugateSpanBy W H
      J ≤ Q ∧ H ≤ normalizer (J : Set G) ∧ J ⊔ C = Q ∧
        (frattini C).map C.subtype ≤ centralizer (Rstar : Set G) ∧
        (frattini C).map C.subtype ⊓ U ≤ centralInvolutions T := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH,hWel,hWQ,hXW,
      hWU,hWUstar,hRW,hmove,hRcard,hRstarcard,hWcard,hWcomm,hUC,
      hindex,hkernelcard,hWCeq,hWQcomm⟩ :=
    source_quintic_second_kernel_span_strong_full
      hG T hempty hM hu hmany hcard e H hH hi
  let Ustar := U.map (MulAut.conj g).toMonoidHom
  let Qstar := Q.map (MulAut.conj g).toMonoidHom
  let Rstar := Ustar ⊓ Q
  let W := conjugateSpanBy (U ⊓ Qstar) X
  let J := conjugateSpanBy W H
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hJQ : J ≤ Q := conjugateSpanBy_le (hWQ.trans inf_le_left) hHQ
  have hHJ : H ≤ normalizer (J : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy
      (localModule T M) H).trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hWnotC : ¬ W ≤ C := by
    intro hWC
    have hbot : ⁅W,U⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hWC.trans inf_le_right)
    exact (by
      have hZne : (centralInvolutions T : Subgroup G) ≠ ⊥ := by
        intro hz
        have hzcard : Nat.card (centralInvolutions T) = 2 :=
          plane_centralInvolutions_card T M hM.1.2 hcard e
        rw [hz,card_bot] at hzcard
        omega
      apply hZne
      exact hWcomm.symm.trans hbot)
  have hHD : H ≤ normalizer ((J ⊔ C : Subgroup G) : Set G) := by
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hHJ hh),
      mem_normalizer_iff_map_conj_eq.mp (hHC hh)]
  have hJC : J ⊔ C = Q := by
    rcases (source_quintic_full_kernel_interval hG T hempty hM hu hmany hcard e H hH hi).2
      (J ⊔ C) le_sup_right (sup_le hJQ hCQ) hHD with he | he
    · exact (hWnotC ((le_conjugateSpanBy W H).trans (le_sup_left.trans he.le))).elim
    · exact he
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hJcomm : ⁅J,Q⁆ ≤ U := by
    change ⁅conjugateSpanBy W H,Q⁆ ≤ U
    rw [commutator_conjugateSpanBy_of_normalized_right W H Q
      ((hWQ.trans inf_le_left).trans (pCoreIn_le 2 H)) hHQ]
    exact conjugateSpanBy_le hWQcomm (le_normalizer_conjugateSpanBy _ _)
  have hCJ : ⁅C,J⁆ ≤ U := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hCQ).trans hJcomm
  have hpC : IsPGroup 2 C :=
    (isPGroup_pCoreIn 2 H).to_le hCQ
  have hphi : (frattini C).map C.subtype ≤ centralizer (J : Set G) :=
    frattini_image_le_centralizer_of_elementary_commutator C J U hpC hCJ inf_le_right
  have hphiR : (frattini C).map C.subtype ≤ centralizer (Rstar : Set G) :=
    hphi.trans (centralizer_le (hRW.trans (le_conjugateSpanBy W H)))
  have hfixed : (frattini C).map C.subtype ⊓ U ≤ centralizer (Q : Set G) := by
    apply le_centralizer_iff.mpr
    rw [←hJC]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans hphi))
      (le_centralizer_iff.mp (inf_le_right.trans
        (le_centralizer_iff.mp (show C ≤ centralizer (U : Set G) from inf_le_right))))
  exact ⟨g,hg,hJQ,hHJ,hJC,hphiR,
    (le_inf inf_le_right hfixed).trans
      (source_quintic_span_card_and_core_radical
        hG T hempty hM hu hmany hcard e H hH hi).2.le⟩

end CFSG.Quasithin.Chapter14.Section06
