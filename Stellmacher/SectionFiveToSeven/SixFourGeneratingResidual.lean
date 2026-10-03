module
public import Stellmacher.SectionFiveToSeven.Result6_1
public import Stellmacher.SectionFiveToSeven.Result5_3
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSectionThree
public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.SectionThree.LocalFamilyGeneratingExtraction
public import Stellmacher.SectionThree.LemmaThreeSeven
public import Stellmacher.BaumannTwoOvergroupTransport
public import Stellmacher.BaumannTwoOvergroupNormalizer
public import Stellmacher.BaumannNormalizer

/-!
# A generating residual selected from an arbitrary centralizer Sylow

Under Hypothesis Two with S the ambient Sylow, suppose B(S) ≤ T ≤ S,
T ≤ C ≤ P₂, C join S=P₂, and O₂(C) is nontrivial. There is K ≤ C with
K=[K,B(S)], K join S=P₂, and T normalizing K. The subgroup T need not
already be Sylow in C.

Extend T to an actual Sylow R of C. The Baumann two-overgroup theorem
identifies B(R)=B(S), so R and its normalizer normalize B(S). By (6.1),
this normalizer is proper in P₂. Local-family extraction selects a factor
F of C over R generating P₂ with S. The core alternative in (3.4) would
make F normalize B(S), again contradicting (6.1), so K=O²(F) has full
Baumann commutator. If K and S generated a proper subgroup, the unique
maximal subgroup over S would contain both K and R, hence F, a contradiction.
Finally T ≤ R ≤ F normalizes the characteristic residual K.

This supplies the group-selection step of Stellmacher (6.4), Journal of
Algebra 190 (1997), p.32, using the actually chosen centralizer Sylow.
Source: `refs/files/stellmacher-n-group.pdf`. The subsequent Sylow
supplement uses (5.2) to control the two-core and odd quotient of K.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_generating_residual
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) (hS : S = (S0 : Subgroup H))
    (C T : Subgroup H) (hTS : T ≤ S) (hBT : baumannIn S ≤ T)
    (hTC : T ≤ C) (hCP : C ≤ P2) (hgen : C ⊔ S = P2)
    (hcore : twoCoreIn C ≠ ⊥) :
    ∃ K : Subgroup H, K ≤ C ∧ K = ⁅K, baumannIn S⁆ ∧
      K ⊔ S = P2 ∧ T ≤ Subgroup.normalizer (K : Set H) := by
  classical
  let B := baumannIn S
  let N := P2 ⊓ Subgroup.normalizer (B : Set H)
  have hSp : IsPGroup 2 S := hS ▸ S0.isPGroup'
  have hBp : IsPGroup 2 B := hSp.to_le inf_le_left
  have hSP : S ≤ P2 := h.fiveOne.P2_mem.1.2.1.1
  have hBP : B ≤ P2 := (inf_le_left : B ≤ S).trans hSP
  have hBN : S ≤ Subgroup.normalizer (B : Set H) :=
    S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hBnot := lemma_six_one S0 S P1 P2 h
  have hPnot : ¬ P2 ≤ Subgroup.normalizer (B : Set H) := by
    intro hn
    have hnormal : (B.subgroupOf P2).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mpr hn
    have htwo : IsPGroup 2 (B.subgroupOf P2) :=
      hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBP).symm
    apply hBnot
    change B ≤ twoCoreIn P2
    rw [← Subgroup.map_subgroupOf_eq_of_le hBP]
    exact Subgroup.map_mono (show B.subgroupOf P2 ≤ pCore 2 P2 from le_sSup ⟨hnormal, htwo⟩)
  have hNne : N ≠ P2 := by
    intro he
    exact hPnot (he ▸ inf_le_right)
  have hTpC : IsPGroup 2 (T.subgroupOf C) :=
    (hSp.to_le hTS).of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  obtain ⟨R0, hTR0⟩ := hTpC.exists_le_sylow
  let R := (R0 : Subgroup C).map C.subtype
  have hRp : IsPGroup 2 R := R0.isPGroup'.map C.subtype
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  have hTR : T ≤ R := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTC]
    exact Subgroup.map_mono hTR0
  have hBR : B ≤ R := hBT.trans hTR
  have hB0 : B = (S0 : Subgroup H) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S0 : Subgroup H)) : Set H) := by
    change baumannIn S = baumannIn (S0 : Subgroup H)
    rw [hS]
  have hRbaumann : baumannIn R = B := by
    change R ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ R) : Set H) = B
    rw [hB0]
    exact (Stellmacher.twoSubgroup_thompson_baumann_eq S0 R hRp (hB0 ▸ hBR)).2
  have hRnB : R ≤ Subgroup.normalizer (B : Set H) := by
    rw [hB0]
    exact Stellmacher.twoSubgroup_le_normalizer_baumann S0 R hRp (hB0 ▸ hBR)
  have hRN : R ≤ N := le_inf (hRC.trans hCP) hRnB
  have hNRB : Subgroup.normalizer (R : Set H) ≤ Subgroup.normalizer (B : Set H) := by
    rw [← hRbaumann]
    exact normalizer_le_normalizer_baumann R
  have hRne : R ≠ ⊥ := by
    intro he
    exact hBnot ((hBR.trans_eq he).trans bot_le)
  have hthreeR : SectionThree.Hypotheses H R := ⟨h.hyp1.even_order,hRne,hRp⟩
  have hRcore : R ≠ twoCoreIn C := by
    intro he
    apply hPnot
    rw [← hgen]
    apply sup_le ?_ hBN
    apply le_trans ?_ hNRB
    rw [he]
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hL : C ∈ SectionThree.LSet ⊤ R := ⟨le_top, ⟨R0,rfl⟩,hcore,hRcore⟩
  have hnorm : (C ⊓ Subgroup.normalizer (R : Set H)) ⊔ S ≠ P2 := by
    intro he
    exact hPnot (he.ge.trans (sup_le (inf_le_right.trans hNRB) hBN))
  have hPset := (pFamily_iff_pSet ⊤ S P2).mp h.fiveOne.P2_mem
  obtain ⟨F,hF,hFS⟩ := SectionThree.exists_pSet_generating_of_normalizer_join_ne
    S R P2 C hthreeR hPset hL hCP hgen hnorm
  have hFC : F ≤ C := hF.1.1
  have hFP : F ≤ P2 := hFC.trans hCP
  have hRF : R ≤ F := by
    obtain ⟨U,hU⟩ := hF.1.2.1
    exact hU ▸ Subgroup.map_subtype_le _
  have hBnormalR : (B.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBR).mpr hRnB
  let _ : Group.IsSolvable P2 := (lemma_five_three S0 S P1 P2 h).2.2.1
  have hsolF : Group.IsSolvable F := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hFP)
  have hFtop : F ∈ SectionThree.PSet ⊤ R := ⟨⟨le_top,hF.1.2⟩,hF.2⟩
  have hKcomm : twoResidualAmbient F = ⁅twoResidualAmbient F,B⁆ := by
    rcases SectionThree.lemma_three_four R hthreeR F hFtop B ⟨hBR,hBnormalR⟩ hsolF with hb | hk
    · exfalso
      have hBcoreEq : baumannIn (twoCoreIn F) = B := by
        change twoCoreIn F ⊓ Subgroup.centralizer
          (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreIn F)) : Set H) = B
        rw [hB0]
        exact (Stellmacher.twoSubgroup_thompson_baumann_eq S0 (twoCoreIn F)
          ((pCore_isPGroup (p := 2) (G := F)).map F.subtype) (hB0 ▸ hb)).2
      have hFnB : F ≤ Subgroup.normalizer (B : Set H) := by
        rw [← hBcoreEq]
        apply le_trans ?_ (normalizer_le_normalizer_baumann (twoCoreIn F))
        apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        rw [subgroupOf_map_subtype_eq]
        infer_instance
      exact hPnot (hFS.ge.trans (sup_le hFnB hBN))
    · exact hk.symm
  let K := twoResidualAmbient F
  have hKF : K ≤ F := Subgroup.map_subtype_le _
  have hKgen : K ⊔ S = P2 := by
    apply le_antisymm (sup_le (hKF.trans hFP) hSP)
    by_contra hn
    have hne : K ⊔ S ≠ P2 := fun he => hn he.ge
    obtain ⟨M,hM,hSM,huniq⟩ := hPset.2
    have hKM : K ≤ M.map P2.subtype := le_sup_left.trans
      (SectionThree.le_unique_maximal_over huniq le_sup_right (sup_le (hKF.trans hFP) hSP) hne)
    have hNM : N ≤ M.map P2.subtype :=
      SectionThree.le_unique_maximal_over huniq (le_inf hSP hBN) inf_le_left hNne
    have hFM : F ≤ M.map P2.subtype := by
      rw [← SectionThree.twoResidual_sup_sylowImage hF.1.2.1]
      exact sup_le hKM (hRN.trans hNM)
    apply hM.1
    apply Subgroup.map_injective P2.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact le_antisymm (Subgroup.map_subtype_le _) (hFS.ge.trans (sup_le hFM hSM))
  have hFnK : F ≤ Subgroup.normalizer (K : Set H) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKF).mp
    dsimp only [K, twoResidualAmbient]
    rw [subgroupOf_map_subtype_eq]
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun N => Subgroup.normal_iInf_normal fun hN => hN.1
  exact ⟨K,hKF.trans hFC,hKcomm,hKgen,(hTR.trans hRF).trans hFnK⟩

end Stellmacher.SectionsFiveToSeven
