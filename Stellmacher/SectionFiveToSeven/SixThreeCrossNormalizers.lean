module

public import Stellmacher.SectionFiveToSeven.FiveFourSharedOmega
public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionThree.ThreeNineBaumannNormalizers
public import Stellmacher.BaumannIntermediate

/-!
# Cross-normalizers under the full (5.4) alternative

Under Hypothesis 2, let `E` and `F` be local-family members with shared
Sylow subgroup `B=B(S)`, and suppose their actual join has nontrivial
2-core. If either `S=S₀` or the join is not contained in the supplied
maximal 2-local subgroup `M`, then each full local group normalizes the
opposite commutator `[Ω₁(Z(B)), O²(E)]` or `[Ω₁(Z(B)), O²(F)]`.

The shared-omega theorem from (5.4) puts `Ω₁(Z(B))` in the join core.
Hypothesis 2 gives solvability of its core normalizer, hence of the join
and both local members. Maximum elementary-order comparison identifies
`J(B)=J(S)`, and Baumann heredity gives `B(B)=B`. The public join-Sylow
transport from (5.4) identifies this Thompson subgroup with that of a
chosen Sylow of the join containing B, under the same stated alternative.
Thus the (3.9) consequence gives opposite residual normalizations. The
shared subgroup B also normalizes both commutators, so residual-Sylow
generation extends these conclusions to the full local groups.

Source: Stellmacher (5.4) and (6.3), Journal of Algebra 190 (1997),
pp.30--31, their applications of (3.9), in
`refs/latex/stellmacher-n-group.tex`. The global-Sylow specialization
retains the existing (6.1) cross-normalizer interface as a wrapper.
All subgroup joins and Sylow images are the supplied actual ones.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem shared_normalizes_omega_residual
    {H : Type u} [Group H] (B P : Subgroup H) (hBP : B ≤ P) :
    B ≤ Subgroup.normalizer
      ((⁅omegaOneCenter B, twoResidualIn P⁆ : Subgroup H) : Set H) := by
  have hRn : (twoResidualSubgroup P).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun N =>
      Subgroup.normal_iInf_normal fun hN => hN.1
  have hPN : P ≤ Subgroup.normalizer (twoResidualIn P : Set H) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    exact hRn
  have hBZ : B ≤ Subgroup.normalizer (omegaOneCenter B : Set H) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff B z).mp hz).2.2 b hb |>.symm
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBZ hb),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPN (hBP hb))]

public theorem sixThree_cross_normalizers
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (E F M : Subgroup H)
    (hE : E ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hF : F ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (hcore : twoCoreIn (E ⊔ F) ≠ ⊥)
    (halt : S = (S0 : Subgroup H) ∨ ¬ (E ⊔ F) ≤ M) :
    F ≤ Subgroup.normalizer
      ((⁅omegaOneCenter (baumannIn S), twoResidualIn E⁆ : Subgroup H) : Set H) ∧
    E ≤ Subgroup.normalizer
      ((⁅omegaOneCenter (baumannIn S), twoResidualIn F⁆ : Subgroup H) : Set H) := by
  classical
  let B := baumannIn S
  let J := E ⊔ F
  have hBS : B ≤ S := inf_le_left
  have hBp : IsPGroup 2 B := S0.isPGroup'.to_le (hBS.trans h.fiveOne.S_le_S0)
  have hBE : B ≤ E := hE.1.2.1.1
  have hBF : B ≤ F := hF.1.2.1.1
  have hBJ : B ≤ J := hBE.trans le_sup_left
  have hBne : B ≠ ⊥ := by
    intro hbot
    apply hE.1.2.2.1
    have hCoreB : twoCoreIn E ≤ B := by
      obtain ⟨_, TE, hTE⟩ := hE.1.2.1
      change twoCoreIn E ≤ baumannIn S
      rw [← hTE]
      exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := E)).le_sylow_of_normal TE)
    exact le_bot_iff.mp (hCoreB.trans_eq hbot)
  have hOmega : omegaOneCenter B ≤ twoCoreIn J :=
    omegaOneCenter_shared_subgroup_le_join_core S0 S P1 P2 h B E F J M
      ⟨le_rfl, hBS⟩ hE hF rfl hM hcore halt
  let N := Subgroup.normalizer (twoCoreIn J : Set H)
  have hJN : J ≤ N := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hNlocal : IsTwoLocal N :=
    ⟨twoCoreIn J, hcore, (pCore_isPGroup (p := 2) (G := J)).map J.subtype, rfl⟩
  let _ : Group.IsSolvable N := (h.local_B N hNlocal (hBJ.trans hJN)).1
  have hJsolv : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJN)
  let _ : Group.IsSolvable J := hJsolv
  have hEsolv : Group.IsSolvable E :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (show E ≤ J from le_sup_left))
  have hFsolv : Group.IsSolvable F :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (show F ≤ J from le_sup_right))
  have hBJp : IsPGroup 2 (B.subgroupOf J) :=
    hBp.comap_of_injective J.subtype J.subtype_injective
  obtain ⟨T, hBTnative⟩ := hBJp.exists_le_sylow
  have hBT : B ≤ sylowAmbient T := by
    have hm := Subgroup.map_mono (f := J.subtype) hBTnative
    rwa [Subgroup.map_subgroupOf_eq_of_le hBJ] at hm
  have hJSB : elementaryAbelianMaxJ S ≤ B := by
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff (elementaryAbelianMaxJ S) z).mp hz).2.2 j hj |>.symm
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq B S hBS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S B hJSB
  have horder : elementaryAbelianMaxOrder B = elementaryAbelianMaxOrder S :=
    le_antisymm hsmall.1 hlarge.1
  have hJBS : elementaryAbelianMaxJ B = elementaryAbelianMaxJ S :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  have hJST : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (sylowAmbient T) :=
    elementaryAbelianMaxJ_eq_of_family_join_sylow S0 S P1 P2 B E F J M (sylowAmbient T)
      h hJSB (hBS.trans h.fiveOne.S_le_S0) hE hF rfl hM hcore halt hBT
      ⟨Subgroup.map_subtype_le _, T, rfl⟩
  have hJBT : elementaryAbelianMaxJ B = elementaryAbelianMaxJ (sylowAmbient T) :=
    hJBS.trans hJST
  have hBB : B ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ B) : Set H) = B :=
    baumann_eq_of_intermediate S B le_rfl hBS
  have hBsec : SectionThree.Hypotheses H B :=
    ⟨h.hyp1.even_order, hBne, hBp⟩
  have hEset := (pFamily_iff_pSet _ _ _).mp hE
  have hFset := (pFamily_iff_pSet _ _ _).mp hF
  have hOmegaInf : omegaOneCenterAmbient B ≤ B ⊓ twoCoreAmbient J :=
    le_inf (Subgroup.map_subtype_le _) hOmega
  obtain ⟨hRF, hRE⟩ := SectionThree.threeNine_residual_normalizes_omega_commutators
    B hBsec E F J hEset hFset rfl hEsolv hFsolv T hBT
      (B ⊓ twoCoreAmbient J) rfl hJsolv hOmegaInf hJBT hBB
  constructor
  · rw [← SectionThree.twoResidual_sup_sylowImage hFset.1.2.1]
    exact sup_le hRF (shared_normalizes_omega_residual B E hBE)
  · rw [← SectionThree.twoResidual_sup_sylowImage hEset.1.2.1]
    exact sup_le hRE (shared_normalizes_omega_residual B F hBF)

end Stellmacher.SectionsFiveToSeven
