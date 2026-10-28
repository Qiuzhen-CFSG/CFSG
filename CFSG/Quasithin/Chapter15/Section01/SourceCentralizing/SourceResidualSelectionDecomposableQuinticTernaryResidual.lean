module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticNormalClosure
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaOvergroupComparison.Proper

/-!
# The actual partner residual from a three-group action residual

For an original maximal two-local N distinct from the central partner,
the literal partner residual Y has its ordered placement in M ∩ N and
is normalized by C_M(V). If the two-residual of N's actual action on
its own local module is a three-group, then Y/O₂(Y) is a three-group.

The intersection two-core centralizes the action kernel modulo O₂(N).
The central-kernel normal-closure theorem therefore applies in N/O₂(N).
Residual functoriality and the normal-subgroup core quotient identify its
conclusion with Y/O₂(Y). The original noncentrality of Y on the local
module makes O₂(Y) nontrivial, giving the full ambient normalizer N.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section02 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition Chapter14.SourcePreliminaries

private theorem residual_normalClosure_threeGroup_mod_core
    {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
    (f : H →* D) (R Q : Subgroup H) [Q.Normal]
    (hR : IsPGroup 2 R) (hQ : Q ≤ f.ker)
    (hc : ⁅f.ker,R⁆ ≤ Q) (hpD : IsPGroup 3 (pResidual 2 D)) :
    IsPGroup 3 (((pResidual 2 (normalClosure (R : Set H))).map
      (normalClosure (R : Set H)).subtype).map (QuotientGroup.mk' Q)) := by
  let q := QuotientGroup.mk' Q
  let g := QuotientGroup.lift Q f hQ
  have hRc : R.map q ≤ centralizer (g.ker : Set (H ⧸ Q)) := by
    rw [show g.ker = f.ker.map q from QuotientGroup.ker_lift Q f hQ]
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using hc
  have hh := DecomposableQuinticControl.three_twoResidual_normalClosure_of_central_kernel
    g (R.map q) (hR.map q) hRc hpD
  have hm : (normalClosure (R : Set H)).map q =
      normalClosure (R.map q : Set (H ⧸ Q)) :=
    map_normalClosure _ q (QuotientGroup.mk'_surjective Q)
  rw [map_embedded_pResidual,hm]
  exact hh

variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation (H : Subgroup G) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hp⟩
    exact ⟨hN,IsPGroup.iff_card.mp hp⟩

/-- A three-group two-residual in the literal local action supplies the
original partner residual, its intrinsic three-group core quotient, and
its full ambient normalizer. -/
theorem PreparedChosenModule.ordered_local_residual_of_three_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNMc : N ≠ Mc)
    (hpD : IsPGroup 3 (pResidual 2 (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N)))) :
    let Y := sourceResidual N Mc
    Y ≤ M ⊓ N ∧ (Y.subgroupOf N).Normal ∧ IsPPerfect 2 Y ∧
      M ⊓ centralizer (V : Set G) ≤ normalizer (Y : Set G) ∧
      IsPGroup 3 (Y ⧸ pCore 2 Y) ∧ normalizer (Y : Set G) = N := by
  let W := localModule T N
  let C := (centralizer (W : Set G)).subgroupOf N
  let R := ((N ⊓ Mc).pCoreIn 2).subgroupOf N
  let J := normalClosure (R : Set N)
  let Y := sourceResidual N Mc
  let A := Y.subgroupOf N
  let a := (actionHom N W (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  have hker : a.ker = C := by
    rw [MonoidHom.ker_rangeRestrict]
    exact actionHom_ker N W (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨hmeet,_,hcomm⟩ := local_partner_core_inputs hG T hempty hN hu hmany hNMc
  have hRN : (N ⊓ Mc).pCoreIn 2 ≤ N := (pCoreIn_le 2 _).trans inf_le_left
  have hCm : C.map N.subtype = N ⊓ centralizer (W : Set G) := by
    rw [subgroupOf_map_subtype,inf_comm]
  have hRm : R.map N.subtype = (N ⊓ Mc).pCoreIn 2 := map_subgroupOf_eq_of_le hRN
  have hmeetN : R ⊓ a.ker = pCore 2 N := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_inf _ _ _ N.subtype_injective,hker,hRm,hCm,
      ←inf_assoc,inf_eq_left.mpr hRN]
    exact hmeet
  have hQ : pCore 2 N ≤ a.ker := by rw [←hmeetN]; exact inf_le_right
  have hc : ⁅a.ker,R⁆ ≤ pCore 2 N := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,hker,hCm,hRm]
    exact hcomm
  have hAid : A = (pResidual 2 J).map J.subtype := by
    change ((twoResidualAmbient J).map N.subtype).comap N.subtype = _
    rw [comap_map_eq,N.ker_subtype,sup_bot_eq,residual_notation]
  have hstar : IsPGroup 3 (A.map (QuotientGroup.mk' (pCore 2 N))) := by
    rw [hAid]
    exact residual_normalClosure_threeGroup_mod_core a R (pCore 2 N)
      ((isPGroup_pCoreIn 2 (N ⊓ Mc)).comap_subtype) hQ hc hpD
  have hn : A.Normal := residualY_normal N Mc
  let : A.Normal := hn
  have hYN : Y ≤ N := sourceResidual_le N Mc
  have hNY : N ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYN).mp hn
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hle : Y ≤ M ⊓ N := ordered_partner_residual_le T hM.1.2 hN.2 hu hord
  refine ⟨hle,hn,residualY_isPPerfect N Mc,?_,?_,?_⟩
  · apply le_trans ?_ hNY
    rw [hfull]
    exact ((lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source hG T hN)).trans inf_le_left
  · let j : A ≃* Y := subgroupOfEquivOfLe hYN
    let k := QuotientGroup.congr (pCore 2 A) (pCore 2 Y) j (pCore_map_iso 2 j)
    exact (hstar.of_equiv (coreQuotientEquivImage 2 A).symm).of_equiv k
  · have hcore : Y.pCoreIn 2 ≠ ⊥ := by
      intro he
      have hWn : N ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
      let : IsElementaryAbelian 2 W := localModule_elementary_from_source hG T
        ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
      have hcY : ⁅W,Y⁆ ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
        ((IsElementaryAbelian.isPGroup 2 W).to_le
          (le_normalizer_iff_commutator_le_left.mp (hYN.trans hWn)))
        (le_normalizer_iff_commutator_le_right.mp ((localModule_le T hN.2).trans hNY))
        (normalizer_commutator_ge_right W Y)
      have hz : ⁅W,Y⁆ = ⊥ := bot_unique (he ▸ hcY)
      exact local_partner_residual_noncentral hG T hempty hN hu hmany hNMc
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
    exact normalizer_eq_of_nontrivial_core N Y (Y.pCoreIn 2) hYN hN.1 hn hcore le_rfl

end CFSG.Quasithin.Chapter15.Section01
