module

public import Stellmacher.SectionEight.GeneratedEightSixSylowIntersection
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCountsTools
public import Theory.GroupTheory.NormalCenterQuotient
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexFixedCore
public import Stellmacher.SectionThree.SylowQuotientCyclicCenter

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

set_option maxHeartbeats 800000

public theorem eight_six_three_subgroup_le_residual
    {G : Type u} [Group G] [Finite G] (T P : Subgroup G)
    (hTP : T ≤ P) (hthree : IsPGroup 3 T) : T ≤ twoResidualIn P := by
  have hlocal : T.subgroupOf P ≤ twoResidualSubgroup P := by
    rw [twoResidualSubgroup]
    apply le_sInf
    intro normal hnormal
    let _ := hnormal.1
    have hquotient : IsPGroup 2 (P ⧸ normal) := by
      rw [IsPGroup.iff_card]
      obtain ⟨exponent, hexponent⟩ := hnormal.2
      exact ⟨exponent, by simpa only [Subgroup.index_eq_card] using hexponent⟩
    have himage : IsPGroup 3 ((T.subgroupOf P).map (QuotientGroup.mk' normal)) :=
      (hthree.comap_of_injective P.subtype P.subtype_injective).map _
    have hdisjoint := himage.disjoint_of_coprime
      (hquotient.to_subgroup ⊤) (by norm_num : Nat.Coprime 3 2)
    have hbot : (T.subgroupOf P).map (QuotientGroup.mk' normal) = ⊥ := by
      simpa using hdisjoint.eq_bot
    simpa only [QuotientGroup.ker_mk'] using
      ((T.subgroupOf P).map_eq_bot_iff.mp hbot)
  calc
    T = (T.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hTP).symm
    _ ≤ _ := Subgroup.map_mono hlocal

public theorem eight_six_initial_core_coprime_decomposition
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q T : Subgroup G)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L) (hT : IsSylowIn 3 T (GAt graph path.a))
    (data : EightSixEquationOneData graph path previous D L Q) :
    QAt graph path.a = (QAt graph path.a ⊓ Subgroup.centralizer (T : Set G)) ⊔ Q := by
  obtain ⟨sylow, hsylow⟩ := hT
  have hTinitial : T ≤ GAt graph path.a := hsylow ▸ Subgroup.map_subtype_le _
  have hTthree : IsPGroup 3 T := hsylow ▸ sylow.isPGroup'.map _
  have hTclosure : T ≤ L := (eight_six_three_subgroup_le_residual T _ hTinitial
    hTthree).trans ((graph.twoResidualAt_def path.a).symm.le.trans data.residual_le)
  have hLnormal : NormalIn L (GAt graph path.a) := by
    refine ⟨data.closure_le, Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hQa : QAt graph path.a = twoCoreIn (GAt graph path.a) :=
    graph.twoCoreAt_def path.a
  have hcore : Q = L ⊓ QAt graph path.a := by
    rw [hQ, eight_six_core_of_normal_eq_inter _ _ hLnormal, hQa]
  have hcomm : ⁅QAt graph path.a, T⁆ ≤ Q := by
    rw [hcore]
    apply le_inf
    · exact (Subgroup.commutator_mono le_rfl hTclosure).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          ((hQa.le.trans (SevenSix.twoCoreIn_le _)).trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer data.closure_le).mp
              hLnormal.2)))
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hTinitial.trans (SevenSix.stabilizer_le_normalizer_q graph path.a))
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : IsPGroup 2 (QAt graph path.a) := by
    rw [QAt, q, graph.twoCoreAt_def]
    exact eight_six_two_core_is_two_group _
  let _ := (SevenSix.edge_local_data hyp graph path).1.2
  have hsolv : Group.IsSolvable (QAt graph path.a) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (show QAt graph path.a ≤ GAt graph path.a from
        (graph.twoCoreAt_def path.a).le.trans (SevenSix.twoCoreIn_le _)))
  have hdecomposition := Subgroup.eq_commutator_sup_centralizer_of_solvable_coprime
    (QAt graph path.a) T
    (hTinitial.trans (SevenSix.stabilizer_le_normalizer_q graph path.a)) hsolv
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) T _ hTthree htwo)
  apply le_antisymm
  · exact hdecomposition.le.trans (sup_le (hcomm.trans le_sup_right) le_sup_left)
  · exact sup_le inf_le_left (hcore.le.trans inf_le_right)

public theorem eight_six_initial_core_three_factor_decomposition
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 2)
    (previous : graph.Vertex) (D L Q T : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L) (hT : IsSylowIn 3 T (GAt graph path.a))
    (data : EightSixEquationOneData graph path previous D L Q) :
    QAt graph path.a = (QAt graph path.a ⊓ Subgroup.centralizer (T : Set G)) ⊔
      (VAt graph previous ⊓ QAt graph path.a) ⊔
      (QAt graph path.a ⊓ QAt graph path.firstStep) := by
  have hV : VAt graph path.firstStep ≤ QAt graph path.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) _
  have hDcore : D ≤ QAt graph path.a := by
    have hDQ : D ≤ Q := data.core_generation ▸ le_sup_right
    have hdecomp := eight_six_initial_core_coprime_decomposition hyp graph path
      previous D L Q T hL hQ hT data
    exact hDQ.trans (le_sup_right.trans hdecomp.ge)
  apply le_antisymm
  · apply (eight_six_initial_core_coprime_decomposition hyp graph path previous
      D L Q T hL hQ hT data).le.trans
    apply sup_le (le_sup_left.trans le_sup_left)
    rw [data.core_generation]
    exact sup_le (sup_le (le_sup_right.trans le_sup_left)
      ((le_inf inf_le_right (inf_le_left.trans hV)).trans le_sup_right))
      ((le_inf hDcore (hD.le.trans inf_le_right)).trans le_sup_right)
  · exact sup_le (sup_le inf_le_left inf_le_right) inf_le_left

public theorem eight_six_first_core_intersection_le_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hprevious : previous ∈ neighborhood graph path.a)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData graph path previous D L Q) :
    QAt graph path.a ⊓ QAt graph path.firstStep ≤ Q := by
  have hnormal : NormalIn L (GAt graph path.a) := by
    refine ⟨data.closure_le, Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hfirst : QAt graph path.firstStep ≤ L := by
    rw [hL]
    exact eight_six_first_core_le_previous_closure hyp graph path previous hprevious
  rw [hQ, eight_six_core_of_normal_eq_inter _ _ hnormal,
    ← show QAt graph path.a = twoCoreIn (GAt graph path.a) from graph.twoCoreAt_def _]
  exact le_inf (inf_le_right.trans hfirst) inf_le_left

public theorem eight_six_core_barred_image_eq
    {G X : Type u} [Group G] [Finite G] [Group X] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 2)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (data : EightSixEquationOneData graph path previous D L Q)
    (projection : S →* X) (hkernel : projection.ker = (QAt graph path.firstStep).subgroupOf S) :
    (Q.subgroupOf S).map projection =
      ((VAt graph previous ⊓ QAt graph path.a).subgroupOf S).map projection := by
  have hQS : Q ≤ S :=
    (le_sup_right.trans data.sylow_intersection.ge).trans inf_le_right
  have hAS : VAt graph previous ⊓ QAt graph path.a ≤ S :=
    inf_le_right.trans (SevenSix.local_cores_le_edge_sylow hyp graph path).1
  have hBS : VAt graph path.firstStep ⊓ QAt graph path.a ≤ S :=
    inf_le_right.trans (SevenSix.local_cores_le_edge_sylow hyp graph path).1
  have hDS : D ≤ S := (data.core_generation ▸ le_sup_right : D ≤ Q).trans hQS
  have hV : VAt graph path.firstStep ≤ QAt graph path.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) _
  have hBzero : ((VAt graph path.firstStep ⊓ QAt graph path.a).subgroupOf S).map
      projection = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hkernel]
    exact Subgroup.comap_mono (inf_le_left.trans hV)
  have hDzero : (D.subgroupOf S).map projection = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hkernel]
    exact Subgroup.comap_mono (hD.le.trans inf_le_right)
  conv_lhs => rw [data.core_generation]
  rw [Subgroup.subgroupOf_sup (sup_le hAS hBS) hDS,
    Subgroup.subgroupOf_sup hAS hBS, Subgroup.map_sup, Subgroup.map_sup,
    hBzero, hDzero, sup_bot_eq, sup_bot_eq]

public theorem eight_six_initial_core_barred_decomposition
    {G X : Type u} [Group G] [Finite G] [Group X] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 2)
    (previous : graph.Vertex) (D L Q T : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L) (hT : IsSylowIn 3 T (GAt graph path.a))
    (data : EightSixEquationOneData graph path previous D L Q)
    (projection : S →* X) (hkernel : projection.ker = (QAt graph path.firstStep).subgroupOf S) :
    ((QAt graph path.a).subgroupOf S).map projection =
      ((QAt graph path.a ⊓ Subgroup.centralizer (T : Set G)).subgroupOf S).map projection ⊔
      ((VAt graph previous ⊓ QAt graph path.a).subgroupOf S).map projection := by
  have hcores := SevenSix.local_cores_le_edge_sylow hyp graph path
  have hdecomp := eight_six_initial_core_coprime_decomposition hyp graph path previous
    D L Q T hL hQ hT data
  have hCS : QAt graph path.a ⊓ Subgroup.centralizer (T : Set G) ≤ S :=
    inf_le_left.trans hcores.1
  have hQS : Q ≤ S := (le_sup_right.trans hdecomp.ge).trans hcores.1
  conv_lhs => rw [hdecomp]
  rw [Subgroup.subgroupOf_sup hCS hQS, Subgroup.map_sup,
    eight_six_core_barred_image_eq hyp graph path hlength previous D L Q hD data
      projection hkernel]

public theorem eight_six_predecessor_barred_image_card
    {G X : Type u} [Group G] [Finite G] [Group X] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 2) (previous : graph.Vertex) (D : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hindex : QuotientCardEq (VAt graph previous ⊓ QAt graph path.a)
      ((VAt graph previous ⊓ QAt graph path.a) ⊓ D) 2)
    (projection : S →* X) (hkernel : projection.ker = (QAt graph path.firstStep).subgroupOf S) :
    Nat.card (((VAt graph previous ⊓ QAt graph path.a).subgroupOf S).map projection) = 2 := by
  have hAS : VAt graph previous ⊓ QAt graph path.a ≤ S :=
    inf_le_right.trans (SevenSix.local_cores_le_edge_sylow hyp graph path).1
  have hprevious : VAt graph previous ≤ QAt graph previous :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) _
  have hinter : (VAt graph previous ⊓ QAt graph path.a) ⊓ D =
      (VAt graph previous ⊓ QAt graph path.a) ⊓ QAt graph path.firstStep := by
    rw [hD, ← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hprevious)]
  rw [← Subgroup.relIndex_ker, hkernel, Subgroup.relIndex_subgroupOf hAS,
    ← Subgroup.inf_relIndex_left, ← hinter]
  exact eight_six_relIndex_two_of_quotient_card _ _ inf_le_left hindex

public theorem eight_six_barred_intersection_of_fixed_core
    {G X : Type u} [Group G] [Finite G] [Group X] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q T : Subgroup G)
    (hprevious : previous ∈ neighborhood graph path.a)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hfixed : Q ⊓ Subgroup.centralizer (T : Set G) ≤ D)
    (projection : S →* X) (hkernel : projection.ker = (QAt graph path.firstStep).subgroupOf S) :
    ((QAt graph path.a ⊓ Subgroup.centralizer (T : Set G)).subgroupOf S).map projection ⊓
      ((VAt graph previous ⊓ QAt graph path.a).subgroupOf S).map projection = ⊥ := by
  have hAQ : VAt graph previous ⊓ QAt graph path.a ≤ Q :=
    data.core_generation ▸ le_sup_left.trans le_sup_left
  have hIQ := eight_six_first_core_intersection_le_core hyp graph path previous
    D L Q hprevious hL hQ data
  apply le_bot_iff.mp
  rintro image ⟨⟨central, hcentral, heqcentral⟩, ⟨member, hmember, heqmember⟩⟩
  have hdifference : central * member⁻¹ ∈ projection.ker := by
    change projection (central * member⁻¹) = 1
    rw [map_mul, map_inv, heqcentral, heqmember, mul_inv_cancel]
  rw [hkernel] at hdifference
  have hinQ : (central : G) * (member : G)⁻¹ ∈ Q :=
    hIQ ⟨(QAt graph path.a).mul_mem hcentral.1
      ((QAt graph path.a).inv_mem hmember.2), hdifference⟩
  have hcentralQ : (central : G) ∈ Q := by
    have hproduct := Q.mul_mem hinQ (hAQ hmember)
    change (central : G) * (member : G)⁻¹ * (member : G) ∈ Q at hproduct
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hproduct
  have hcentralD := hfixed ⟨hcentralQ, hcentral.2⟩
  have hzero : central ∈ projection.ker := by
    rw [hkernel]
    exact (hD.le.trans inf_le_right) hcentralD
  have heq : image = 1 := heqcentral.symm.trans hzero
  exact heq

public theorem eight_six_first_core_normal_in_sylow
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph) :
    ((QAt graph path.firstStep).subgroupOf S).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((SevenSix.edge_sylow_data hyp graph path).2.1.trans
      (SevenSix.stabilizer_le_normalizer_q graph path.firstStep))

public theorem eight_six_predecessor_barred_image_central
    {G X : Type u} [Group G] [Finite G] [Group X] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 2)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hindex : QuotientCardEq (VAt graph previous ⊓ QAt graph path.a)
      ((VAt graph previous ⊓ QAt graph path.a) ⊓ D) 2)
    (projection : S →* X) (hsurjective : Function.Surjective projection)
    (hkernel : projection.ker = (QAt graph path.firstStep).subgroupOf S) :
    ((VAt graph previous ⊓ QAt graph path.a).subgroupOf S).map projection ≤
      Subgroup.center X := by
  have hLnormal : (L.subgroupOf (GAt graph path.a)).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hQinitial : Q ≤ GAt graph path.a :=
    (hQ.le.trans (SevenSix.twoCoreIn_le L)).trans data.closure_le
  have hQnormal : (Q.subgroupOf (GAt graph path.a)).Normal := by
    rw [hQ]
    exact SevenSix.twoCoreIn_normal_of_normal L _ data.closure_le hLnormal
  have hQSnormal : (Q.subgroupOf S).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((SevenSix.edge_sylow_data hyp graph path).1.1.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hQinitial).mp hQnormal))
  let _ : (((VAt graph previous ⊓ QAt graph path.a).subgroupOf S).map projection).Normal := by
    rw [← eight_six_core_barred_image_eq hyp graph path hlength previous D L Q
      hD data projection hkernel]
    exact hQSnormal.map projection hsurjective
  exact Subgroup.central_of_normal_card_two _
    (eight_six_predecessor_barred_image_card hyp graph path hlength previous D hD
      hindex projection hkernel)

public theorem eight_six_initial_first_core_sup_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hlength : ctx.criticalPath.length = 2) :
    QAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep = S := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hlength' : path.length = 2 := hlength
  have hcores := SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path
  have hindex : (QAt graph path.a).relIndex S = 2 := by
    rw [QAt, q, graph.twoCoreAt_def]
    exact eight_two_core_relIndex_two _ _
      (SevenSix.edge_sylow_data ctx.sectionSeven graph path).1
      (eight_five_dihedral_action_of_card_four_local ctx hcard).1
  have hterminal : path.a' ∈ neighborhood graph path.firstStep := by
    apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
    have hstep := path.path_adj ⟨1, by omega⟩
    have hlast : (⟨1, by omega⟩ : Fin path.length).succ =
        ⟨path.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hlast, path.path_end] at hstep
    simpa only [Fin.castSucc_mk, path.path_first] using hstep
  have hterminalCore : ZAt graph path.a' ≤ QAt graph path.firstStep := by
    apply le_trans _ (SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) _)
    rw [v, graph.vAt_def]
    exact le_sSup ⟨path.a', hterminal, rfl⟩
  have hnot : ¬ QAt graph path.firstStep ≤ QAt graph path.a := by
    intro hle
    have hfirst : path.firstStep ∈ neighborhood graph path.a :=
      (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
    have hcentral : ZAt graph path.a ≤ Subgroup.centralizer (QAt graph path.a : Set G) :=
      ((lemma_seven_three ctx.sectionSeven graph).center_core path.a path.firstStep hfirst).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
    exact ctx.commutator_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcentral.trans (Subgroup.centralizer_le (hterminalCore.trans hle))))
  have htower := Subgroup.relIndex_mul_relIndex (QAt graph path.a)
    (QAt graph path.a ⊔ QAt graph path.firstStep) S le_sup_left (sup_le hcores.1 hcores.2)
  rw [hindex] at htower
  have hdiv : (QAt graph path.a).relIndex
      (QAt graph path.a ⊔ QAt graph path.firstStep) ∣ 2 := ⟨_, htower.symm⟩
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdiv with hone | htwo
  · exact (hnot (le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone))).elim
  · rw [htwo] at htower
    have hone : (QAt graph path.a ⊔ QAt graph path.firstStep).relIndex S = 1 := by omega
    exact le_antisymm (sup_le hcores.1 hcores.2) (Subgroup.relIndex_eq_one.mp hone)

public theorem eight_six_initial_core_barred_image_top_local
    {G X : Type u} [Group G] [Finite G] [Group X] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hlength : ctx.criticalPath.length = 2)
    (projection : S →* X) (hsurjective : Function.Surjective projection)
    (hkernel : projection.ker = (QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf S) :
    ((QAt ctx.Γ ctx.criticalPath.a).subgroupOf S).map projection = ⊤ := by
  have hcores := SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath
  have hsup := eight_six_initial_first_core_sup_local ctx hcard hlength
  have hnative : (QAt ctx.Γ ctx.criticalPath.a).subgroupOf S ⊔ projection.ker = ⊤ := by
    rw [hkernel, ← Subgroup.subgroupOf_sup hcores.1 hcores.2, hsup]
    exact Subgroup.subgroupOf_self S
  have hmapped := congrArg (Subgroup.map projection) hnative
  have hkerzero : projection.ker.map projection = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr le_rfl
  rw [Subgroup.map_sup, hkerzero, sup_bot_eq, ← MonoidHom.range_eq_map,
    projection.range_eq_top_of_surjective hsurjective] at hmapped
  exact hmapped

public theorem eight_six_sylow_quotient_center_isCyclic
    {G X : Type u} [Group G] [Finite G] [Group X]
    (S : Subgroup G) (hyp : SectionThree.Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (projection : S →* X) (hsurjective : Function.Surjective projection)
    (hkernel : projection.ker = (twoCoreIn P).subgroupOf S) :
    IsCyclic (Subgroup.center X) := by
  have hSP : S ≤ P := by
    obtain ⟨sylow, hsylow⟩ := hP.1.2.1
    rw [← hsylow]
    exact Subgroup.map_subtype_le _
  let quotient := QuotientGroup.mk' (pCore 2 P)
  let image := (S.subgroupOf P).map quotient
  let inclusion : S →* P := Subgroup.inclusion hSP
  let toImage : S →* image := (quotient.comp inclusion).codRestrict image (by
    intro member
    exact Subgroup.mem_map.mpr ⟨inclusion member, member.property, rfl⟩)
  have hsurjImage : Function.Surjective toImage := by
    intro member
    obtain ⟨preimage, hpreimage, heq⟩ := member.property
    exact ⟨⟨preimage, hpreimage⟩, Subtype.ext heq⟩
  have hkerImage : toImage.ker = (twoCoreIn P).subgroupOf S := by
    ext member
    change toImage member = 1 ↔ (member : G) ∈ twoCoreIn P
    constructor
    · intro hmember
      have hquotient : quotient (inclusion member) = 1 := congrArg Subtype.val hmember
      have hcore : inclusion member ∈ pCore 2 P :=
        (QuotientGroup.eq_one_iff _).mp hquotient
      exact Subgroup.mem_map.mpr ⟨inclusion member, hcore, rfl⟩
    · rintro ⟨preimage, hpreimage, heq⟩
      apply Subtype.ext
      change quotient (inclusion member) = quotient 1
      have heq' : preimage = inclusion member := Subtype.ext heq
      rw [map_one]
      exact (QuotientGroup.eq_one_iff _).mpr (heq' ▸ hpreimage)
  let equiv : X ≃* image :=
    (QuotientGroup.quotientKerEquivOfSurjective projection hsurjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hkernel.trans hkerImage.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective toImage hsurjImage))
  exact (MulEquiv.isCyclic (Subgroup.centerCongr equiv)).mpr
    (SectionThree.sylow_quotient_center_isCyclic S hyp P hP hsolv)

public theorem eight_six_first_core_quotient_center_isCyclic
    {G X : Type u} [Group G] [Finite G] [Group X] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (projection : S →* X) (hsurjective : Function.Surjective projection)
    (hkernel : projection.ker = (QAt graph path.firstStep).subgroupOf S) :
    IsCyclic (Subgroup.center X) := by
  have hlocal := (SevenSix.edge_local_data hyp graph path).2
  apply eight_six_sylow_quotient_center_isCyclic S
    (SevenSix.sectionThreeHypotheses hyp) (GAt graph path.firstStep)
    ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2 projection hsurjective
  rw [hkernel, show QAt graph path.firstStep = twoCoreIn (GAt graph path.firstStep)
    from graph.twoCoreAt_def _]

public theorem generated_eight_six_small_index_barred_intersection
    {H X : Type u} [Group H] [Finite H] [Group X] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hdefs : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a) ∧
      Q = twoCoreIn L ∧ IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hquotient : QuotientCardEq Q D 4)
    (projection : (S.subgroupOf (P1 ⊔ P2)) →* X)
    (hkernel : projection.ker = (QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (S.subgroupOf (P1 ⊔ P2))) :
    ((QAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (T : Set (P1 ⊔ P2 : Subgroup H))).subgroupOf
      (S.subgroupOf (P1 ⊔ P2))).map projection ⊓
    ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a).subgroupOf
      (S.subgroupOf (P1 ⊔ P2))).map projection = ⊥ := by
  exact eight_six_barred_intersection_of_fixed_core ctx.sectionSeven ctx.Γ ctx.criticalPath
    previous D L Q T hprev.1 hdefs.1 hdefs.2.1 hdefs.2.2.1 data
    (generated_eight_six_small_index_fixed_core_le_intersection ctx hquot previous
      D L Q T hprev hdefs hindex data hquotient) projection hkernel

public theorem generated_eight_six_first_core_quotient_center_isCyclic
    {H X : Type u} [Group H] [Finite H] [Group X] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (projection : (S.subgroupOf (P1 ⊔ P2)) →* X)
    (hsurjective : Function.Surjective projection)
    (hkernel : projection.ker = (QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (S.subgroupOf (P1 ⊔ P2))) : IsCyclic (Subgroup.center X) :=
  eight_six_first_core_quotient_center_isCyclic ctx.sectionSeven ctx.Γ ctx.criticalPath
    projection hsurjective hkernel

end Stellmacher.SectionEight
