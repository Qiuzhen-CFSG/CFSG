module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallCoreAction
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.FirstParabolic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Quintic
public import Theory.GroupAction.RankTwoCosetGeometry.SpanCentralizerKernel
public import Theory.GroupAction.RankTwoCosetGeometry.QuinticTwoPathActors
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Exact kernels for the original centered marked (5,3) pair

The full overlap of P = YT and H is T. Its two relative normal cores give
the first-ball kernels O₂(P) and O₂(H). The proved equality C_P(V) = O₂(P)
then identifies the cubic second kernel with C_H(U_H), where U_H is the
whole original elementary orbit span. The two faithful chief factors put
this centralizer inside O₂(H); the nontrivial core action makes it proper.

The actual conjugation homomorphism on U_H therefore has exactly this
second kernel, and its image has nontrivial two-core. The final theorem
transports this equality to the exact graph inside ⟨YT,H⟩ used by the
original quintic track, through its original inclusion into G. The literal first
factor YRc, full parabolic YT and full second parabolic H are retained;
no containment of T in YRc or descent of the whole action to S₃ is used.
These exact kernels are inputs to the remaining marked recognition, whose
shared producer is qt-e-quintic-recognition. They supply no upper bound
on their orders. Original 15.2.1--8 assembly remains with
qt-e-152-small-parabolic, including the S₅ and marked-five wreath exclusions.

Source: Aschbacher--Smith 15.1.12 and 15.2.6--8, printed pp.1090,1109--1110,
and F.3.2--4, printed p.270, refs/quasithin.pdf.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem kernel_of_sylow_overlap (T : Sylow 2 G) (P H : Subgroup G)
    (hPH : P ⊓ H = (T : Subgroup G)) :
    let F : Bool → Subgroup G := fun i => if i then H else P
    ballKernel F (base F false) 1 = P.pCoreIn 2 ∧
      ballKernel F (base F true) 1 = H.pCoreIn 2 := by
  let F : Bool → Subgroup G := fun i => if i then H else P
  have hk (i : Bool) : ballKernel F (base F i) 1 = (F i).pCoreIn 2 := by
    have ht : (T : Subgroup G) ≤ F i := by
      rw [←hPH]
      cases i
      · exact inf_le_left
      · exact inf_le_right
    apply base_kernel_eq_core F i (T.subtype ht)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le ht]
    exact hPH.symm
  exact ⟨hk false,hk true⟩

/-- Both original first-ball kernels are the embedded two-cores. The
quintic one is also precisely the centralizer of the chosen four-space. -/
theorem ChosenSmallSource.marked_five_symmetricThree_first_kernels
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let P := h.residual ⊔ (T : Subgroup G)
    let F : Bool → Subgroup G := fun i => if i then H else P
    ballKernel F (base F false) 1 = P.pCoreIn 2 ∧
      ballKernel F (base F false) 1 = P ⊓ centralizer (V : Set G) ∧
      ballKernel F (base F true) 1 = H.pCoreIn 2 := by
  let P := h.residual ⊔ (T : Subgroup G)
  have hg := (h.smallResidualWitness_of_marked_five hd).1.symmetricThree_geometry hH he
  obtain ⟨hkP,hkH⟩ := kernel_of_sylow_overlap T P H hg.2.2.2.2.1
  obtain ⟨_,_,hVP,_,_,hc,_⟩ := h.marked_five_first_parabolic hd
  have hc' := congrArg (map P.subtype) hc
  rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hVP] at hc'
  exact ⟨hkP,hkP.trans hc'.symm,hkH⟩

/-- The cubic second kernel is the full centralizer of the original
elementary H-span, with both groups embedded in the original ambient G. -/
theorem ChosenSmallSource.marked_five_symmetricThree_second_kernel
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let P := h.residual ⊔ (T : Subgroup G)
    let F : Bool → Subgroup G := fun i => if i then H else P
    ballKernel F (base F true) 2 = H ⊓ centralizer (conjugateSpan H V : Set G) := by
  let P := h.residual ⊔ (T : Subgroup G)
  let F : Bool → Subgroup G := fun i => if i then H else P
  have hk := h.marked_five_symmetricThree_first_kernels hd hH he
  have hc : H ⊓ centralizer (conjugateSpan H V : Set G) ≤ H.pCoreIn 2 := by
    rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,(h.HStar_span_centralizer_lt_core hprior hH).le ?_,rfl⟩
    intro u hu
    exact Subtype.ext (hc u hu)
  have hwhole : F true ⊓ centralizer (conjugateSpanBy V (F true) : Set G) ≤
      ballKernel F (base F true) 1 := by
    change H ⊓ centralizer (conjugateSpanBy V H : Set G) ≤ _
    rw [←UniqueFactor.conjugateSpan_eq,hk.2.2]
    exact hc
  simpa only [F,if_true,←UniqueFactor.conjugateSpan_eq] using
    second_kernel_eq_span_centralizer F V hk.2.1 hwhole

/-- The whole-span core action forces a strict drop between the cubic
first and second kernels; no numerical upper bound is asserted. -/
theorem ChosenSmallSource.marked_five_symmetricThree_second_kernel_lt_first
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let P := h.residual ⊔ (T : Subgroup G)
    let F : Bool → Subgroup G := fun i => if i then H else P
    ballKernel F (base F true) 2 < ballKernel F (base F true) 1 := by
  let P := h.residual ⊔ (T : Subgroup G)
  let F : Bool → Subgroup G := fun i => if i then H else P
  have hk := h.marked_five_symmetricThree_first_kernels hd hH he
  have hc := h.marked_five_symmetricThree_second_kernel hprior hd hH he
  apply lt_of_le_of_ne (ballKernel_antitone F _ (by decide : 1 ≤ 2))
  intro heq
  apply h.HStar_core_not_centralizes_span hH
  intro x hx u hu
  have hh : (x : G) ∈ ballKernel F (base F true) 1 := hk.2.2.symm ▸ mem_map_of_mem H.subtype hx
  rw [←heq,hc] at hh
  exact Subtype.ext (hh.2 u hu)

/-- The original whole-span action has exactly the second graph kernel
and a nontrivial two-core in its image. It cannot be replaced by the
common S₃ chief-factor action. -/
theorem ChosenSmallSource.marked_five_symmetricThree_whole_action
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let P := h.residual ⊔ (T : Subgroup G)
    let F : Bool → Subgroup G := fun i => if i then H else P
    let a := actionHom H (conjugateSpan H V) (conjugateSpan_normalized H V)
    a.ker.map H.subtype = ballKernel F (base F true) 2 ∧
      pCore 2 a.range ≠ ⊥ := by
  let a := actionHom H (conjugateSpan H V) (conjugateSpan_normalized H V)
  refine ⟨?_,?_⟩
  · rw [h.marked_five_symmetricThree_second_kernel hprior hd hH he,
      actionHom_ker,subgroupOf_map_subtype,inf_comm]
  · intro hzero
    have hm : (pCore 2 H).map a.rangeRestrict ≤ pCore 2 a.range :=
      le_sSup ⟨Subgroup.Normal.map inferInstance a.rangeRestrict a.rangeRestrict_surjective,
        pCore_isPGroup.map a.rangeRestrict⟩
    rw [hzero] at hm
    have hk : pCore 2 H ≤ a.ker := by
      rw [←MonoidHom.ker_rangeRestrict a]
      intro x hx
      exact hm (mem_map_of_mem a.rangeRestrict hx)
    change pCore 2 H ≤ (actionHom H (conjugateSpan H V)
      (conjugateSpan_normalized H V)).ker at hk
    rw [actionHom_ker] at hk
    apply h.HStar_core_not_centralizes_span hH
    intro x hx u hu
    exact Subtype.ext (hk hx u hu)

/-- On the exact graph of the generated group used by the original
quintic track, inclusion maps the cubic second kernel onto C_H(U_H).
Both the vertex groups and the inclusion W → G remain literal. -/
theorem ChosenSmallSource.marked_five_symmetricThree_generated_kernel
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let P := h.residual ⊔ (T : Subgroup G)
    let W := P ⊔ H
    let F : Bool → Subgroup W := fun i => if i then H.subgroupOf W else P.subgroupOf W
    (ballKernel F (base F true) 2).map W.subtype =
      H ⊓ centralizer (conjugateSpan H V : Set G) := by
  let P := h.residual ⊔ (T : Subgroup G)
  let W := P ⊔ H
  let F : Bool → Subgroup W := fun i => if i then H.subgroupOf W else P.subgroupOf W
  have hPH : P ⊓ H = (T : Subgroup G) :=
    ((h.smallResidualWitness_of_marked_five hd).1.symmetricThree_geometry hH he).2.2.2.2.1
  have hTW : (T : Subgroup G) ≤ W := le_sup_left.trans' le_sup_right
  let S := T.subtype hTW
  have hcommon : F false ⊓ F true = (S : Subgroup W) := by
    change (P.subgroupOf W) ⊓ (H.subgroupOf W) = (T : Subgroup G).subgroupOf W
    rw [←hPH]
    rfl
  have hkernel (i : Bool) : ballKernel F (base F i) 1 = (F i).pCoreIn 2 := by
    have hle : (S : Subgroup W) ≤ F i := by
      rw [←hcommon]
      cases i
      · exact inf_le_left
      · exact inf_le_right
    apply base_kernel_eq_core F i (S.subtype hle)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hle,hcommon]
  have hVP : V ≤ P := (h.marked_five_first_parabolic hd).2.2.1
  have hVW : V ≤ W := hVP.trans le_sup_left
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  have hUW : conjugateSpan H V ≤ W := hUH.trans le_sup_right
  have hspan : conjugateSpanBy (V.subgroupOf W) (F true) =
      (conjugateSpan H V).subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hVW,
      show (F true).map W.subtype = H from map_subgroupOf_eq_of_le le_sup_right,
      map_subgroupOf_eq_of_le hUW,UniqueFactor.conjugateSpan_eq]
  have hfirst : ballKernel F (base F false) 1 =
      F false ⊓ centralizer (V.subgroupOf W : Set W) := by
    rw [hkernel false]
    change (P.subgroupOf W).pCoreIn 2 = _
    rw [pCoreIn_subgroupOf 2 P W le_sup_left]
    have hk := h.marked_five_symmetricThree_first_kernels hd hH he
    rw [hk.1.symm.trans hk.2.1]
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun v hv => Subtype.ext (hc v hv)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun v hv => congrArg Subtype.val (hc ⟨v,hVW hv⟩ hv)⟩
  have hwhole : F true ⊓ centralizer (conjugateSpanBy (V.subgroupOf W) (F true) : Set W) ≤
      ballKernel F (base F true) 1 := by
    rw [hspan,hkernel true]
    change H.subgroupOf W ⊓ centralizer ((conjugateSpan H V).subgroupOf W : Set W) ≤
      (H.subgroupOf W).pCoreIn 2
    rw [pCoreIn_subgroupOf 2 H W le_sup_right]
    rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,(h.HStar_span_centralizer_lt_core hprior hH).le ?_,rfl⟩
    intro u hu
    exact Subtype.ext (congrArg (fun z : W => (z : G)) (hc ⟨u,hUW hu⟩ hu))
  have hk := second_kernel_eq_span_centralizer F (V.subgroupOf W) hfirst hwhole
  rw [hspan] at hk
  change (ballKernel F (base F true) 2).map W.subtype = _
  rw [hk,map_inf _ _ _ W.subtype_injective,map_centralizer_subtype,
    map_subgroupOf_eq_of_le hUW,
    show (F true).map W.subtype = H from map_subgroupOf_eq_of_le le_sup_right,
    ←inf_assoc,inf_eq_left.mpr (show H ≤ W from le_sup_right)]
end CFSG.Quasithin.Chapter15.Section02
