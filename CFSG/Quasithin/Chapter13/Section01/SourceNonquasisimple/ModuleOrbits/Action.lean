module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.RadicalCentralizationComplete

/-!
# The literal moved-module action and its component kernel

The normalizer of L acts on U=[R₂(N_G(L)),L]. Perfectness gives [U,L]=U,
so the action of L is nontrivial. Its kernel is a proper normal subgroup
of the C-component L and hence is solvable. Radical centralization gives
the reverse inclusion. Thus this kernel, like the kernel on R₂(N_G(L)),
is exactly O∞(L). The two component images are identified over the
original quotient map, rather than merely identified as abstract groups.

Source: Aschbacher--Smith, 13.1.8--10, printed pp.869--872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The whole original normalizer preserves the moved subgroup. -/
theorem normalizer_le_normalizer_moved (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (normalizerMoved L : Set G) := by
  let M := normalizer (L : Set G)
  let A := L.subgroupOf M
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let V := reducedTwoSubgroup M
  let : V.Normal := isPReduced_reducedPSubgroup.normal
  have he : ⁅V,A⁆.map M.subtype = normalizerMoved L := by
    rw [map_commutator,map_subgroupOf_eq_of_le L.le_normalizer,normalizerMoved_eq]
  rw [← he]
  apply le_normalizer_iff.mpr
  intro g hg u hu
  obtain ⟨v,hv,rfl⟩ := hu
  exact ⟨(⟨g,hg⟩ : M)*v*(⟨g,hg⟩ : M)⁻¹,
    (inferInstance : (⁅V,A⁆ : Subgroup M).Normal).conj_mem v hv ⟨g,hg⟩,rfl⟩

/-- Conjugation on the actual U, before any choice of model coordinates. -/
@[expose] def action (L : Subgroup G) :
    normalizer (L : Set G) →* MulAut (normalizerMoved L) :=
  (normalizerMoved L).normalizerMonoidHom.comp
    (inclusion (normalizer_le_normalizer_moved L))

/-- Restriction of the same action to the original component. -/
@[expose] def componentAction (L : Subgroup G) : L →* MulAut (normalizerMoved L) :=
  (action L).comp (inclusion L.le_normalizer)

@[expose] def componentImage (L : Subgroup G) : Subgroup (MulAut (normalizerMoved L)) :=
  (componentAction L).range

omit [Finite G] in
/-- Its kernel is the literal centralizer in L, with the original inclusion. -/
theorem componentAction_ker (L : Subgroup G) :
    (componentAction L).ker =
      (centralizer (normalizerMoved L : Set G)).comap L.subtype := by
  ext l
  rw [MonoidHom.mem_ker,mem_comap,mem_centralizer_iff]
  constructor
  · intro hl u hu
    have he := congrArg (fun f : MulAut (normalizerMoved L) =>
      ((f ⟨u,hu⟩ : normalizerMoved L) : G)) hl
    change (l : G)*u*(l : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hl
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change (l : G)*(u : G)*(l : G)⁻¹ = (u : G)
    have hc : (u : G)*(l : G) = (l : G)*(u : G) := hl u u.property
    rw [← hc,mul_inv_cancel_right]

/-- The moved-module kernel is precisely the solvable radical. -/
theorem componentAction_ker_eq_radical
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (componentAction L).ker = solvableRadical L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hne := (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1
  have hm := (normalizerMoved_commutator_and_card hL.1.1 hne).1
  have ht : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using hL.1.1.1.subgroupOf_of_le le_rfl le_sup_left
  have hk : (componentAction L).ker ≠ ⊤ := by
    intro hk
    have hc : L ≤ centralizer (normalizerMoved L : Set G) := by
      intro l hl
      have hh : (⟨l,hl⟩ : L) ∈ (componentAction L).ker := hk ▸ mem_top _
      rwa [componentAction_ker] at hh
    apply hne
    rw [← hm,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  refine le_antisymm (kernel_le_solvableRadical_of_top_isCComponent ht _ hk) ?_
  rw [componentAction_ker]
  exact map_le_iff_le_comap.mp (solvableRadical_centralizes_normalizerMoved h hmany hL.1 hn)

/-- The original centralizer identity on U, in the ambient group. -/
theorem component_centralizer_eq_radical
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    L ⊓ centralizer (normalizerMoved L : Set G) = (solvableRadical L).map L.subtype := by
  have he := congrArg (Subgroup.map L.subtype) (componentAction_ker_eq_radical h hmany hL hn)
  rw [componentAction_ker,map_comap_eq,range_subtype] at he
  exact he

/-- The first isomorphism theorem for the original action on U. -/
noncomputable def radicalEquivMovedImage
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (L ⧸ solvableRadical L) ≃* componentImage L :=
  (QuotientGroup.quotientMulEquivOfEq (componentAction_ker_eq_radical h hmany hL hn).symm).trans
    (QuotientGroup.quotientKerEquivRange (componentAction L))

theorem radicalEquivMovedImage_mk
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (l : L) :
    (radicalEquivMovedImage h hmany hL hn (QuotientGroup.mk' (solvableRadical L) l) :
      MulAut (normalizerMoved L)) = componentAction L l := by
  simp only [radicalEquivMovedImage]
  rfl

/-- The reduced and moved component images agree over L/O∞(L). -/
noncomputable def reducedImageEquivMovedImage
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    NormalizerReducedAction.componentImage L ≃* componentImage L :=
  (NormalizerReducedAction.radicalQuotientEquiv hL.1.1
    (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).2.2.2.1
    (solvableRadical_centralizes_normalizerReduced h hmany hL.1 hn)).symm.trans
      (radicalEquivMovedImage h hmany hL hn)

theorem reducedImageEquivMovedImage_component
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (l : L) :
    (reducedImageEquivMovedImage h hmany hL hn
      ⟨NormalizerReducedAction.componentMap L l,
        NormalizerReducedAction.componentMap_range L ▸ ⟨l,rfl⟩⟩ :
      MulAut (normalizerMoved L)) = componentAction L l := by
  let e := NormalizerReducedAction.radicalQuotientEquiv hL.1.1
    (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).2.2.2.1
    (solvableRadical_centralizes_normalizerReduced h hmany hL.1 hn)
  have he : (⟨NormalizerReducedAction.componentMap L l,
      NormalizerReducedAction.componentMap_range L ▸ ⟨l,rfl⟩⟩ :
      NormalizerReducedAction.componentImage L) = e (QuotientGroup.mk' (solvableRadical L) l) :=
    Subtype.ext (NormalizerReducedAction.radicalQuotientEquiv_mk _ _ _ l).symm
  change (radicalEquivMovedImage h hmany hL hn (e.symm _) : MulAut (normalizerMoved L)) = _
  rw [he,e.symm_apply_apply]
  exact radicalEquivMovedImage_mk h hmany hL hn l

/-- The PSL₂(p) action in 13.1.8 also holds on the literal moved module. -/
theorem moved_component_pslTwo
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ClassicalGroup.IsPSL (componentImage L) 2 p := by
  obtain ⟨p,hp,hp3,he⟩ := nonquasisimple_local_radical_quotient h.simpleQTKE T hL.1.1 hn
  exact ⟨p,hp,hp3,he.of_mulEquiv (radicalEquivMovedImage h hmany hL hn).symm⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
