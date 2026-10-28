module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaCenterFree
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# The genuine QRC configuration on the central Omega core

Let Q = O₂(L₀T) and W = Ω₁Z(Q). The kernel of the original tensor action
on L₀ is O₂(L₀). Since T is a two-group supplement, the kernel on L₀T
is a two-group, hence exactly Q by reducedness of the original module.
The inclusions V ≤ W ≤ Z(Q) then show C_{L₀T}(W)=Q as well. Thus the
actual action on W is reduced, and every original H* gives a QRC
configuration on W with source case (I), normalizing the two-residual.

This supplies the hypotheses for the numerical source producer on W;
it does not replace that larger-module bound by a bound only on V.
Source: Aschbacher–Smith 3.1.5–8 and 9.2.2, printed pp.573–576 and730.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The full tensor module has exactly the local two-core as its join centralizer. -/
theorem centralizer_fullModule_join_eq_core :
    (localJoin T L) ⊓ centralizer (D.fullModule : Set G) = (localJoin T L).pCoreIn 2 := by
  let J := localJoin T L
  let X := (localOrbit T L).subgroupOf J
  have hn : J ≤ normalizer (D.fullModule : Set G) := by
    rw [← m.module_eq]
    exact D.join_normalizes_module
  let f := ChapterD.UniqueFactor.actionHom J D.fullModule hn
  have hxnormal : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  let : X.Normal := hxnormal
  have hgen : X ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hk : IsPGroup 2 (f.comp X.subtype).ker := by
    let r : (f.comp X.subtype).ker →* pCore 2 (localOrbit T L) :=
      ((subgroupOfEquivOfLe (show localOrbit T L ≤ J from le_sup_left)).toMonoidHom.comp
          (f.comp X.subtype).ker.subtype).codRestrict _ (by
            intro x
            have hc : (x.val.val : G) ∈ centralizer (D.fullModule : Set G) := by
              have hker : x.val.val ∈ f.ker := x.property
              rw [ChapterD.UniqueFactor.actionHom_ker] at hker
              exact hker
            have hx := (m.centralizer_localOrbit_iff ⟨x.val.val,x.val.property⟩).mp hc
            rwa [m.kernel_eq] at hx)
    apply pCore_isPGroup.of_injective r
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 (localOrbit T L) => (x.val : G)) hab
  have hkp := f.kernel_isPGroup_of_normal_supplement X _ T.isPGroup'.comap_subtype hgen hk
  have hi : pCore 2 f.range = ⊥ := by
    have h127 := source_module_nonsolvable_uniqueness D
    have hred := internalActionImage_core_of_reduced J D.fullModule
      (D.fullModule_le_orbit.trans le_sup_left) hn (by
        have h := D.module_reduced h127
        have ht (V W : Subgroup G) (he : V = W) :
            IsPReduced 2 (V.subgroupOf J) → IsPReduced 2 (W.subgroupOf J) := by
          subst W
          exact id
        exact ht _ _ m.module_eq h)
    exact hred
  have hker := f.ker_eq_pCore_of_range_core_eq_bot 2 hkp hi
  have he := congrArg (Subgroup.map J.subtype) hker
  rw [ChapterD.UniqueFactor.actionHom_ker,subgroupOf_map_subtype,inf_comm] at he
  exact he

omit [Finite G] m in
/-- The original join normalizes its characteristic central Omega core. -/
theorem join_normalizes_omegaCenter_core :
    localJoin T L ≤ normalizer (omegaCenterIn ((localJoin T L).pCoreIn 2) : Set G) := by
  have hq : localJoin T L ≤ normalizer ((localJoin T L).pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 (localJoin T L)).le_normalizer_map (localJoin T L).subtype
  exact hq.trans (normalizer_le_normalizer_omegaCenterIn _)

/-- The larger Omega module has the same literal centralizer as the tensor module. -/
theorem centralizer_omegaCenter_core_join_eq_core :
    (localJoin T L) ⊓ centralizer (omegaCenterIn ((localJoin T L).pCoreIn 2) : Set G) =
      (localJoin T L).pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le m.fullModule_le_omegaCenter_core)).trans
      m.centralizer_fullModule_join_eq_core.le
  · refine le_inf (pCoreIn_le _ _) ?_
    intro q hq u hu
    exact ((mem_omegaCenterIn_iff _ _).mp hu).2.1 q hq |>.symm

/-- The action on the larger Omega module has precisely the actual local core kernel. -/
theorem omegaCenter_core_action_ker :
    (ChapterD.UniqueFactor.actionHom (localJoin T L)
      (omegaCenterIn ((localJoin T L).pCoreIn 2)) join_normalizes_omegaCenter_core).ker =
      pCore 2 (localJoin T L) := by
  apply Subgroup.map_injective (localJoin T L).subtype_injective
  rw [ChapterD.UniqueFactor.actionHom_ker,subgroupOf_map_subtype,inf_comm]
  exact m.centralizer_omegaCenter_core_join_eq_core

/-- Every original H* supplies the genuine source case (I) QRC configuration on Ω₁Z(Q). -/
theorem omegaCenter_core_qrcHypotheses {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    Chapter3.QrcHypotheses T D.maximalLocal (localJoin T L) H
      (omegaCenterIn ((localJoin T L).pCoreIn 2)) := by
  have h127 := source_module_nonsolvable_uniqueness D
  have hbase := D.qrcHypotheses h127 hH
  refine ⟨hbase.sylow_le,hbase.left_le,hH,?_,join_normalizes_omegaCenter_core,
    inferInstance,?_,?_,Or.inl ?_⟩
  · intro u hu
    exact pCoreIn_le 2 _ ((mem_omegaCenterIn_iff _ _).mp hu).1
  · exact pCore_range_eq_bot_of_ker_eq_pCore 2 _ m.omegaCenter_core_action_ker
  · apply le_antisymm
    · refine le_inf ?_ ?_
      · simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
          pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)
      · exact m.centralizer_omegaCenter_core_join_eq_core.ge.trans inf_le_right
    · exact (inf_le_inf_left _ (centralizer_le m.fullModule_le_omegaCenter_core)).trans (by
        rw [← m.module_eq]
        exact (D.sylow_centralizer_module h127).le)
  · have he := embedded_pResidual_join_pGroup (localOrbit T L) (T : Subgroup G)
      ((pResidual_eq_top_iff 2 _).mp D.orbit_residual) T.isPGroup'
      (le_normalizer_componentOrbit L T)
    rw [he]
    exact inf_le_right

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
