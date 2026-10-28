module
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import Theory.GroupTheory.CComponent.SimplePairKernel
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# The original nonnormal module action kernel

The actual nonnormal component catalogue makes L/O₂(L) simple. The
nontrivial homogeneous seed survives under both conjugate components,
so the kernel of the action of L₀T on its local module is a two-group.
Reducedness identifies that kernel with O₂(L₀T). Its faithful quotient
therefore retains the original component and its literal intrinsic quotient.

This supplies the component input to the moving-Thompson module
classification, without assuming natural coordinates or separated support.
Source: Aschbacher--Smith 1.2.1(3), 3.2.2(8), 10.1.1--2,
printed pp.504,579,741--742.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem simple_of_linear {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] {q : ℕ} (h : ClassicalGroup.IsPSL Q 2 q) : IsSimpleGroup Q := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  have hz : center Q = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨x, hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

include D in
/-- The actual nonnormal source catalogue, on the intrinsic quotient. -/
theorem component_quotient_model
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Chapter1.Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE
    (show H ∈ Chapter1.H G from D.maximal.1.2.2)
  have hnA : ¬ A.Normal := fun h => hn (le_sup_right.trans
    ((normal_subgroupOf_iff_le_normalizer (show L ≤ H from le_sup_left)).mp h))
  obtain ⟨_,hm⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    hQ D.maximal.1.1).resolve_left hnA
  let e := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  exact hm.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

include D in
/-- Every nonnormal source component has simple intrinsic two-core quotient. -/
theorem component_quotient_simple
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsSimpleGroup (L ⧸ pCore 2 L) := by
  let := D.quasisimple
  cases component_quotient_model D hn with
  | linear_even n hn he => exact simple_of_linear he
  | linear_prime p hp ho he => exact simple_of_linear he
  | suzuki m hm he =>
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    exact he.some.isSimpleGroup
  | janko he => exact he.some.isSimpleGroup

/-- The nonnormal original pair has a two-group kernel on its local module. -/
theorem local_module_kernel_isTwoGroup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsPGroup 2 (centralizer
      (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L))) := by
  let H := localJoin T L
  let A := L.subgroupOf H
  let U := D.moduleSubgroup.subgroupOf H
  let C := centralizer (U : Set H)
  have hUH : D.moduleSubgroup ≤ H := D.module_le_core.trans (pCoreIn_le 2 H)
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let : C.Normal := inferInstance
  have hAC : ¬ A ≤ C := by
    intro hc
    have hLC : L ≤ centralizer (D.moduleSubgroup : Set G) := by
      intro l hl v hv
      exact congrArg H.subtype (hc (show (⟨l,hLH hl⟩ : H) ∈ A from hl)
        ⟨v,hUH hv⟩ hv)
    have hOC : localOrbit T L ≤ centralizer (D.moduleSubgroup : Set G) :=
      iSup_conjugates_le_of_le_normalizer L T _ hLC
        (D.sylow_normalizes_module.trans (normalizer_le_normalizer_centralizer _))
    apply D.homogeneous.isIrrPlus.not_le_fixedSpace
      (ReducedNormal.representation H)
    intro w hw x
    have hxc : ((x : H) : G) ∈ centralizer (D.seed : Set G) :=
      (centralizer_le (le_componentOrbit D.seed T)) (hOC x.property)
    exact ReducedNormal.representation_fixes_of_centralizes_subspaceImage
      H D.seedSpace (x : H) hxc w hw
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tH).toMonoidHom from rfl, map_map,
      show H.subtype.comp (MulAut.conj tH).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp H.subtype from rfl, ←map_map, hmapA]
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hB : B.IsCComponent := hA.map_equiv (MulAut.conj tH)
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hp : A ⊔ B = (localOrbit T L).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,map_subgroupOf_eq_of_le le_sup_left,hpair]
  let : (A ⊔ B).Normal := hp ▸ normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  let a : A ≃* L := subgroupOfEquivOfLe hLH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := aq.isSimpleGroup
  let b : A ≃* B := (MulAut.conj tH).subgroupMap A
  let : IsSimpleGroup (B ⧸ pCore 2 B) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.isSimpleGroup
  apply isTwoGroup_of_normal_avoiding_simpleCore_pair A B
    ((T : Subgroup G).subgroupOf H) C hA hB hne T.isPGroup'.comap_subtype
    ?_ hAC ?_
  · rw [hp, ←subgroupOf_sup (show localOrbit T L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right), subgroupOf_self]
  · intro hBC
    apply hAC
    intro a ha
    have hc := hBC (mem_map_of_mem (MulAut.conj tH).toMonoidHom ha)
    have hh := (inferInstance : C.Normal).conj_mem _ hc tH⁻¹
    simpa [MulAut.conj_apply,mul_assoc] using hh


/-- The local action kernel is exactly O₂(L₀T), without an escaping-normalizer premise. -/
theorem local_module_kernel_eq_twoCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) =
      pCore 2 (localJoin T L) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, local_module_kernel_isTwoGroup D hn⟩
  · intro x hx v hv
    exact Subtype.ext (D.core_centralizes_module (mem_map_of_mem H.subtype hx) v hv)

/-- Enlarging to the actual full module retains a two-group kernel in L₀T. -/
theorem full_module_local_kernel_isTwoGroup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsPGroup 2 (centralizer
      (D.fullModule.subgroupOf (localJoin T L) : Set (localJoin T L))) := by
  exact (local_module_kernel_isTwoGroup D hn).to_le
    (centralizer_le (show D.moduleSubgroup.subgroupOf (localJoin T L) ≤
      D.fullModule.subgroupOf (localJoin T L) from fun _ hv =>
        le_componentOrbit D.moduleSubgroup D.maximalLocal hv))


/-- The literal local action quotient retains the original component. -/
theorem local_action_original_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let H := localJoin T L
    let U := D.moduleSubgroup.subgroupOf H
    let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    IsComponent (H ⧸ centralizer (U : Set H)) ((L.subgroupOf H).map q) ∧
      Nonempty (((L.subgroupOf H).map q) ≃* (L ⧸ pCore 2 L)) := by
  dsimp only
  let H := localJoin T L
  let : (D.moduleSubgroup.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let A := L.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a : A ≃* L := subgroupOfEquivOfLe hLH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let eqt := cComponentTwoCoreQuotientEquiv hA
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hh : IsComponent (H ⧸ pCore 2 H) (A.map (QuotientGroup.mk' (pCore 2 H))) ∧
      Nonempty ((A.map (QuotientGroup.mk' (pCore 2 H))) ≃* (L ⧸ pCore 2 L)) :=
    ⟨⟨hA.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv eqt⟩, ⟨eqt.symm.trans aq⟩⟩
  have htransfer (C : Subgroup H) [C.Normal] (hc : C = pCore 2 H) :
      IsComponent (H ⧸ C) (A.map (QuotientGroup.mk' C)) ∧
        Nonempty ((A.map (QuotientGroup.mk' C)) ≃* (L ⧸ pCore 2 L)) := by
    subst C
    exact hh
  exact htransfer _ (local_module_kernel_eq_twoCore D hn)



end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
