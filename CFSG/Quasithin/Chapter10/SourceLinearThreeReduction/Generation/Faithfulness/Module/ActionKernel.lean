module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.Coprimality
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import Theory.GroupTheory.CComponent.SimplePairKernel

/-!
# The action kernel of the original nonnormal component pair

The two component quotients are simple, and neither component centralizes
the original noncentral seed. A normal kernel avoiding both components is
a two-group. Reducedness identifies the local kernel with O₂(L₀T), and
enlarging to the full module retains the two-group bound. No A₅ marking
or assumption about irreducibility of the full module is used.

The full-module conclusion supplies the centralizer-intersection step in
the normal-component placement argument of 4.4.10(3).
Source: Aschbacher--Smith, 3.2.2(8) and 4.4.10, printed pp.579,621
(combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The nonnormal original nonnormal pair has a two-group kernel on its local module. -/
theorem source_nonnormal_local_module_kernel_isTwoGroup
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
  let Q := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let eQ : (Q ⧸ center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq
      (source_nonnormal_component_core_center D hn)).trans QuotientGroup.quotientBot
  let : IsSimpleGroup Q := eQ.symm.isSimpleGroup
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
theorem source_nonnormal_local_module_kernel_eq_twoCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) =
      pCore 2 (localJoin T L) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, source_nonnormal_local_module_kernel_isTwoGroup D hn⟩
  · intro x hx v hv
    exact Subtype.ext (D.core_centralizes_module (mem_map_of_mem H.subtype hx) v hv)

/-- Enlarging to the actual full module retains a two-group kernel in L₀T. -/
theorem source_nonnormal_full_module_local_kernel_isTwoGroup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsPGroup 2 (centralizer
      (D.fullModule.subgroupOf (localJoin T L) : Set (localJoin T L))) := by
  exact (source_nonnormal_local_module_kernel_isTwoGroup D hn).to_le
    (centralizer_le (show D.moduleSubgroup.subgroupOf (localJoin T L) ≤
      D.fullModule.subgroupOf (localJoin T L) from fun _ hv =>
        le_componentOrbit D.moduleSubgroup D.maximalLocal hv))


end CFSG.Quasithin.Chapter10
