module
public import CFSG.Quasithin.Chapter10.SourceA5FullModule
public import Theory.GroupTheory.CComponent.SimplePairKernel

/-!
# The original paired A₅ module has a two-group kernel

The actual two conjugate C-components have simple two-core quotients and
generate the local join with T. A normal kernel missing both components
is therefore a two-group. The local-module kernel misses L: otherwise
T-invariance makes it centralize the whole orbit, contradicting the proved
commutator generation of the same nonzero full/local module.

This applies in both center branches of 10.2.1. It does not identify the
module with the local two-core. Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_module_centralizer_isTwoGroup
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
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
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal
    have hg := D.fullModule_eq_commutator hu
    rw [source_a5_exception_fullModule_eq D e hn hout, commutator_comm,
      commutator_eq_bot_iff_le_centralizer.mpr hOC] at hg
    exact D.module_ne_bot hg
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
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let a : A ≃* L := subgroupOfEquivOfLe hLH
  let aq := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
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

end CFSG.Quasithin.Chapter10
