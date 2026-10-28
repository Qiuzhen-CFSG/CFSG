module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponent
public import CFSG.Quasithin.Chapter10.SourceLocalThompsonControl
public import Theory.GroupTheory.ElementaryThompsonQuasisimpleCore

/-!
# Thompson generation of the original old residual

The literal two-residual of the original H-star member escapes M. When
J(T) centralizes the local module, the source Thompson normalizer bound
therefore prevents that residual from normalizing J(T). The quasisimple
core quotient theorem gives K=[K,J(T)], and injective image transport keeps
the original ambient Thompson subgroup throughout.

Source: Aschbacher–Smith 9.3.1 and 9.3.7, printed pp.732–734, using
3.2.10(8). The actual A₅ quotient remains the earlier 9.2.7 input.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_hstar_residual_thompson_commutator
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    (pResidual 2 H).map H.subtype =
      ⁅(pResidual 2 H).map H.subtype, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let K := pResidual 2 H
  let S : Sylow 2 H := T.subtype hH.1.1.2
  let J := elementaryAbelianMaxJ (S : Subgroup H)
  have hjmap : J.map H.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hH.1.1.2
  have hC : K.IsCComponent := by
    have hc := (source_hstar_residual_mem_local_of_a5 hH eK).1
    rw [source_hstar_residual_sup_sylow hH] at hc
    simpa only [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using hc
  let f := K.equivMapOfInjective H.subtype H.subtype_injective
  let q := f.toMonoidHom.pCoreQuotientEquiv (p := 2) f.surjective
    (by rw [f.toMonoidHom.ker_eq_bot f.injective]; exact IsPGroup.of_bot)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv (q.trans eK).symm
  have hnot : ¬ K ≤ normalizer (J : Set H) := by
    intro hh
    have hm := (map_mono (f := H.subtype) hh).trans (le_normalizer_map H.subtype)
    rw [hjmap] at hm
    exact source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH
      (hm.trans (source_local_thompson_normalizer_le_of_centralizes D hJ))
  have he := eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes
    S K hC (pResidual_sup_sylow_eq_top S) hnot
  have hm := congrArg (map H.subtype) he
  rw [map_commutator, hjmap] at hm
  exact hm

end CFSG.Quasithin.Chapter10
