module
public import CFSG.Quasithin.Chapter10.SourceThompsonControl
public import Stellmacher.ElementaryAbelianMaxFusion
public import Theory.GroupTheory.SubgroupConjugateIncidence

/-!
# Fusion and Sylow transport for the original full module

When the elementary Thompson subgroup centralizes the full module, its
weak closure gives Burnside fusion for every subgroup of that module.
The source Thompson-normalizer bound places the correcting conjugators
in the original maximal local subgroup. Since that subgroup normalizes
the full module, this also controls conjugates containing a prescribed
subgroup and proves uniqueness when its normalizer lies in M.

A two-subgroup containing J(T) has its normalizer in M. The normalizer
condition therefore upgrades Sylow membership in M ∩ K to membership
in K. The tensor point-centralizer application uses this with C_T(v).

Source: Aschbacher--Smith 3.2.10(2--4), printed pp.583--584. These
statements concern the full module, which is normal in M; the separate
TI-module version is not used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
include D hJ

theorem source_fullModule_subgroup_fusion {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (g : G) (hg : U.map (MulAut.conj g).toMonoidHom ≤ D.fullModule) :
    ∃ n ∈ D.maximalLocal,
      U.map (MulAut.conj n).toMonoidHom = U.map (MulAut.conj g).toMonoidHom := by
  have hn {W : Subgroup G} (hWV : W ≤ D.fullModule) :
      elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (W : Set G) :=
    hJ.trans ((centralizer_le hWV).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨n,hnJ,he⟩ := T.weakly_closed_normalizer_controls_set_fusion
    (elementaryAbelianMaxJ (T : Subgroup G))
    (sSup_le fun _ h => h.1) (maxJ_weakly_closed_normalizer T)
    (U : Set G) (U.map (MulAut.conj g).toMonoidHom : Set G)
    (hn hUV) (hn hg) g rfl
  exact ⟨n,source_thompson_normalizer_le_of_centralizes D hJ hnJ,
    SetLike.coe_injective he⟩

theorem source_fullModule_element_fusion {x y : G}
    (hx : x ∈ D.fullModule) (hy : y ∈ D.fullModule) (hxy : IsConj x y) :
    ∃ n ∈ D.maximalLocal, n * x * n⁻¹ = y := by
  have hc {z : G} (hz : z ∈ D.fullModule) :
      z ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    fun j hj => (hJ hj z hz).symm
  obtain ⟨n,hn,he⟩ := T.weakly_closed_normalizer_controls_centralizer_fusion
    (elementaryAbelianMaxJ (T : Subgroup G))
    (sSup_le fun _ h => h.1) (maxJ_weakly_closed_normalizer T)
    (hc hx) (hc hy) hxy
  exact ⟨n,source_thompson_normalizer_le_of_centralizes D hJ hn,he⟩

theorem source_fullModule_conjugate_through {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (g : G) (hg : U ≤ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    ∃ c ∈ normalizer (U : Set G),
      D.fullModule.map (MulAut.conj c).toMonoidHom =
        D.fullModule.map (MulAut.conj g).toMonoidHom := by
  apply Subgroup.exists_normalizer_conjugator_of_subgroup_fusion U D.fullModule _ g hg
  intro a ha
  obtain ⟨n,hn,he⟩ := source_fullModule_subgroup_fusion D hJ hUV a ha
  exact ⟨n,D.maximalLocal_normalizes_fullModule hn,he⟩

theorem source_fullModule_unique_conjugate {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hn : normalizer (U : Set G) ≤ D.maximalLocal)
    (g : G) (hg : U ≤ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule := by
  obtain ⟨c,hc,he⟩ := source_fullModule_conjugate_through D hJ hUV g hg
  rw [←he]
  exact mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule (hn hc))

theorem source_sylow_in_of_thompson_le (R K : Subgroup G)
    (hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ R)
    (hR : Chapter1.IsSylowIn 2 R (D.maximalLocal ⊓ K)) :
    Chapter1.IsSylowIn 2 R K := by
  obtain ⟨hp,hRM,hmax⟩ := Chapter1.isSylowIn_iff.mp hR
  have hn := (source_two_overgroup_normalizer_le_of_centralizes D hJ R hp hJR).2
  apply Chapter1.isSylowIn_iff.mpr
  refine ⟨hp,hRM.trans inf_le_right,?_⟩
  intro S hS hRS hSK
  let : Group.IsNilpotent S := hS.isNilpotent
  have he : S ⊓ normalizer (R : Set G) = R :=
    hmax _ (hS.to_le inf_le_left) (le_inf hRS R.le_normalizer)
      (le_inf (inf_le_right.trans hn) (inf_le_left.trans hSK))
  have hnR : normalizer (R.subgroupOf S : Set S) = R.subgroupOf S := by
    rw [← subgroupOf_normalizer_eq hRS]
    ext x
    change (x : G) ∈ normalizer (R : Set G) ↔ (x : G) ∈ R
    constructor
    · intro hx
      exact he.le ⟨x.property,hx⟩
    · intro hx
      exact R.le_normalizer hx
  have ht : R.subgroupOf S = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := S)) _ hnR
  exact le_antisymm (subgroupOf_eq_top.mp ht) hRS

end CFSG.Quasithin.Chapter10
