module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.PushingInput
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses
/-!
# Conditional C.2.7 input for a strict opposite component

The source setup fixes the ambient normalizer and the exact two-core. This
adapter records the remaining classification fields without weakening them: a
quasisimple quotient and the fitting equality must still be supplied by the
source component branch. The strict opposite enlargement proves the component
is outside the restricted maximal-local group, while the normality field gives
the literal R-normalization required by C.2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The literal conjugate factor is a C-component of the original M. -/
theorem source_conjugate_component_in_maximalLocal {t : G} (ht : t ∈ (T : Subgroup G)) :
    ((L.map (MulAut.conj t).toMonoidHom).subgroupOf D.maximalLocal).IsCComponent := by
  let M := D.maximalLocal
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have htM : t ∈ M := le_normalizer_componentOrbit L T ht
  let tM : M := ⟨t,htM⟩
  have hB := D.component_in_maximalLocal.map_equiv (MulAut.conj tM)
  have hBM : L.map (MulAut.conj t).toMonoidHom ≤ M := by
    rw [← mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer htM)]
    exact map_mono hLM
  have he : (L.subgroupOf M).map (MulAut.conj tM).toMonoidHom =
      (L.map (MulAut.conj t).toMonoidHom).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_map,show M.subtype.comp (MulAut.conj tM).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp M.subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le hLM,map_subgroupOf_eq_of_le hBM]
  exact he ▸ hB

/-- A strict containing C-component of an original factor lies outside M. -/
theorem source_strict_conjugate_component_outside {t : G} (ht : t ∈ (T : Subgroup G))
    {H K : Subgroup G} (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj t).toMonoidHom < K) : ¬ K ≤ D.maximalLocal := by
  intro hKM
  have hBc := (source_conjugate_component_in_maximalLocal D ht).subgroupOf_of_le hBK.le hKM
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  have he := congrArg (map K.subtype) (hBc.eq_of_le htop le_top)
  rw [map_subgroupOf_eq_of_le hBK.le,←MonoidHom.range_eq_map,range_subtype] at he
  exact hBK.ne he

/-- All geometric C.2.7 input for an actual normal strict opposite component;
only its intrinsic quotient and Fitting branch remain to be determined. -/
theorem source_nonnormal_component_c27_input
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn (normalizer (L : Set G)))
    (hKN : (K.subgroupOf (normalizer (L : Set G))).Normal)
    (hBK : L.map (MulAut.conj t).toMonoidHom < K)
    (hQ : IsQuasisimple (K ⧸ pCore 2 K))
    (hF : generalizedFitting K = pCore 2 K) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple (normalizer (L : Set G))
      ((localJoin T L).pCoreIn 2) (normalizer (L : Set G) ⊓ D.maximalLocal) K := by
  refine ⟨source_nonnormal_component_normalizer_pushing_setup D hn,hK,hQ,hF,?_,?_⟩
  · exact fun h => source_strict_conjugate_component_outside D ht hK hBK (h.trans inf_le_right)
  · exact (source_join_core_le_component_normalizer D).trans
      ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKN)

end CFSG.Quasithin.Chapter10
