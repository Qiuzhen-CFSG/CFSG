module
public import CFSG.Quasithin.Chapter4.Section04.OddActorLargeModule
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Selection

/-!
# A component moved by a large chosen module in the odd normalizer

The generalized-Fitting argument only needs |V| > 8 and a trivial two-core
in N(A). The chosen module lies in the two-core of N(L) ∩ N(A) and centralizes
the odd core, so it moves a component outside N(L). All subgroups retain
their original embeddings. The exterior consumer obtains the trivial
two-core in the branch where the fixed residual has a unique overgroup.

Source: Aschbacher--Smith, the paragraph after 4.4.9 and 4.4.10(1), p.621.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
variable {G : Type*} [Group G] [Finite G]

/-- Select the component on the original odd normalizer and preserve its
full inherited simple-class membership. -/
theorem chosen_oddNormalizer_exists_moved_component_of_large_module
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V) (hcard:8<Nat.card V)
    (A:Subgroup G) [IsMulCommutative A] (hne:A≠⊥)
    (hAN:A≤normalizer (L:Set G)) (hcomm:⁅A,L⁆≤L.pCoreIn 2)
    (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G))
    (hcore:pCore 2 (normalizer (A:Set G))=⊥) :
    ∃K:Subgroup (normalizer (A:Set G)),
      IsComponent (normalizer (A:Set G)) K ∧
      ⁅K,V.subgroupOf (normalizer (A:Set G))⁆≠⊥ ∧
      ¬K.map (normalizer (A:Set G)).subtype≤normalizer (L:Set G) ∧
      pCore 2 K=⊥ ∧ IsQuasithin K ∧ κ (K⧸center K) := by
  let N:=normalizer (A:Set G)
  let Y:=(normalizer (L:Set G)).subgroupOf N
  have hVN:V≤N:=(le_centralizer_iff.mp hAV).trans (Subgroup.centralizer_le_normalizer _)
  have hvcore:=chosen_oddNormalizer_module_le_intersection_core h D A hAN hcomm hodd hAV
  have hk:IsPGroup 2 N.subtype.ker:=by
    rw [N.subtype.ker_eq_bot N.subtype_injective]
    exact IsPGroup.of_bot
  have hvY:V.subgroupOf N≤Y.pCoreIn 2:=by
    apply (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hVN,map_pCoreIn_of_ker_isPGroup N.subtype hk]
    simpa only [Y,subgroupOf_map_subtype,N] using hvcore
  have hvne:V.subgroupOf N≠⊥:=by
    intro hb
    apply D.ne_bot
    have hh:=congrArg (Subgroup.map N.subtype) hb
    simpa only [map_subgroupOf_eq_of_le hVN,Subgroup.map_bot] using hh
  have hvodd:⁅V.subgroupOf N,pPrimeCore 2 N⁆=⊥:=by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,Subgroup.map_bot]
    exact chosen_oddNormalizer_centralizes_oddCore_of_large_module h D hcard A hAN hcomm hodd hAV
  let :=D.elementary
  have hVp:IsPGroup 2 (V.subgroupOf N):=(IsElementaryAbelian.isPGroup 2 V).comap_subtype
  obtain ⟨K,hK,hm,ho⟩:=exists_component_moved_outside_of_centralizes_oddCore
    (V.subgroupOf N) Y hVp hvne hcore hvodd hvY
  have hKN:¬K.map N.subtype≤normalizer (L:Set G):=by
    intro he
    apply ho
    exact map_le_iff_le_comap.mp he
  have hKcore:pCore 2 K=⊥:=by
    rw [pCore_subnormal_eq_comap 2 hK.1,hcore,MonoidHom.comap_bot]
    exact K.subtype.ker_eq_bot K.subtype_injective
  obtain ⟨_,hqt,hkg⟩:=oddNormalizer_properQTK h.simpleQTKE A hne
  let :IsQuasisimple K:=hK.2
  let :IsSimpleGroup (K⧸center K):=IsQuasisimple.simple
  exact ⟨K,hK,hm,hKN,hKcore,hqt.subgroup K,hkg.simple_quotient K (center K)⟩
end CFSG.Quasithin.Chapter4.Section04
