module
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore
public import Theory.GroupTheory.GeneralizedFitting.MovedComponentOutside
public import Theory.GroupTheory.PCoreImage

/-!
# The component actually moved by the chosen unitary module

The fixed residual L_A is normal in N(L) intersect N(A), so its two-core
places the same chosen V in the two-core of that intersection. The completed
odd-core step and the genuine earlier uniqueness theorem give a trivial
two-core in N(A). Generalized-Fitting detection now selects an actual
component moved by V, outside N(L). Subnormality kills its two-core, and
proper K-group inheritance retains its literal simple central quotient.

Source: Aschbacher--Smith, the component choice after4.4.9 and4.4.10(1),
printed p.621. No SQTK hypothesis on the odd normalizer is introduced.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
variable {G:Type*} [Group G] [Finite G]

/-- The chosen V lies in the core of the actual intersection of normalizers. -/
theorem chosen_oddNormalizer_module_le_intersection_core
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (A:Subgroup G) (hAN:A≤normalizer (L:Set G))
    (hcomm:⁅A,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card A))
    (hAV:A≤centralizer (V:Set G)) :
    V≤(normalizer (L:Set G)⊓normalizer (A:Set G)).pCoreIn 2 := by
  obtain ⟨_,_,hc,_⟩:=chosen_oddActorResidual_cover h D A hAN hcomm hodd hAV
  have hF:oddActorResidual L A≤normalizer (L:Set G)⊓normalizer (A:Set G):=
    le_inf (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
      (((oddActorResidual_le L A).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _))
  exact hc.trans (pCoreIn_mono_of_normalizes hF (normalizes_oddActorResidual L A))

/-- Select the component on the original odd normalizer and preserve its
full inherited simple-class membership. -/
theorem chosen_oddNormalizer_exists_moved_component
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V) (hcard:Nat.card V=64)
    (A:Subgroup G) [IsMulCommutative A] (hne:A≠⊥)
    (hAN:A≤normalizer (L:Set G)) (hcomm:⁅A,L⁆≤L.pCoreIn 2)
    (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L:Set G)))
    (hout:¬normalizer (A:Set G)≤normalizer (L:Set G)) :
    ∃K:Subgroup (normalizer (A:Set G)),
      IsComponent (normalizer (A:Set G)) K ∧
      ⁅K,V.subgroupOf (normalizer (A:Set G))⁆≠⊥ ∧
      ¬K.map (normalizer (A:Set G)).subtype≤normalizer (L:Set G) ∧
      pCore 2 K=⊥ ∧ IsQuasithin K ∧ κ (K⧸center K) := by
  let N:=normalizer (A:Set G)
  let Y:=(normalizer (L:Set G)).subgroupOf N
  have hVN:V≤N:=(le_centralizer_iff.mp hAV).trans (Subgroup.centralizer_le_normalizer _)
  have hcore:pCore 2 N=⊥:=(oddNormalizer_reduction_of_cover_uniqueness D A hunique hout).2
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
    exact chosen_oddNormalizer_centralizes_oddCore h D hcard A hAN hcomm hodd hAV
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
