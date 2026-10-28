module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.Nonconstrained
/-!
# Removing the odd core in source orbit overgroups

The original full module and its two-perfect orbit lie in any overgroup
considered here. A.1.26 centralizes that overgroup's odd core on the full
module. The odd core therefore lies in M, and the literal O₂(L₀T) supplies
the mutual normalization with O₂(M). Characteristic two of M kills it.
This is the source odd-core argument with only the needed containment
hypotheses; it applies to the actual moved-factor normalizer.

Source: Aschbacher--Smith, Lemma 10.2.6, printed p.749.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
private theorem uniq : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
/-- Any SQTK overgroup retaining the actual orbit and local two-core has trivial odd core. -/
theorem source_a5_orbit_overgroup_oddCore_eq_bot
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {H : Subgroup G} (_hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hXH : localOrbit T L ≤ H) (hRH : (localJoin T L).pCoreIn 2 ≤ H) :
    pPrimeCore 2 H = ⊥ := by
  let X := localOrbit T L
  let V := D.fullModule
  let M := D.maximalLocal
  let O := (pPrimeCore 2 H).map H.subtype
  let Q := M.pCoreIn 2
  have hVH : V ≤ H := D.fullModule_le_orbit.trans hXH
  let := D.fullModule_elementary (uniq D)
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  have heH : V.subgroupOf H = ⁅V.subgroupOf H,X.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hXH]
    exact D.fullModule_eq_commutator (uniq D)
  have hLV : L ≤ normalizer (V : Set G) :=
    ((le_componentOrbit L T).trans X.le_normalizer).trans D.maximalLocal_normalizes_fullModule
  have hc : 16 ≤ Nat.card V := (source_a5_full_moved_card D e).trans
    (Nat.card_le_card_of_injective _ (inclusion_injective
      (le_normalizer_iff_commutator_le_left.mp hLV)))
  have hcH : 8 < Nat.card (V.subgroupOf H) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv]
    omega
  have hXP : IsPPerfect 2 (X.subgroupOf H) :=
    ((pResidual_eq_top_iff 2 _).mp D.orbit_residual).of_surjective
      (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  have hh := ChapterA.large_elementary_commutator_centralizes_oddCore
    (D.simpleQTKE.quasithin.subgroup H) (X.subgroupOf H) (V.subgroupOf H) hXP hcH heH
  have hm := congrArg (Subgroup.map H.subtype) hh
  have hcomm : ⁅V,O⁆ = ⊥ := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hVH,Subgroup.map_bot] using hm
  have hOM : O ≤ M := by
    change O ≤ D.maximalLocal
    rw [← source_fullModule_normalizer D]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQH : Q ≤ H := (pCoreIn_le_pCoreIn_of_sylow T le_sup_right
    (sup_le X.le_normalizer (le_normalizer_componentOrbit L T))).trans hRH
  have hHO : H ≤ normalizer (O : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pPrimeCore 2 H).le_normalizer_map H.subtype
  have hMQ : M ≤ normalizer (Q : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hdis : Q ⊓ O = ⊥ := by
    apply (disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 M).exists_card_eq
    rw [hk,card_map_of_injective H.subtype_injective]
    exact (pPrimeCore_coprime_card (G := H) (p := 2)).pow_left k
  have hQO : ⁅Q,O⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp (hOM.trans hMQ))
      (le_normalizer_iff_commutator_le_right.mp (hQH.trans hHO))).trans_eq hdis
  have hchar : M ⊓ centralizer (Q : Set G) ≤ Q :=
    Chapter1.mem_He_iff.mpr (D.simpleQTKE.evenCharacteristic T M
      (uniq D).normalizer_maximal (le_normalizer_componentOrbit L T))
  have hOQ : O ≤ Q := (le_inf hOM
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQO))).trans hchar
  have hO : O = ⊥ := bot_unique ((le_inf hOQ le_rfl).trans_eq hdis)
  apply map_injective H.subtype_injective
  simpa only [Subgroup.map_bot] using hO

/-- The nonconstrained component alternative is quasisimple in the actual source overgroup. -/
theorem source_a5_orbit_overgroup_component_quasisimple
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {H : Subgroup G} (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hXH : localOrbit T L ≤ H) (hRH : (localJoin T L).pCoreIn 2 ≤ H)
    {K : Subgroup G} (hK : K ∈ cComponentsIn H)
    (hf : generalizedFitting K ≠ pCore 2 K) : IsQuasisimple K := by
  let j := subgroupOfEquivOfLe hK.1
  rcases hK.2.component_or_generalizedFitting_eq_pCore
    (source_a5_orbit_overgroup_oddCore_eq_bot D e hsq hXH hRH) with hq | he
  · let := hq.2
    exact IsQuasisimple.of_mulEquiv j
  · apply (hf ?_).elim
    have hm := congrArg (Subgroup.map j.toMonoidHom) he
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hm
end CFSG.Quasithin.Chapter10
