module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.PushingInput
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosure
public import CFSG.Quasithin.ChapterA.Section01.RankActions.LargeElementary
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# Odd-core removal in the original component normalizer

The full source module is a commutator module of order at least sixteen.
A.1.26 centralizes the odd core of N_G(L), placing it in M=N_G(V).
The original two-core O₂(M) lies in N_G(L), so mutual normalization and
coprime orders make that odd core centralize O₂(M). Characteristic two of M
then kills it. The C-component dichotomy makes every nonconstrained selected
overcomponent quasisimple.

Source: Aschbacher–Smith, proof of 10.2.6, printed pp.748–749.
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

/-- The actual component normalizer has trivial odd core. -/
theorem source_a5_component_normalizer_oddCore_eq_bot
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    pPrimeCore 2 (normalizer (L : Set G)) = ⊥ := by
  let N := normalizer (L : Set G)
  let X := localOrbit T L
  let V := D.fullModule
  let M := D.maximalLocal
  let O := (pPrimeCore 2 N).map N.subtype
  let Q := M.pCoreIn 2
  have hXN : X ≤ N := source_nonnormal_orbit_le_normalizer D hn
  have hVN : V ≤ N := D.fullModule_le_orbit.trans hXN
  let := D.fullModule_elementary (uniq D)
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  have heN : V.subgroupOf N = ⁅V.subgroupOf N,X.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hXN]
    exact D.fullModule_eq_commutator (uniq D)
  have hLV : L ≤ normalizer (V : Set G) :=
    ((le_componentOrbit L T).trans X.le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hc : 16 ≤ Nat.card V := (source_a5_full_moved_card D e).trans
    (Nat.card_le_card_of_injective _ (inclusion_injective
      (le_normalizer_iff_commutator_le_left.mp hLV)))
  have hcN : 8 < Nat.card (V.subgroupOf N) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv]
    omega
  have hXP : IsPPerfect 2 (X.subgroupOf N) :=
    ((pResidual_eq_top_iff 2 _).mp D.orbit_residual).of_surjective
      (subgroupOfEquivOfLe hXN).symm.toMonoidHom (subgroupOfEquivOfLe hXN).symm.surjective
  have hh := ChapterA.large_elementary_commutator_centralizes_oddCore
    (D.simpleQTKE.quasithin.subgroup N) (X.subgroupOf N) (V.subgroupOf N) hXP hcN heN
  have hm := congrArg (Subgroup.map N.subtype) hh
  have hcomm : ⁅V,O⁆ = ⊥ := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hVN,Subgroup.map_bot] using hm
  have hOM : O ≤ M := by
    change O ≤ D.maximalLocal
    rw [← source_fullModule_normalizer D]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQN : Q ≤ N :=
    (pCoreIn_le_pCoreIn_of_sylow T le_sup_right
      (sup_le X.le_normalizer (le_normalizer_componentOrbit L T))).trans
      (source_join_core_le_component_normalizer D)
  have hNO : N ≤ normalizer (O : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pPrimeCore 2 N).le_normalizer_map N.subtype
  have hMQ : M ≤ normalizer (Q : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hdis : Q ⊓ O = ⊥ := by
    apply (disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 M).exists_card_eq
    rw [hk,card_map_of_injective N.subtype_injective]
    exact (pPrimeCore_coprime_card (G := N) (p := 2)).pow_left k
  have hQO : ⁅Q,O⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp (hOM.trans hMQ))
      (le_normalizer_iff_commutator_le_right.mp (hQN.trans hNO))).trans_eq hdis
  have hchar : M ⊓ centralizer (Q : Set G) ≤ Q :=
    Chapter1.mem_He_iff.mpr (D.simpleQTKE.evenCharacteristic T M
      (uniq D).normalizer_maximal (le_normalizer_componentOrbit L T))
  have hOQ : O ≤ Q := (le_inf hOM
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQO))).trans hchar
  have hO : O = ⊥ := bot_unique ((le_inf hOQ le_rfl).trans_eq hdis)
  apply map_injective N.subtype_injective
  simpa only [Subgroup.map_bot] using hO

/-- A selected component whose Fitting generalized subgroup is not its two-core is ordinary. -/
theorem source_a5_nonconstrained_component_quasisimple
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {K : Subgroup G} (hK : K ∈ cComponentsIn (normalizer (L : Set G)))
    (hf : generalizedFitting K ≠ pCore 2 K) : IsQuasisimple K := by
  let j := subgroupOfEquivOfLe hK.1
  rcases hK.2.component_or_generalizedFitting_eq_pCore (source_a5_component_normalizer_oddCore_eq_bot D e hn) with hq | he
  · let := hq.2
    exact IsQuasisimple.of_mulEquiv j
  · apply (hf ?_).elim
    have hm := congrArg (Subgroup.map j.toMonoidHom) he
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hm
end CFSG.Quasithin.Chapter10
