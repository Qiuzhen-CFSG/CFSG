module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingGeometry
public import Theory.Frattini.ConjugateCentralFactorsDisjoint
public import Theory.GroupTheory.OddAutomorphismElementaryIndexTwo

/-!
# The alternating centralizer contradiction from invariant-core geometry

The first half of source 3.3.31 suffices for its conclusion. Central
elementary supplements give Φ(Q)=Φ(Q∩Qᵈ)=Φ(Qᵈ). Since Φ(Q)≤C_T(L) and
the two conjugate Sylow centralizers are disjoint, Q is elementary abelian.
An odd automorphism of S then fixes its self-centralizing elementary
subgroup Q of index two. Uniqueness forces the escaping element into N_G(L).

This avoids the subsequent cyclic and elementary-four centralizer cases.
The centralizer clause is now proved for the actual omega module. Invariance,
factorization and index remain explicit source inputs; the literal original
contract and its normalizer consumer are included below.

Source: Aschbacher–Smith 3.3.27(1), 3.3.31, printed pp.600,602; B.2.21,
printed pp.82–83, supplies the elementary-lift uniqueness argument.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The elementary Frattini argument eliminates every invariant-core geometry. -/
theorem false_of_alternating_invariant_core_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hb : ChapterC.IsShort L) {d : G} (ho : Odd (orderOf d))
    (hd : d ∈ normalizer (T : Set G)) (hout : d ∉ normalizer (L : Set G))
    (geometry : AlternatingInvariantCoreGeometry T L d) : False := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let W := blockOmegaModule T L
  let Wd := W.map (MulAut.conj d⁻¹).toMonoidHom
  let S := Q ⊔ Wd
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hWQ : W ≤ Q := blockOmegaModule_le_core h
  have hdT := mem_normalizer_iff_map_conj_eq.mp ((normalizer (T : Set G)).inv_mem hd)
  have hST : S ≤ (T : Subgroup G) := sup_le hQT (by
    change W.map (MulAut.conj d⁻¹).toMonoidHom ≤ (T : Subgroup G)
    rw [← hdT]
    exact map_mono (hWQ.trans hQT))
  have hHQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hSQ := hST.trans (le_sup_right.trans hHQ)
  have hdi : d⁻¹ ∉ normalizer (L : Set G) := fun hi => hout (by
    simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem hi)
  have hSdi : d⁻¹ ∈ normalizer (S : Set G) :=
    (normalizer (S : Set G)).inv_mem geometry.invariant
  have hel : IsElementaryAbelian 2 Q :=
    elementary_of_conjugate_central_factors_disjoint S W Q
      (Q ⊓ centralizer (Wd : Set G)) ((T : Subgroup G) ⊓ centralizer (L : Set G))
      (MulAut.conj d⁻¹) (mem_normalizer_iff_map_conj_eq.mp hSdi)
      geometry.centralizer geometry.factorization inf_le_right (sup_comm Q Wd)
      (blockOmegaModule_elementary h) (isPGroup_pCoreIn 2 _) hSQ
      (local_core_frattini_le_sylow_centralizer D hb)
      (sylow_centralizer_disjoint_conjugate h D ((normalizer (T : Set G)).inv_mem hd) hdi)
  let := hel
  have hself : S ⊓ centralizer (Q : Set G) = Q := by
    apply le_antisymm
    · exact (inf_le_inf_left S (centralizer_le hWQ)).trans geometry.centralizer.ge
    · exact le_inf le_sup_left (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hdQ : d⁻¹ ∈ normalizer (Q : Set G) :=
    elementary_relIndex_two_normalized_of_odd Q S le_sup_left geometry.index
      hself d⁻¹ hSdi (by simpa only [orderOf_inv] using ho)
  have hQne : Q ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_core.trans_eq he))
  have hQL : normalizer (Q : Set G) ≤ normalizer (L : Set G) :=
    D.normal_subgroup_normalizer_le h.toHypothesis1221 (pCoreIn_le 2 _) hQne hHQ
  exact hdi (hQL hdQ)

/-- The terminal contradiction needs only the three remaining geometric claims:
the centralizer equality follows from the actual source omega module. -/
theorem false_of_alternating_core_join
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hb : ChapterC.IsShort L) {d : G} (ho : Odd (orderOf d))
    (hd : d ∈ normalizer (T : Set G)) (hout : d ∉ normalizer (L : Set G))
    (hinvariant : d ∈ normalizer (alternatingCoreJoin T L d : Set G))
    (hfactorization : (L ⊔ (T : Subgroup G)).pCoreIn 2 = blockOmegaModule T L ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
        ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G)))
    (hindex : ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex
      (alternatingCoreJoin T L d) = 2) : False := by
  have hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) :=
    fun hn => hout (hn hd)
  exact false_of_alternating_invariant_core_geometry h D hb ho hd hout
    ⟨hinvariant, alternatingCoreJoin_centralizer h D hescape hb hd, hfactorization, hindex⟩

/-- Literal contract assembly. The invariant-core source remains a genuine input. -/
theorem alternatingBlockCentralizerSource_of_invariant_core_geometry
    (geometry : AlternatingInvariantCoreGeometrySource T L V) :
    AlternatingBlockCentralizerSource T L V := by
  intro h D structural hnone hfixed hescape hi hb
  obtain ⟨d, ho, hd, hout, hg⟩ := geometry h D structural hnone hfixed hescape hi hb
  exact (false_of_alternating_invariant_core_geometry h D hb.2.1 ho hd hout hg).elim

/-- Application to the unchanged original reducible normalizer consumer. -/
theorem sylow_normalizer_le_of_alternating_invariant_core_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (reduction : BlockReductionSource T L V)
    (localSource : BlockLocalInvarianceSource T L V)
    (nonalternating : NonalternatingBlockCentralizerSource T L V)
    (geometry : AlternatingInvariantCoreGeometrySource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_local_block_branches h D structural hnone hfixed reduction
    localSource nonalternating (alternatingBlockCentralizerSource_of_invariant_core_geometry geometry)
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
