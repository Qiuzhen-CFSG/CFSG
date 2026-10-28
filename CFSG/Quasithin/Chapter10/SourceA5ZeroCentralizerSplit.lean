module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerCore
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFivePairSplit
public import Theory.GroupTheory.SubgroupConjugation
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveActorCorrection

/-!
# Actual group splitting of the original zero-center A₅ block

The original paired-core decomposition removes every extra central factor
from O₂(L). Thus the alternating-five regular-kernel theorem supplies an
actual complement in the original L. Its quotient section lifts commuting
involutions of the original A₅ quotient simultaneously, retaining the given
quotient map. No supplement or involution lift is assumed.

This supplies the alternating part of the group-extension step in
Aschbacher–Smith 10.2.1, printed pp.742–743. Extending these lifts to the odd
transpositions in the paired S₅ quotient remains a separate step.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original block has no central two-core factor in the zero-center branch. -/
theorem source_a5_zero_centralizer_block_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    pCore 2 L = blockU L := by
  let H := localJoin T L
  let A := L.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  obtain ⟨ha,haa,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  obtain ⟨t,ht,hne,hb,hab,hpair,hsplit,hE⟩ :=
    source_a5_zero_centralizer_pair_core D e hn hout hz
  let B := A.map (MulAut.conj t).toMonoidHom
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm))
  have hc := ha.commutator_eq_bot_of_quasisimple_quotient hb hqA hne
  have hcore := alternatingFive_pair_block_core_eq A B ha hab hc hsplit
  have hm := congrArg (map (subgroupOfEquivOfLe hLH).toMonoidHom) hcore
  rwa [pCore_map_iso,RankOne.Solvable.blockU_map_equiv] at hm

/-- The original L splits over its actual two-core, with no supplied complement. -/
theorem source_a5_zero_centralizer_block_complement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ K : Subgroup L, (pCore 2 L).IsComplement' K := by
  obtain ⟨_,ha,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hL := RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hLH) ha
  exact hL.exists_core_complement (source_a5_zero_centralizer_block_core D e hn hout hz)

/-- The actual original quotient map has a group-homomorphic section. -/
theorem source_a5_zero_centralizer_quotient_section
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ s : (L ⧸ pCore 2 L) →* L,
      (QuotientGroup.mk' (pCore 2 L)).comp s = MonoidHom.id _ := by
  obtain ⟨K,hK⟩ := source_a5_zero_centralizer_block_complement D e hn hout hz
  let E := hK.symm.QuotientMulEquiv
  refine ⟨K.subtype.comp E.toMonoidHom,?_⟩
  apply MonoidHom.ext
  intro x
  apply E.injective
  exact quotientMulEquiv_mk_apply_of_isComplement' hK.symm (E x)

/-- Every commuting pair of quotient involutions has commuting involution lifts in L. -/
theorem source_a5_zero_centralizer_commuting_lifts
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a b : L ⧸ pCore 2 L) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) :
    ∃ x y : L, QuotientGroup.mk' (pCore 2 L) x = a ∧
      QuotientGroup.mk' (pCore 2 L) y = b ∧ x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ Commute x y := by
  obtain ⟨s,hs⟩ := source_a5_zero_centralizer_quotient_section D e hn hout hz
  refine ⟨s a,s b,DFunLike.congr_fun hs a,DFunLike.congr_fun hs b,?_,?_,hab.map s⟩
  · rw [←map_pow,ha,map_one]
  · rw [←map_pow,hb,map_one]

/-- An actor fixing the original block layer lifts to its full centralizer,
with the same image in the actual local two-core quotient. -/
theorem source_a5_block_centralizing_lift
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (g : localJoin T L)
    (hg : g ∈ normalizer (L.subgroupOf (localJoin T L) : Set (localJoin T L)))
    (hfix : g ∈ centralizer
      ((blockU (L.subgroupOf (localJoin T L))).map (L.subgroupOf (localJoin T L)).subtype :
        Set (localJoin T L))) :
    ∃ c : localJoin T L,
      c ∈ centralizer (L.subgroupOf (localJoin T L) : Set (localJoin T L)) ∧
      QuotientGroup.mk' (pCore 2 (localJoin T L)) c =
        QuotientGroup.mk' (pCore 2 (localJoin T L)) g := by
  obtain ⟨ha,haa,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  obtain ⟨u,hu⟩ := haa.exists_centralizing_correction g hg hfix
  refine ⟨((u : L.subgroupOf (localJoin T L)) : localJoin T L) * g,hu,?_⟩
  have huQ : ((u : L.subgroupOf (localJoin T L)) : localJoin T L) ∈
      pCore 2 (localJoin T L) :=
    pCoreIn_le_of_subnormal 2 ha.subnormal
      (mem_map_of_mem _ (blockU_le_core u.property))
  have heq : QuotientGroup.mk' (pCore 2 (localJoin T L))
      ((u : L.subgroupOf (localJoin T L)) : localJoin T L) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr huQ
  rw [map_mul,heq,one_mul]

end CFSG.Quasithin.Chapter10
