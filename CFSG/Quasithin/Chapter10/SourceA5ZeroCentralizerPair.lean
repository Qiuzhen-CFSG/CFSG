module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerBaumann
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFivePairCentralizers

/-!
# Faithful paired block centralizers in the original zero-center branch

The actual Sylow-conjugate pair from the original Fundamental Setup spans
the local two-core by its two natural layers. The local reduced module is
that core, and characteristic two makes it self-centralizing. Therefore
the kernel inside either block centralizer is precisely the opposite
natural layer, and the pair has trivial joint centralizer in L₀T.

This supplies the faithful kernels for the two symmetric-five extensions
in Aschbacher–Smith 10.2.1, printed pp.742–743. The identification of the
quotient axes remains a separate step.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original pair has exact natural kernels and trivial joint centralizer. -/
theorem source_a5_zero_centralizer_pair_centralizers
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ t : localJoin T L, (t : G) ∈ (T : Subgroup G) ∧
      let A := L.subgroupOf (localJoin T L)
      let B := A.map (MulAut.conj t).toMonoidHom
      A ≠ B ∧ ⁅A,B⁆ = ⊥ ∧
        (A ⊔ B).map (localJoin T L).subtype = localOrbit T L ∧
        pCore 2 (localJoin T L) = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype ∧
        pCore 2 (localJoin T L) ⊓ centralizer (B : Set (localJoin T L)) =
          (blockU A).map A.subtype ∧
        pCore 2 (localJoin T L) ⊓ centralizer (A : Set (localJoin T L)) =
          (blockU B).map B.subtype ∧
        centralizer ((A ⊔ B : Subgroup (localJoin T L)) : Set (localJoin T L)) = ⊥ := by
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
  have hc : ⁅A,B⁆ = ⊥ := ha.commutator_eq_bot_of_quasisimple_quotient hb hqA hne
  have hu : D.moduleSubgroup.subgroupOf H = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←hu]
    exact (source_a5_zero_centralizer_local_module_centralizer D e hn hout hz).le
  obtain ⟨hfirst,hsecond⟩ := alternatingFive_pair_core_centralizers A B haa hab hc hsplit
  exact ⟨t,ht,hne,hc,hpair,hsplit,hfirst,hsecond,
    alternatingFive_pair_centralizer_eq_bot A B haa hab hc hsplit hself⟩

end CFSG.Quasithin.Chapter10
