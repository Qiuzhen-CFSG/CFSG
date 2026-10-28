module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreSquares
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerCore
/-!
# The original natural-generation block has trivial center

The original T-conjugate is another block. Its quasisimple quotient and
C.1.9 give commutation of the pair. Their central two-core fixed subgroup
vanishes by the already established Sylow-center hypothesis, so each
block's center is trivial. The short-group square calculation then makes
the actual two-core elementary; no equality with the moved layer is assumed.

Source: Aschbacher–Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

private theorem original_pair_structure
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    center (L.subgroupOf (localJoin T L)) = ⊥ ∧
      IsElementaryAbelian 2 (pCore 2 (localJoin T L)) := by
  let H := localJoin T L
  let A := L.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hbB : IsBlock B := hb.map_equiv (MulAut.conj tH)
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tH).toMonoidHom from rfl,map_map]
    rw [show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm))
  have hc := hb.commutator_eq_bot_of_quasisimple_quotient hbB hqA hne
  have hmapPair : (A ⊔ B).map H.subtype = localOrbit T L := by
    rw [Subgroup.map_sup,hmapA,hmapB,hpair]
  have hfixed : pCore 2 H ⊓ centralizer ((A ⊔ B : Subgroup H) : Set H) = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ H.subtype_injective).mp
    apply bot_unique
    apply le_trans ?_ (source_orbit_core_centralizer_eq_bot hz).le
    apply le_inf (map_mono inf_le_left)
    have hh := (map_mono (f := H.subtype) (show
      pCore 2 H ⊓ centralizer ((A ⊔ B : Subgroup H) : Set H) ≤
        centralizer ((A ⊔ B : Subgroup H) : Set H) from inf_le_right)).trans
      (map_centralizer_le_centralizer_image _ H.subtype)
    change _ ≤ centralizer ((A ⊔ B).map H.subtype : Set G) at hh
    rwa [hmapPair] at hh
  exact ⟨hb.center_eq_bot_of_pair_core_centralizer hc hfixed,
    hb.ambient_core_elementary_of_pair_core_centralizer hbB hfixed⟩

/-- The original component's whole center vanishes. -/
theorem source_original_block_center_eq_bot
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    center L = ⊥ := by
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hza := (original_pair_structure D hn hb hz).1
  let e := subgroupOfEquivOfLe hLH
  apply bot_unique
  intro l hl
  have hmem : e.symm l ∈ center (L.subgroupOf (localJoin T L)) :=
    (centerCongr e.symm ⟨l,hl⟩).property
  rw [hza,mem_bot] at hmem
  exact mem_bot.mpr (e.symm.injective (hmem.trans e.symm.map_one.symm))

/-- The entire original local core, including any extra layers, is elementary. -/
theorem source_original_block_local_core_elementary
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    IsElementaryAbelian 2 (pCore 2 (localJoin T L)) :=
  (original_pair_structure D hn hb hz).2

theorem source_original_block_core_elementary
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    IsElementaryAbelian 2 (pCore 2 L) := by
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hs := RankOne.Solvable.isShort_of_equiv (subgroupOfEquivOfLe hLH) hb.short
  exact hs.core_elementary_of_center_eq_bot (source_original_block_center_eq_bot D hn hb hz)
end CFSG.Quasithin.Chapter10
