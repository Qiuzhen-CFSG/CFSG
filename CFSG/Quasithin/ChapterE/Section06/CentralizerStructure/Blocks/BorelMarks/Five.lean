module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.AlternatingLocal.Source
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelControl
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelMarks.Three
public import Theory.GroupTheory.SylowSmallOmegaNormalizer
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# The original alternating-five Borel mark

The A₅-block omega-center has central quotient of order two. Its Sylow
normalizer therefore centralizes that omega-center; the ambient block-action
formula puts the whole normalizer in the original characteristic-normalizer
closure. Its quotient image is an A₄ point stabilizer. Maximality of that
point stabilizer and the properness of the controlled intersection give the
full Borel preimage, including the original two-core.

Source: Aschbacher–Smith C.1.29, printed p.134, and E.6.7, p.246.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem a5_stabilizer_coatom (i : Fin 5) :
    IsCoatom (MulAction.stabilizer (alternatingGroup (Fin 5)) i) := by
  let B := MulAction.stabilizer (alternatingGroup (Fin 5)) i
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
  change IsCoatom B
  have hi : B.index = 5 := by
    exact (MulAction.index_stabilizer_of_transitive (alternatingGroup (Fin 5)) i).trans (Nat.card_fin 5)
  refine ⟨?_, ?_⟩
  · intro h
    simp [h] at hi
  · intro D hD
    have hd := index_dvd_of_le hD.le
    rw [hi] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact index_eq_one.mp h
    · have := index_strictAnti hD
      omega

theorem alternating_five_block_borel_of_control
    (hf : generalizedFitting G = pCore 2 G)
    (S : Sylow 2 G) (N L : Subgroup G)
    (hN : (S : Subgroup G).characteristicNormalizerClosure ≤ N)
    (hL : ChapterC.IsBlock L) (hout : ¬ L ≤ N)
    (htype : ChapterC.IsAlternatingBlock L 5) :
    AlternatingBlockBorel L (N.subgroupOf L) 5 := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  have hPmap : (P : Subgroup L).map L.subtype = L ⊓ S := by
    rw [hP, subgroupOf_map_subtype, inf_comm]
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hs
    have hU : (ChapterC.blockU L).map L.subtype ≤ (S : Subgroup G) :=
      (map_mono ChapterC.blockU_le_core).trans
        ((pCoreIn_le_of_subnormal 2 hL.subnormal).trans (pCore_isPGroup.le_sylow_of_normal S))
    rw [hs] at hU
    exact hL.short.blockU_ne_bot (((ChapterC.blockU L).map_eq_bot_iff_of_injective
      L.subtype_injective).mp (bot_unique hU))
  have hc := P.normalizer_centralizes_omegaCenter_of_small_quotient
    (AlternatingLocal.a5_omega_center_quotient_card_source htype P).le
  have hBN : normalizer (P : Set L) ≤ N.subgroupOf L := by
    apply map_le_iff_le_comap.mp
    exact (block_sylow_normalizer_le_characteristic_control hf S hSne L hL P hPmap hc).trans hN
  obtain ⟨e⟩ := htype.2.2.quotient_iso
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pb := P.mapSurjective hq
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer Pb
  have himage : (normalizer (P : Set L)).map q = MulAction.stabilizer (alternatingGroup (Fin 5)) i :=
    (P.normalizer_map_surjective q hq).trans hi
  have hk : q.ker ≤ N.subgroupOf L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact ChapterC.LocalC129.core_le_control_intersection S N L hN hL.subnormal
  have hproper : (N.subgroupOf L).map q ≠ ⊤ := by
    intro ht
    have hh := congrArg (Subgroup.comap q) ht
    rw [comap_map_eq_self hk,comap_top] at hh
    exact hout (subgroupOf_eq_top.mp hh)
  have heq : (N.subgroupOf L).map q = MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
    exact ((a5_stabilizer_coatom i).le_iff.mp (himage ▸ map_mono hBN)).resolve_left hproper
  refine ⟨e,i,?_⟩
  have hh := congrArg (Subgroup.comap q) heq
  rwa [comap_map_eq_self hk] at hh

end CFSG.Quasithin.ChapterE.Section06
