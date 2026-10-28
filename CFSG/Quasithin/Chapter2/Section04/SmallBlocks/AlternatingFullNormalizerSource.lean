module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingFullCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.Source
/-!
# The full natural-module normalizer in the single alternating-five case

When the Sylow centralizer factor is trivial, the natural module is the full
2-core of the selected subgroup, is self-centralizing in the ambient group,
and has that subgroup as its full normalizer. The proof uses the original
characteristic-two normalizer statement, normality of the non-three block,
and the marked symmetric-five action to compare the two normalizer orders.

Source: Aschbacher–Smith, (2.4.29), printed p.545.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis ChapterC.Section05.BlockAnalysis.AlternatingSetup
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem MinimalBlockSetup.single_alternating_full_normalizer_of_centralizer_bot
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥) :
    let U := sourceModule (d.block.map d.H.subtype)
    twoCore d.H=U ∧ centralizer (U : Set G)=U ∧ normalizer (U : Set G)=d.H := by
  let L := d.block.map d.H.subtype
  let U := sourceModule L
  let N := normalizer (U : Set G)
  let Ui := (blockU d.block).map d.block.subtype
  let Di := centralizer (d.block : Set d.H)
  have hDi : Di=⊥ := by
    apply (map_eq_bot_iff_of_injective Di d.H.subtype_injective).mp
    exact (d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA).trans hD
  have hcorei : pCore 2 d.H=Ui := by
    have hh := (d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA).2.2.2.1
    change pCore 2 d.H=Ui⊔Di at hh
    simpa only [hDi,sup_bot_eq] using hh
  have hUi : Ui.map d.H.subtype=U := (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hcore : twoCore d.H=U := by
    change (pCore 2 d.H).map d.H.subtype=U
    rw [hcorei,hUi]
  have hUH : U≤d.H := hUi ▸ map_subtype_le _
  have hUN : U≤N := U.le_normalizer
  have hHN : d.H≤N := by
    change d.H≤normalizer (U : Set G)
    rw [←hcore]
    exact le_normalizer_twoCore d.H
  have hMe := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  obtain ⟨hNg,hNc,_,_⟩ := lemma_2_4_3_1 hG.evenCharacteristic hMe d.mem_gammaEvenZero d.full_pair d.S le_rfl
  have hNN : normalizer (twoCore d.H : Set G)=N := by rw [hcore]
  rw [hNN] at hNg hNc
  rw [hcore] at hNc
  have hCU : centralizer (U : Set G)=U := by
    apply le_antisymm
    · have hh := hNg.2
      change N ⊓ centralizer (twoCore N : Set G) ≤ twoCore N at hh
      rw [hNc] at hh
      exact (le_inf (Subgroup.centralizer_le_normalizer _) le_rfl).trans hh
    · let : IsElementaryAbelian 2 U := hcore ▸ (d.core_source hG T hST).2.2.2.1
      exact le_centralizer U
  refine ⟨hcore,hCU,?_⟩
  have hAi : IsAlternatingBlock d.block 5 := hA.of_mulEquiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  have hnot : ¬IsAlternatingBlock d.block 3 := by
    intro hh
    have hc := hAi.module_card_odd (by decide)
    rw [hh.module_card_odd (by decide)] at hc
    norm_num at hc
  have hNL : N≤normalizer (L : Set G) := by
    have hh := d.coreNormalizer_normalizes_L0_source_of_not_three hG T hM hTM hu hnot
    rwa [hNN,hsingle] at hh
  obtain ⟨q,e,hk,_,_⟩ := exists_action hA ((map_subtype_le _).trans hHN) hNL
  obtain ⟨qH,eH,hqH,hkH,_,_⟩ := d.single_alternating_marked_action hsingle hA
  have hcN : Nat.card q.ker=Nat.card U := by
    rw [hk,hCU,Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv]
  have hcH : Nat.card qH.ker=Nat.card U := by
    rw [hkH,hcorei,←card_map_of_injective d.H.subtype_injective,hUi]
  have hhH := qH.ker.index_mul_card
  rw [index_ker,MonoidHom.range_eq_top.mpr hqH,card_top,hcH] at hhH
  have hhN := q.ker.index_mul_card
  rw [index_ker,hcN] at hhN
  symm
  apply eq_of_le_of_card_ge hHN
  calc
    Nat.card N = Nat.card q.range * Nat.card U := hhN.symm
    _ ≤ Nat.card (Equiv.Perm (Fin 5)) * Nat.card U := Nat.mul_le_mul_right _ q.range.card_le_card_group
    _ = Nat.card d.H := hhH
end CFSG.Quasithin.Chapter2
