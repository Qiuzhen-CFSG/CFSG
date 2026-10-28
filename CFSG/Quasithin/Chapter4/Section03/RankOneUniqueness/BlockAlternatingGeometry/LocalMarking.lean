module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.LocalFive
public import Theory.Representation.BinaryPermutation.SevenParabolic.Reindex
public import Theory.SpecificGroups.Alternating.SevenFivePlacement.Centralizer

/-!
# Simultaneous marking of the source A₅ and radical

The source section-centralizer condition makes R centralize the A₅ image.
Its image is nontrivial and the five-letter centralizer is exactly the
transposition on the two fixed letters. Relabelling the whole-module chart
therefore marks both literal subgroup images at once.
Source: Aschbacher--Smith C.4.1(1), C.4.6 and 4.3.7, pp.151--152,616.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem radical_image_centralizes (c : SourceConfiguration T L)
    (f : (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) →*
      Equiv.Perm (Fin 7))
    (hkL : (f.comp (inclusion (c.le_component.trans le_sup_left))).ker = pCore 2 L) :
    ((c.I.pCoreIn 2).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f ≤
        centralizer (((L.subgroupOf
          (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f) : Set _) := by
  have hspan : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  obtain ⟨S,hS⟩ := c.c28.section_sylow
  have hR0 : c.I.pCoreIn 2 ≤ ChapterA.Section04.twoSectionCentralizer
      (conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)))
      (c.H ⊓ normalizer (L : Set G)) := by
    rw [← hS]
    exact map_subtype_le _
  have hR : c.I.pCoreIn 2 ≤ ChapterA.Section04.twoSectionCentralizer
      L (c.H ⊓ normalizer (L : Set G)) := by simpa only [hspan] using hR0
  have hc := (ChapterA.Section04.le_twoSectionCentralizer_iff _ _ _).mp hR |>.2.2
  rintro _ ⟨r,hr,rfl⟩ _ ⟨l,hl,rfl⟩
  obtain ⟨q,hq,hqq⟩ := hc (commutator_mem_commutator hl hr)
  have hqf : f (inclusion (c.le_component.trans le_sup_left) q) = 1 := by
    change q ∈ (f.comp (inclusion (c.le_component.trans le_sup_left))).ker
    rwa [hkL]
  have he : inclusion (c.le_component.trans le_sup_left) q = ⁅l,r⁆ := Subtype.ext hqq
  rw [he,map_commutatorElement] at hqf
  exact commutatorElement_eq_one_iff_mul_comm.mp hqf

private theorem eq_swap_group_of_nontrivial {B : Subgroup (Equiv.Perm (Fin 7))}
    (hne : B ≠ ⊥) (hle : B ≤ zpowers (Equiv.swap (0 : Fin 7) 1)) :
    B = zpowers (Equiv.swap (0 : Fin 7) 1) := by
  obtain ⟨x,hx,hx1⟩ := B.bot_or_exists_ne_one.resolve_left hne
  have ht := hle hx
  rw [mem_zpowers_iff_mem_range_orderOf,
    (show orderOf (Equiv.swap (0 : Fin 7) 1) = 2 from
      orderOf_eq_prime (by decide +kernel) (by decide +kernel))] at ht
  have he : x = Equiv.swap (0 : Fin 7) 1 := by
    have hh : x = 1 ∨ x = Equiv.swap (0 : Fin 7) 1 := by
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
      have ha2 := Finset.mem_range.mp ha
      interval_cases a <;> simp_all
    exact hh.resolve_left hx1
  exact le_antisymm hle (zpowers_le.mpr (he ▸ hx))

/-- The action and the original L and R admit simultaneous standard markings.
This supplies the chart, kernel, transposition and five-image fields of the
local-coordinate contract without assuming any of them. -/
theorem SourceConfiguration.exists_alternating_marked_chart
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (halt : ChapterC.IsAlternatingBlock c.K 7) :
    ∃ d : BinaryPermutation.SevenParabolic.Ordinary.Chart
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)) (c.K.map c.H.subtype)
      ((ChapterC.blockU (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype),
      d.actor.ker = pCore 2
        (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) ∧
      ((c.I.pCoreIn 2).subgroupOf
        (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map d.actor =
          zpowers (Equiv.swap (0 : Fin 7) 1) ∧
      (L.subgroupOf (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map d.actor =
        (fixingSubgroup (alternatingGroup (Fin 7)) ({0,1} : Set (Fin 7))).map
          (alternatingGroup (Fin 7)).subtype := by
  obtain ⟨d,hker,_⟩ := c.exists_alternating_join_chart halt
  obtain ⟨_,i,j,hij,hfive⟩ := c.alternating_five_placement D hpsl d.actor hker d.component_image
  have hpair : Function.Injective (![i,j] : Fin 2 → Fin 7) := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  have hstandard : Function.Injective (![0,1] : Fin 2 → Fin 7) := by decide
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair ![i,j] ![0,1] hpair hstandard
  have hσi : σ i = 0 := hσ 0
  have hσj : σ j = 1 := hσ 1
  let d' := d.reindex σ
  have hker' : d'.actor.ker = pCore 2
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) :=
    (d.reindex_ker σ).trans hker
  have hfive' : (L.subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map d'.actor =
      (fixingSubgroup (alternatingGroup (Fin 7)) ({0,1} : Set (Fin 7))).map
        (alternatingGroup (Fin 7)).subtype := by
    change (L.subgroupOf (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map
      ((MulAut.conj σ).toMonoidHom.comp d.actor) = _
    rw [← map_map,hfive,Theory.SpecificGroups.Alternating.SevenFivePlacement.map_fixer_pair,hσi,hσj]
  have hkL := (c.alternating_five_placement D hpsl d'.actor hker' d'.component_image).1
  have hcentral := radical_image_centralizes c d'.actor hkL
  rw [hfive',Theory.SpecificGroups.Alternating.SevenFivePlacement.centralizer_standard_five] at hcentral
  exact ⟨d',hker',eq_swap_group_of_nontrivial
    (c.alternating_radical_image_ne_bot d'.actor hker') hcentral,hfive'⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
