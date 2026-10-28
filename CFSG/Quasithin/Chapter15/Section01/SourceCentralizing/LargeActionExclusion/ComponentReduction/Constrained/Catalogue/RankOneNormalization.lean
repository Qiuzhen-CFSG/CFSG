module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.Radical
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.FullSylowBlocks
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Genuine rank-one blocks or radical normalization

The full-Sylow alternative in C.2.4 now yields an actual chi-zero block.
The component cannot be the solvable A3 block, so only the natural L2-even
and alternating-five blocks remain. Every other constrained component is
normalized by the literal Q1, giving the C.2.7 input without a separate
full-Sylow exclusion or a model assumption on an unidentified quotient.

Both original pre-exclusion and exchanged applications retain the fixed
G1, MZ, S and Q1. The original prime is unrestricted and both exchanged
plane sizes remain available. Rank-one Borel identification and the remaining
field, block and parabolic clauses stay with the catalogue owner; quotient
assembly stays with qt-e-1515-constrained-linear-quotient.

Source: Aschbacher--Smith C.2.4(1--2), p.144, and 15.1.20(2), pp.1094--1095.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source ChapterC.CatalogueFullSylow
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- C.2.4(1) removes the unclassified full-Sylow branch on the fixed original
centralizer. The sole alternative to actual radical normalization is a
genuine rank-one block on the same component. -/
theorem constrained_component_rankOne_or_normalizes_of_radical_control
    (d : CaseIComponentData T M Mc V) (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hodd : pPrimeCore 2 d.G1 = ⊥)
    (hQne : d.Q1 ≠ ⊥)
    (hcontrol : d.Q1.characteristicNormalizerClosure ≤ Mc)
    (hnormalizer : d.G1 ⊓ normalizer (d.Q1 : Set G) = d.MZ)
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (B ⧸ pCore 2 B))
    (hfit : generalizedFitting B = pCore 2 B) (hout : ¬ B ≤ d.MZ) :
    ((∃ n : ℕ, IsL2EvenBlock B n) ∨ IsAlternatingBlock B 5) ∨
      d.Q1 ≤ normalizer (B : Set G) := by
  rcases d.constrained_component_sylow_or_normalizes_of_radical_control h hG
    hodd hQne hcontrol hnormalizer hB hq hfit with ⟨P,hP⟩ | hn
  · left
    let := h.elementary
    let K := B.subgroupOf d.G1
    let R := d.Q1.subgroupOf d.G1
    let N := d.MZ.subgroupOf d.G1
    let e : K ≃* B := subgroupOfEquivOfLe hB.1
    let := hq
    let hqK : IsQuasisimple (K ⧸ pCore 2 K) :=
      IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
    have hf : generalizedFitting K = pCore 2 K := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_generalizedFitting_equiv,pCore_map_iso,hfit]
    have hQG := d.Q1_le_MZ.trans (show d.MZ ≤ d.G1 from inf_le_left)
    let P0 : Sylow 2 K := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hP0 : (P0 : Subgroup K).map K.subtype ≤ R := by
      rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
      exact (hP ▸ mem_map_of_mem B.subtype hy).1
    have hb : IsChiZeroBlock B :=
      (@constrained_component_chiZero_of_full_sylow d.G1 inferInstance inferInstance
        (caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
          ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)))
        R N K
        (caseI_intrinsic_core_radical d.G1 d.MZ inf_le_left hQne hnormalizer)
        (caseI_intrinsic_characteristic_control d.G1 Mc d.Q1 hQG hcontrol)
        hB.2 hqK hodd hf
        (fun hh => hout (fun b hb => hh (show (⟨b,hB.1 hb⟩ : d.G1) ∈ K from hb)))
        P0 hP0).of_mulEquiv e
    rcases hb with hb | hb | hb
    · exact Or.inl hb
    · obtain ⟨f⟩ := hb.equiv_alternatingFour
      let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
      let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
      exact (hB.2.not_isSolvable
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    · exact Or.inr hb
  · exact Or.inr hn

theorem PreExclusionSource.constrained_rankOne_or_normalizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∨
      d.Q1 ≤ normalizer (d.L : Set G) :=
  d.constrained_component_rankOne_or_normalizes_of_radical_control h hG
    s.odd_core s.core_nontrivial s.characteristic_control s.core_normalizer
    d.L_component s.quasisimple hfit d.L_not_le_MZ

theorem ExchangedSource.constrained_rankOne_or_normalizes
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∨
      d.Q1 ≤ normalizer (d.L : Set G) :=
  d.constrained_component_rankOne_or_normalizes_of_radical_control h hG
    s.odd_core s.core_nontrivial s.characteristic_control s.core_normalizer
    d.L_component s.quasisimple hfit d.L_not_le_MZ

theorem PreExclusionSource.constrained_input_of_not_rankOne
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hn : ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5)) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L :=
  s.constrained_input_of_normalizes (h := h) hG hfit
    ((s.constrained_rankOne_or_normalizes (h := h) hG hfit).resolve_left hn)

theorem ExchangedSource.constrained_input_of_not_rankOne
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hn : ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5)) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L :=
  s.constrained_input_of_normalizes hG h hfit
    ((s.constrained_rankOne_or_normalizes hG h hfit).resolve_left hn)
/-- The original component now has a rank-one block or the literal C.2.7
star catalogue. The full-Sylow case is no longer an unclassified premise. -/
theorem PreExclusionSource.constrained_star_catalogue_or_rankOne
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  rcases s.constrained_rankOne_or_normalizes (h := h) hG hfit with hb | hn
  · exact Or.inl hb
  · exact Or.inr ⟨hn,s.constrained_star_catalogue_of_normalizes (h := h) hG hfit hn⟩

/-- Both exchanged-plane sizes use the same original rank-one alternative
and the same core-to-star map in every remaining branch. -/
theorem ExchangedSource.constrained_star_catalogue_or_rankOne
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  rcases s.constrained_rankOne_or_normalizes hG h hfit with hb | hn
  · exact Or.inl hb
  · exact Or.inr ⟨hn,s.constrained_star_catalogue_of_normalizes hG h hfit hn⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
