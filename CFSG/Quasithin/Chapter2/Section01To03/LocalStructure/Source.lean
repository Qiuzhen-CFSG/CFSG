module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Components
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.IndexTwo
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.HalfSylow

/-!
# The selected central involution in the source local geometry

Source: Aschbacher–Smith 2.3.9(3,5–6), printed pp.525–526.
This assembles the Sylow witness of part (3) with the structural conclusions
for every involution in its center. Thus the centrality and membership
assumptions in the general earlier-source applications are all discharged.
The full structural family 2.3.8(4–6), 2.3.9(1–6,8), and 2.3.10 is exported;
C.1.29 and the structural clauses of 1.1.5 and 1.2.4 remain universal earlier
source inputs. Their producers must instantiate these inputs before the
unconditional chapter theorem is claimed.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U L : Subgroup G}

/-- Select the source T (called R here to distinguish the initial Sylow)
and obtain the 1.1.5 hypotheses for every involution in its center. -/
theorem exists_source_sylow_with_115 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    ∃ R : Sylow 2 G, (R : Subgroup G) ≤ M ∧
      (S : Subgroup H).map H.subtype < (R : Subgroup G) ∧
      (center (R : Subgroup G)).map (R : Subgroup G).subtype ≤ (S : Subgroup H).map H.subtype ∧
      ∀ z ∈ (center (R : Subgroup G)).map (R : Subgroup G).subtype, orderOf z = 2 →
        Chapter1.Lemma115Hypotheses H S M z := by
  obtain ⟨R, hRM, hSR, hZS, hZC⟩ := lemma_2_3_9_3 T hTM hunique
    (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)) hH hpair S hUS
  refine ⟨R, hRM, hSR, hZS, ?_⟩
  intro z hz hzi
  apply lemma_2_3_8_6 hG T hM hTM hunique hH hpair S hUS hzi (hZS hz)
    (fun s hs => hZC hz s hs)
  refine ⟨R.subtype hRM, ?_⟩
  intro r hr
  have hrR : r ∈ (R : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hRM] using hr
  obtain ⟨a, ha, rfl⟩ := hz
  exact congrArg Subtype.val (mem_center_iff.mp ha ⟨r, hrR⟩)

/-- Source 2.3.9(3,5–6) with every local involution premise discharged.
The only additional premises are the universal earlier-source implications. -/
theorem source_lemma_2_3_9_3_5_6 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (source115 : Structural115Input G) (source124 : Embedding124Input G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    ∃ R : Sylow 2 G, (R : Subgroup G) ≤ M ∧
      (S : Subgroup H).map H.subtype < (R : Subgroup G) ∧
      (center (R : Subgroup G)).map (R : Subgroup G).subtype ≤ (S : Subgroup H).map H.subtype ∧
      ∀ z ∈ (center (R : Subgroup G)).map (R : Subgroup G).subtype, orderOf z = 2 →
        centralizer ({z} : Set G) ≤ M ∧
        (∀ x ∈ (pPrimeCore 2 H).map H.subtype, z * x * z⁻¹ = x⁻¹) ∧
        ∀ B : Subgroup H, IsComponent H B →
          B.map H.subtype = ⁅B.map H.subtype, zpowers z⁆ ∧ ¬ B.map H.subtype ≤ M ∧
          ∃ D : Subgroup (normalizer (twoCore H : Set G)),
            IsComponent (normalizer (twoCore H : Set G)) D ∧
            B.map H.subtype ≤ D.map (normalizer (twoCore H : Set G)).subtype := by
  obtain ⟨R, hRM, hSR, hZS, h115⟩ := exists_source_sylow_with_115 hG T hM hTM hunique hH hpair S hUS
  refine ⟨R, hRM, hSR, hZS, ?_⟩
  intro z hz hzi
  have hh := h115 z hz hzi
  have hMc : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x := by
    refine ⟨R.subtype hRM, ?_⟩
    intro x hx
    have hxR : x ∈ (R : Subgroup G) := by
      simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hRM] using hx
    obtain ⟨a, ha, rfl⟩ := hz
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x, hxR⟩)
  exact ⟨hh.centralizer_le, (source115 H S M z hh).1,
    fun B hB => lemma_2_3_9_6_of_115_124 hG source115 source124 T hM hTM hunique
      hH hpair S hUS hzi hh.mem_sylow hh.central hMc B hB⟩

end CFSG.Quasithin.Chapter2
