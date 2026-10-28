module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.CoreGeometry

/-!
# Central Sylow involutions and the inputs of 1.1.5

Source: Aschbacher–Smith, Lemmas 2.3.8(6) and 2.3.9(3), printed p.525.
Extend S to an ambient Sylow subgroup R. The β barrier keeps R inside M,
and characteristic two in M forces Z(R) into its two-core. The bound from
2.3.9(2) then puts Z(R) in S. Uniqueness of the maximal two-local puts the
centralizer of every M-central involution in M. These facts construct all
the actual hypotheses of 1.1.5, without any classification input.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H U L : Subgroup G}

/-- The uniqueness hypothesis controls every involution central in a Sylow of M. -/
theorem centralizer_le_of_M_central_involution (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    {z : G} (hz : orderOf z = 2) (P : Sylow 2 M)
    (hzP : ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x) :
    centralizer ({z} : Set G) ≤ M := by
  apply core_overgroup_le_of_sylow T hTM hunique
    (Chapter1.mem_H_of_isTwoLocal (Theory.GroupTheory.isTwoLocal_involution_centralizer hz)) P
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (hzP x hx)

/-- Lemma 2.3.9(3), with an ambient Sylow witness (and hence a Sylow of M). -/
theorem lemma_2_3_9_3 (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hM : M ∈ Chapter1.He G) (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    ∃ R : Sylow 2 G, (R : Subgroup G) ≤ M ∧
      (S : Subgroup H).map H.subtype < (R : Subgroup G) ∧
      (center (R : Subgroup G)).map (R : Subgroup G).subtype ≤
        (S : Subgroup H).map H.subtype ∧
      (center (R : Subgroup G)).map (R : Subgroup G).subtype ≤
        centralizer ((S : Subgroup H).map H.subtype : Set G) := by
  let A := (S : Subgroup H).map H.subtype
  obtain ⟨R, hAR⟩ := (S.isPGroup'.map H.subtype).exists_le_sylow
  have hAb := beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)
  have hRM : (R : Subgroup G) ≤ M := beta_overgroup_le hAb hAR R.isPGroup'
  have hQR : twoCore M ≤ (R : Subgroup G) := by
    simpa only [twoCore_eq_pCoreIn, Sylow.coe_subtype, map_subgroupOf_eq_of_le hRM]
      using pCoreIn_le_sylow M (R.subtype hRM)
  have hc : (center (R : Subgroup G)).map (R : Subgroup G).subtype ≤
      centralizer (R : Set G) := by
    rintro z ⟨a, ha, rfl⟩ x hx
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x, hx⟩)
  have hZQ : (center (R : Subgroup G)).map (R : Subgroup G).subtype ≤ twoCore M :=
    fun z hz => hM ⟨hRM (map_subtype_le _ hz), centralizer_le hQR (hc hz)⟩
  have hZA := (le_inf hZQ (hc.trans (centralizer_le
    ((pCoreIn_le_sylow H S).trans hAR)))) |>.trans (lemma_2_3_9_2 hH hpair S hUS)
  refine ⟨R, hRM, lt_of_le_of_ne hAR ?_, hZA, hc.trans (centralizer_le hAR)⟩
  intro he
  have hgam : H ∈ gamma (Chapter1.He G) M := hH.elim (fun h => h.1.1) (fun h => h.1)
  apply gamma_not_le hgam
  apply core_overgroup_le_of_sylow T hTM hunique hgam.1 (R.subtype hRM)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hRM, ← he]
  exact map_subtype_le _

/-- Lemma 2.3.8(6): construct every premise of 1.1.5 for the specified involution. -/
theorem lemma_2_3_8_6 {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ (S : Subgroup H).map H.subtype)
    (hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s)
    (hMcentral : ∃ P : Sylow 2 M,
      ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x) :
    Chapter1.Lemma115Hypotheses H S M z := by
  have hgam : H ∈ gamma (Chapter1.He G) M := hH.elim (fun h => h.1.1) (fun h => h.1)
  have hSM := (beta_mono hpair.1.1 hUS (S.isPGroup'.map H.subtype)).2.1
  obtain ⟨P, hP⟩ := hMcentral
  exact ⟨hgam.1, ⟨Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM),
    Chapter1.mem_H_of_isTwoLocal hM.1, hSM⟩,
    (gammaZero_intersection_core_centralizer hH hpair S hUS).trans (map_subtype_le _),
    hz, hzS, hcentral, centralizer_le_of_M_central_involution T hTM hunique hz P hP⟩

end CFSG.Quasithin.Chapter2
