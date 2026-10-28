module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Radical.Intersection
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Source

/-!
# Refined escape from a contrary radical-supplement overgroup

For any actual supplement B and an outside maximal two-local H≥BT,
the canonical comparison places Y=N_L(R)^∞ in B. Source 1.2.4 constructs
the containing normal C-component of H. The completed radical geometry
then discharges all canonical premises of the existing refined escape
construction, including faithfulness, the core and centralizer identities,
and the actual PSL₂(p) quotient.

Only canonical starred membership and the exact earlier 13.1.2 rigidity
and classification clauses remain explicit. Their final assembly owner
is qt-d-1317-source. The independent FF exclusion must still rule out
the resulting witness to prove supplement uniqueness.
Source: Aschbacher--Smith, 13.1.9, printed pp.869--870.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- A contrary overgroup of any actual radical supplement gives the refined source witness, with canonical geometry constructed. -/
theorem canonical_escape_for_supplement (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) (hrig : Escape.QuasisimpleRigidity T)
    (hclass : Escape.QuasisimpleClassification T)
    {L B H : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (hB : B ∈ radicalSupplements T L)
    (hH : IsMaximalTwoLocal H) (hBH : B ⊔ (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G)) :
    ∃ C Y : Subgroup G, C ∈ cComponentsIn H ∧
      canonicalSupplement T L ≤ C ∧ (C.subgroupOf H).Normal ∧
      Escape.RefinedWitness T L H C Y := by
  let A := canonicalSupplement (T : Subgroup G) L
  have hA := canonical_mem_faithfulLocalComponents h hmany hL hn
  have hg := canonical_supplement_comparison h hmany hL hn
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hBH
  have hAH : A ≤ H := (hg.2.2 B hB).2.2.1.trans (le_sup_left.trans hBH)
  have hTA := sylow_normalizes_canonicalSupplement
    (radicalLocal_invariant_source hL.1.1
      (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn)
  have haH : A.subgroupOf H ∈ Chapter1.L H (T.subtype hTH : Subgroup H) :=
    (mem_LIn_iff_subgroupOf hTH hAH).mp ⟨hAH,hg.1.1⟩
  have hnorm : (T.subtype hTH : Subgroup H) ≤ normalizer (A.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hAH]
    intro t ht
    exact hTA ht
  obtain ⟨C,⟨hC,hAC,hCN⟩,_⟩ := lemma_1_2_4_containment_normality_source
    (uniqueness_local_quotient_sqtk h.simpleQTKE (mem_H_of_isTwoLocal hH.1))
    (T.subtype hTH) haH hnorm
  let C₀ := C.map H.subtype
  have hm : C₀.subgroupOf H = C := comap_map_eq_self_of_injective H.subtype_injective C
  have hC₀ : C₀ ∈ cComponentsIn H := ⟨map_subtype_le _,hm.symm ▸ hC⟩
  have hAC₀ : A ≤ C₀ := by
    simpa only [map_subgroupOf_eq_of_le hAH] using map_mono (f := H.subtype) hAC
  have hcent : radicalSylowCentralizer T A = radicalSylowCentralizer T L :=
    supplement_radicalSylowCentralizer
      (radicalLocal_invariant_source hL.1.1
        (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn)
      hTA (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).1 hg.1.2
  obtain ⟨p,_,_,hmodel⟩ := canonical_twoCore_quotient h hmany hL hn
  obtain ⟨Y,hY⟩ := Escape.exists_refined_witness h hmany hs hrig hclass hL hn hH hTH hne
    hA hC₀ hAC₀ hTA hg.2.1 hcent hmodel
  exact ⟨C₀,Y,hC₀,hAC₀,hm.symm ▸ hCN,hY⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
