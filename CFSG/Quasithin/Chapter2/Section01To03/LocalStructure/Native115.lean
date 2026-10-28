module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Adequate
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs

/-!
# The structural 1.1.5 input to the original local geometry

The original marked-involution hypotheses imply odd-core inversion and
construct the component action, its commutator equality and noncontainment.
The commutator equality itself gives normalization. Thus the structural
input to 2.3.9 is unconditional and independent of the later model list.
The actual source application supplies the selected Sylow and central
involution; the core-normalizer component embedding uses the adequate A.3
boundary, whose earlier producer remains `qt-1-02-adequate-assembly`.

Source: Aschbacher--Smith 1.1.5(2--3) and 2.3.9(5--6), pp.501--503, 526.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The structural source implication needs no classification premise. -/
theorem structural115Input : Structural115Input G := by
  intro H S M z h
  constructor
  · rintro x ⟨y, hy, rfl⟩
    exact h.inverts_oddCore y hy
  · intro B hB
    obtain ⟨hout, α, P, ha, hd, hcomm⟩ := h.component_inputs B hB
    refine ⟨hcomm, hout, ?_⟩
    exact (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) (mem_zpowers z)

/-- Source 2.3.9(5) with its universal structural input discharged. -/
theorem lemma_2_3_9_5_source {C : GroupClass.{u}} (hG : IsSimpleQTKE C G)
    {M H U L : Subgroup G}
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ (S : Subgroup H).map H.subtype)
    (hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s)
    (hMcentral : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x) :
    centralizer ({z} : Set G) ≤ M ∧
      ∀ x ∈ (pPrimeCore 2 H).map H.subtype, z * x * z⁻¹ = x⁻¹ :=
  lemma_2_3_9_5_of_115 hG structural115Input T hM hTM hunique hH hpair S hUS
    hz hzS hcentral hMcentral

/-- Source 2.3.9(6) on the actual component and core normalizer, retaining
only the genuine earlier A.3 input to the adequate embedding theorem. -/
theorem lemma_2_3_9_6_source
    (earlier : Chapter1.Section02.Adequate.A3EarlierResults KnownSimple.IsKnownSimple.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {M H U L : Subgroup G}
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, L) ∈ localPairsIn (Chapter1.He G) M H)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {z : G} (hz : orderOf z = 2) (hzS : z ∈ (S : Subgroup H).map H.subtype)
    (hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s)
    (hMcentral : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x)
    (B : Subgroup H) (hB : IsComponent H B) :
    B.map H.subtype = ⁅B.map H.subtype, zpowers z⁆ ∧ ¬ B.map H.subtype ≤ M ∧
      ∃ D : Subgroup (normalizer (twoCore H : Set G)),
        IsComponent (normalizer (twoCore H : Set G)) D ∧
        B.map H.subtype ≤ D.map (normalizer (twoCore H : Set G)).subtype :=
  lemma_2_3_9_6_of_adequate earlier hG structural115Input
    T hM hTM hunique hH hpair S hUS hz hzS hcentral hMcentral B hB

end CFSG.Quasithin.Chapter2
