module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaSource

/-!
# Original escaping omega points with ambient-local earlier inputs

The six-letter weight orbits supply a Sylow-fixed representative of the
escaping vector from 12.2.13 at the same G,T,L,V. An outside maximal
two-local over its centralizer then gives the genuine Chapter 3
Thompson-generation theorem. Both central-cover rows are retained.
OmegaIndexAt uses this movement to split the full omega-center.
Source: Aschbacher--Smith 13.3.5(3), 13.4.3(1), pp.886,897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the nonfixed escaping omega point from the preceding centralizer-escape theorem. -/
theorem exists_nonfixed_omega_escape_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T) :
    ∃ z : V, z ≠ 1 ∧ z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
      z.val ∉ centralizer (L : Set G) ∧
      ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v,hv,_,hvL,hout⟩ := exists_nonfixed_escape_at h structural D m h₀ earlier
  obtain ⟨z,hzT,hzL,hweight⟩ := omega_representative_of_nonfixed D m
    (normalizer_component_le_module_at h structural D m) ⟨v,hv⟩ hvL
  refine ⟨z,?_,hzT,hzL,?_⟩
  · intro he
    exact hzL ((m.fixed_iff z).mpr (Or.inl he))
  · intro hc
    exact hout ((m.centralizer_le_iff_of_weight_eq z ⟨v,hv⟩ hweight).mp hc)

/-- Original 13.4.3(1), with its outside-local and centralizer-control premises discharged. -/
theorem original_core_thompson_generation_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T) :
    ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ = L := by
  obtain ⟨z,hz1,hzT,_,hout⟩ := exists_nonfixed_omega_escape_at h₀ h structural D m earlier
  have hz1' : z.val ≠ 1 := fun he => hz1 (Subtype.ext he)
  have htwo := isTwoLocal_involution_centralizer
    (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1')
  obtain ⟨H,hCH,hH⟩ := Finite.exists_le_maximal htwo
  have hTH : (T : Subgroup G) ≤ H := by
    apply le_trans ?_ hCH
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.2 t ht)
  have hmax : Chapter3.HasMaximalOutside T (normalizer (L : Set G)) :=
    Chapter3.hasMaximalOutside_of_two_distinct
      (h.source_normalizer_maximal_unique_at structural
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
      hH D.sylow_normalizes_component hTH (fun he => hout (hCH.trans_eq he))
  have hf : V ⊓ centralizer (L : Set G) ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    intro a ha
    apply (CoreMarking.mem_omega_iff (D := D) ⟨a,ha.1⟩).mpr
    apply mem_centralizer_iff.mpr
    intro t ht
    exact (mem_centralizer_iff.mp
      (normalizer_component_le_fixed_centralizer_at h structural D m
        (D.sylow_normalizes_component ht)) a ha).symm
  exact Chapter3.Section02.source_component_thompson_generation h.simpleQTKE T L
    h.maximal_faithful.1 h.maximal_faithful.2 h.quasisimple D.sylow_normalizes_component
    hmax ((centralizer_le hf).trans (fixed_centralizer_eq_normalizer_at h structural D m).le)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
