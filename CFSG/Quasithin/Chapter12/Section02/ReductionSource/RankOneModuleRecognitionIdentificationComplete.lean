module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictConclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityComplete

/-!
# Identification from the original natural reduction and H-star centralization

The strict-intersection contradiction supplies equality for the same involution,
sourceClosure and whole reduced commutator layer used by the equality recognition.
The latter constructs the marked symmetric-five quotient and extraspecial core
inside the original involution centralizer and identifies G with M₂₂.

For the Chapter 12 application, the original 6.1.5 H-star centralization and an
outside H-star member give omega-centralizer escape. The completed 6.2.1--12
construction then supplies the involution and every field of LocalAnalysis.
The many-overgroups application constructs the outside member, and the SmallExit
application removes the identification callback from the source assembly.

These are conditional source implications: 6.1.5 and Conclusion6127 remain
explicit inputs, owned by qt-d-1222-rankone-recognition-natural. The final owner
qt-d-1222-rankone-recognition must discharge both before claiming unconditional
SmallExit. No intersection equality or recognition conclusion is assumed.

Source: Aschbacher--Smith, 6.1.5, 6.2.1--19 and 12.2.2(3d), printed
pp.666--669, 679--691 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- Compose the strict exclusion and equality recognition on the same original
involution centralizer. Only the earlier local analysis remains explicit. -/
theorem reduced_m22_of_local_analysis
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) :=
  reduced_m22_of_local_analysis_of_equality A h611 hnatural hz ho hT
    (reduced_sourceClosure_intersection_eq_ZS h611 hnatural A hz ho hT)

/-- Construct the original involution and LocalAnalysis from omega-centralizer
escape, then identify G. This retains precisely the independent 6.1.5 input. -/
theorem m22_of_source_natural_reduction_of_omega_escape
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (homega : ¬ centralizer (centralOmega (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  obtain ⟨z, hz, ho, hT, A⟩ :=
    source_exists_local_analysis_of_omega_escape D h h611 hnatural homega
  exact reduced_m22_of_local_analysis A h611 hnatural hz ho hT

/-- The specialized 6.2.19 implication from the original 6.1.5 statement.
An actual outside H-star member forces the omega-centralizer to escape M. -/
theorem m22_of_source_natural_reduction_of_hstar_centralization
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (h615 : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  apply m22_of_source_natural_reduction_of_omega_escape D h h611 hnatural
  have he : centralOmega (T : Subgroup G) =
      Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    rw [centralOmega, ← map_center_subtype_eq_inf_centralizer,
      ← omegaCenterIn_eq_omegaOneAmbient]
    rfl
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  rw [he]
  exact fun hc => hH.1.2 ((h615 H hH).trans hc)

/-- The literal Chapter 12 identification with the earlier 6.1.5 statement
explicit. The many-overgroups hypothesis constructs HasMaximalOutside. -/
theorem m22_of_source_natural_reduction_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (h615 : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) :=
  m22_of_source_natural_reduction_of_hstar_centralization D h
    (D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany) h611 hnatural h615

/-- Apply the proved identification to the original SmallExit consumer.
The final rank-one owner supplies 6.1.27 and 6.1.5 on this same whole reduced
subgroup; no local-analysis, intersection or recognition callback remains. -/
theorem smallExit_of_source_natural_reduction_and_hstar_centralization_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hnatural : Chapter3.HasMaximalOutside T (normalizer (L : Set G)) →
      Hypothesis611 KnownSimple.IsKnownSimple T L
        (normalizer (L : Set G)) (wholeReduced T L) n →
      Conclusion6127 (T : Subgroup G) L
        (normalizer (L : Set G)) (wholeReduced T L) n)
    (h615 : Chapter3.HasMaximalOutside T (normalizer (L : Set G)) →
      Hypothesis611 KnownSimple.IsKnownSimple T L
        (normalizer (L : Set G)) (wholeReduced T L) n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    SmallExit T L := by
  apply smallExit_of_source_reduction_and_recognition_of_many D h hmany hn hpsl hnatural
  intro hout h611 hnat
  exact m22_of_source_natural_reduction_of_hstar_centralization D h hout h611 hnat
    (h615 hout h611)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
