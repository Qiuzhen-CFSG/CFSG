module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl

/-!
# Normalizers above the original A₅ orbit intersection

The literal Hypothesis 13.3.1 and original A₅ quotient construct the
Fundamental Setup before component normalization. In the nonnormal branch,
every T-invariant subgroup above T ∩ L₀ has its ambient normalizer in
N_G(L₀). In particular this holds for the original stabilizer N_T(L).

This supplies the early common-normal step of 10.2.1 at its original
13.3.2 consumer. Neither the equality of the full and local modules nor a
normalized-component choice is needed.
Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), printed pp.742–743,884–885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Common-normal control above the original Sylow-orbit intersection,
with all relative Sylow and minimal-parabolic premises discharged. -/
theorem normalizer_le_of_orbit_intersection_le
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hT0 : (T : Subgroup G) ⊓ localOrbit T L ≤ R) :
    normalizer (R : Set G) ≤ normalizer (localOrbit T L : Set G) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_normalizer_le_of_orbit_intersection_le D e hn R hRT hR hT0

/-- The original stabilizer T₁=N_T(L) has its full ambient normalizer in M. -/
theorem sylow_stabilizer_normalizer_le
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (localOrbit T L : Set G) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_sylow_stabilizer_normalizer_le D e hn

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
