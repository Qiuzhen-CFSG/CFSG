module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.DGSProfiles
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.SizeBound

/-!
# DGS profile consequences in the original mixed tensor pair

Apply the exceptional index calculation, the regular irreducible-section
exclusion and the proved commuting-distance-one size theorem to the literal
pair constructed from H, A and the cubic factor U. The full Borel is BT and
the original Sylow remains T. These are branch applications: exhaustive
critical-distance selection is still needed for unconditional MixedSizeInput.

Source: Aschbacher--Smith, original 9.3.1, pp.732--733, using F.1.12(I);
DGS (10.7)--(10.10), pp.158--165, and (11.7), p.174.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Chapter3.Section02 MixedZeroCore
open ChapterF.Source.DGS85 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The exhaustive DGS profile implication supplies the exact original
`MixedSizeInput` contract.  All F.1.1 hypotheses and the literal A₅/S₃
quotient markings remain explicit at the consumer boundary. -/
theorem mixedSizeInput_of_dgs_profile_exhaustion
    {G : Type*} [Group G] [Finite G]
    (profiles : ChapterF.Source.MixedDGS.MixedDGSProfileExhaustive G) :
    MixedSizeInput G := by
  intro K U S h hqt hSyl hK hU hn
  exact ChapterF.Source.MixedDGS.mixed_a5_s3_sylow_card_le_of_dgs_profiles
    profiles K U S h hqt hSyl hK hU hn

/-- Feed the profile-derived size input into the original tensor-line
consumer, retaining the independent cubic-factor construction. -/
theorem old_residual_centralizes_tensorLine_of_dgs_profiles
    {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
    (m : SourceA5TensorModel D e)
    (profiles : ChapterF.Source.MixedDGS.MixedDGSProfileExhaustive G)
    (factor : m.MixedCubicFactorInput)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < ChapterE.generationParameter H) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  exact m.old_residual_centralizes_tensorLine_of_mixed_inputs
    (mixedSizeInput_of_dgs_profile_exhaustion profiles) factor hH hlarge

/-- The exceptional profile controls the literal BT and original T, with no recognition map. -/
theorem mixed_cubic_factor_exceptional_profile_size
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (profile : ChapterF.Source.MixedDGS.ExceptionalProfile
      ((pResidual 2 H).map H.subtype) U (T : Subgroup G)) :
    Nat.card (pCore 2 H) = 32 ∧
    Nat.card ((B ⊔ (T : Subgroup G)).pCoreIn 2) = 128 ∧
      (Nat.card T = 128 ∨ Nat.card T = 256) := by
  obtain ⟨hf, _, _, _, hb, hp, _⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨eU⟩ := hU.2.2.2.2
  have hs := ChapterF.Source.MixedDGS.exceptional_size _ _ _ hf eK eU profile
  have hq := ChapterF.Source.MixedDGS.exceptional_first_core_card _ _ _ hf eK eU profile
  rw [hb] at hs
  rw [hp] at hq
  exact ⟨hq,hs⟩

/-- The actual first reduced quotient excludes the regular source profile in this tensor pair. -/
theorem mixed_cubic_factor_regular_profile_excluded
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    let hf := (mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero).1
    ∀ _profile : ChapterF.Source.MixedDGS.RegularProfile
      ((pResidual 2 H).map H.subtype) U (T : Subgroup G) hf eK hU.2.2.2.2.some,
      False := by
  intro hf profile
  exact ChapterF.Source.MixedDGS.not_regular_profile _ _ _ hf eK hU.2.2.2.2.some profile

/-- The proved commuting distance-one profile supplies the stronger bound on the original T. -/
theorem mixed_cubic_factor_commuting_one_size
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (hc : let F := Reduction.reducedFamily ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)
      IsCriticalPair F (base F false) (base F true))
    (hb : b (Reduction.reducedFamily ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) = 1)
    (hcomm : let F := Reduction.reducedFamily ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)
      ⁅Z F (base F false),Z F (base F true)⁆ = ⊥) :
    Nat.card ((B ⊔ (T : Subgroup G)).pCoreIn 2) = 64 ∧
      (Nat.card T = 64 ∨ Nat.card T = 128) := by
  obtain ⟨hf, _, _, _, hB, _, _⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨eU⟩ := hU.2.2.2.2
  have hs := CommutingOneProfile.mixed_binary_graph_exact_row_size _ _ _ hf eK eU hc hb hcomm
  rw [hB] at hs
  exact hs

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
