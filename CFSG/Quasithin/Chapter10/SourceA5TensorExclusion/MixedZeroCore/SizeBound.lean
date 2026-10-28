module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.Assembly

/-!
# The mixed Borel size calculation in the original tensor consumer

Structural recognition supplies an actual model for the whole common Borel.
The Chapter F size calculation then supplies exactly `MixedSizeInput` and
feeds the original zero-core contradiction and tensor-line centralization.
The mixed recognition and the construction of the cubic factor remain
explicit independent inputs; this is conditional assembly. The local-order
and quotient theorems below apply the new local structure to the literal
source pair and identify the weighted two-core bounds still to be proved.

Source: Aschbacher--Smith, original 9.3.1, printed pp.732--733, using
F.1.12(I), printed pp.262--264 of refs/quasithin.pdf.
-/

public section
namespace CFSG.Quasithin.Chapter10
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Supply the literal size contract from the structural mixed recognition. -/
theorem MixedZeroCore.mixedSizeInput_of_borel_recognition
    (recognition : ChapterF.Source.MixedA5S3BorelRecognition G) :
    MixedZeroCore.MixedSizeInput G := by
  intro K U S h hqt hSyl hK hU _
  exact ChapterF.Source.mixed_a5_s3_sylow_card_le_of_borel_recognition
    recognition K U S h hqt hSyl hK hU

namespace SourceA5TensorModel
open Chapter3.Section02
open MixedZeroCore
variable {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Apply the local structure to the original H, BT and AT, keeping their literal inclusions. -/
theorem mixed_cubic_factor_local_orders
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    Nat.card (B ⊔ (T : Subgroup G) : Subgroup G) = 3 * Nat.card T ∧
    Nat.card H = 15 * Nat.card T ∧
    Nat.card (A ⊔ (T : Subgroup G) : Subgroup G) = 9 * Nat.card T ∧
    (Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) := by
  obtain ⟨hf, _, _, _, hb, hp, hq⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨eU⟩ := hU.2.2.2.2
  have hc := hf.mixed_local_orders eK eU
  rw [hb, hp, hq] at hc
  have he := hf.mixed_first_parabolic_quotient eK eU
  rw [hp] at he
  exact ⟨hc.1, hc.2.1, hc.2.2, he⟩

/-- The exact core-size obligation in the original mixed zero-core consumer.
This equivalence does not assert either of the two remaining bounds. -/
theorem mixed_cubic_factor_size_iff_core_bounds
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    Nat.card T ≤ 256 ↔
      ((pCore 2 H).index = 60 ∧ Nat.card (pCore 2 H) ≤ 64) ∨
      ((pCore 2 H).index = 120 ∧ Nat.card (pCore 2 H) ≤ 32) := by
  obtain ⟨hf, _, _, _, _, hp, _⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨eU⟩ := hU.2.2.2.2
  have hc := hf.mixed_first_core_size_cases eK eU
  rw [hp] at hc
  change ((pCore 2 H).index = 60 ∧ Nat.card T = 4 * Nat.card (pCore 2 H)) ∨
    ((pCore 2 H).index = 120 ∧ Nat.card T = 8 * Nat.card (pCore 2 H)) at hc
  rcases hc with ⟨hi, hs⟩ | ⟨hi, hs⟩ <;> rw [hi, hs] <;> omega

/-- DGS (15.1) on the original tensor pair: replace T by O₂(BT), keeping
the original residual and cubic factor and both original parabolic kernels.
This does not assert that O₂(BT) is Sylow in the smaller generated group. -/
theorem mixed_cubic_factor_reduced_pair
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    let R := (B ⊔ (T : Subgroup G)).pCoreIn 2
    let F := ![(pResidual 2 H).map H.subtype,U]
    ChapterF.Source.HypothesisF11 F R ∧
    IsQuasithin (ChapterF.Source.generated F R) ∧
    (ChapterF.Source.parabolic F R 0).pCoreIn 2 = H.pCoreIn 2 ∧
    (ChapterF.Source.parabolic F R 1).pCoreIn 2 = (A ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    (pCore 2 (ChapterF.Source.commonBorel F R)).index = 3 := by
  obtain ⟨hf, hqt, _, _, hb, hp, hq⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨eU⟩ := hU.2.2.2.2
  have hnew := hf.restrict_to_borel_core
  have hnewqt := hf.borel_core_generated_quasithin hqt
  have hleft := hf.borel_core_parabolic_same_core 0
  have hright := hf.borel_core_parabolic_same_core 1
  have hindex := hf.mixedReducedBorel_two_closed eK eU
  rw [← hf.mixed_reduced_commonBorel eU] at hindex
  rw [hb] at hnew hnewqt hleft hright hindex
  rw [hp] at hleft
  rw [hq] at hright
  exact ⟨hnew, hnewqt, hleft, hright, hindex⟩

/-- The exact extension factor and reduced Sylow order in the literal BT.
The outstanding source estimate is |O₂(BT)| ≤ 128. -/
theorem mixed_cubic_factor_borel_core_orders
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    let R := pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)
    (R.index = 3 ∨ R.index = 6) ∧
    Nat.card R = 4 * Nat.card (pCore 2 H) ∧
    (Nat.card T = Nat.card R ∨ Nat.card T = 2 * Nat.card R) := by
  obtain ⟨hf, _, _, _, hb, hp, _⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨eU⟩ := hU.2.2.2.2
  have hi := hf.mixed_borel_core_index eK eU
  have hc := hf.mixed_borel_core_card eK eU
  have hs := hf.mixed_sylow_card_borel_core_cases eK eU
  rw [hb] at hi hc hs
  rw [hp] at hc
  exact ⟨hi, hc, hs⟩

/-- The reduced pair inside the original tensor configuration has the same
outer index at both endpoints and at the Sylow inclusion. The entire reduced
completion is normal in H ∨ A, with index dividing that common factor. -/
theorem mixed_cubic_factor_reduced_extension
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    let R := (B ⊔ (T : Subgroup G)).pCoreIn 2
    let F := ![(pResidual 2 H).map H.subtype,U]
    let B₀ := ChapterF.Source.commonBorel F R
    let P₀ := ChapterF.Source.parabolic F R
    let M := ChapterF.Source.generated F R
    (∀ i, (T : Subgroup G) ⊓ P₀ i = R ∧ P₀ i ⊓ (B ⊔ (T : Subgroup G)) = B₀) ∧
    (P₀ 0).relIndex H = R.relIndex (T : Subgroup G) ∧
    (P₀ 1).relIndex (A ⊔ (T : Subgroup G)) = R.relIndex (T : Subgroup G) ∧
    R.relIndex (T : Subgroup G) ≤ 2 ∧
    H ⊔ A ≤ normalizer (M : Set G) ∧
    M.relIndex (H ⊔ A) ∣ R.relIndex (T : Subgroup G) := by
  obtain ⟨hf, _, _, _, hb, hp, hq⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨eU⟩ := hU.2.2.2.2
  have hi := hf.mixed_reduced_borel_index_eq_sylow_index eU
  have hleft := hf.mixed_reduced_parabolic_index eU 0
  have hright := hf.mixed_reduced_parabolic_index eU 1
  have hbound := hf.mixedReducedBorel_index_le_two eK eU
  have hnorm := hf.borel_core_generated_normalizes
  have hdiv := hf.mixed_reduced_generated_index_dvd eU
  have hgen : ChapterF.Source.generated ![(pResidual 2 H).map H.subtype,U]
      (T : Subgroup G) = H ⊔ A := by
    rw [← ChapterF.Source.parabolics_generate, hp, hq]
    exact le_antisymm
      (sup_le le_sup_left (sup_le le_sup_right
        ((show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_left)))
      (sup_le le_sup_left (le_sup_left.trans le_sup_right))
  rw [hi] at hleft hright hbound hdiv
  rw [hp] at hleft
  rw [hq] at hright
  rw [hgen] at hnorm hdiv
  rw [hb] at hleft hright hbound hnorm hdiv
  refine ⟨?_, hleft, hright, hbound, hnorm, hdiv⟩
  intro i
  have hs := hf.borel_core_parabolic_inf_S i
  have hbi := hf.borel_core_parabolic_inf_commonBorel i
  rw [hb] at hs hbi
  exact ⟨hs, hbi⟩


variable {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual original-source application of the numerical reduction.
Its two remaining source inputs have separate recognition and factor producers. -/
theorem old_residual_centralizes_tensorLine_of_mixed_borel_recognition
    (recognition : ChapterF.Source.MixedA5S3BorelRecognition G)
    (factor : m.MixedCubicFactorInput)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < ChapterE.generationParameter H) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  exact m.old_residual_centralizes_tensorLine_of_mixed_inputs
    (MixedZeroCore.mixedSizeInput_of_borel_recognition recognition) factor hH hlarge

end SourceA5TensorModel
end CFSG.Quasithin.Chapter10
