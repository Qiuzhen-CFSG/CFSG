module
public import CFSG.Quasithin.ChapterC.Section05.CommonNormalSource.CompleteKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThreeParameter
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThree

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwoSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.OddThreeSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.ClassicalCoverSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SmallFiniteSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AuxiliaryKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalNormalizerKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalTheoremKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalFullSpanKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeFullSpanKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.CommonNormalSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.OddLinearSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.BenderSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceModelsKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.BinaryLinearSource
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleSpan
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.G6CompleteSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.CubicBlockNormal
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.JankoExclusion
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.FittingPairSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceShort
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalComponent
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EnlargedControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeFullSpan
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.AlternatingTheorem
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalTheorem
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.JankoInvolutionSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.AlternatingOriginalControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalOriginalControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.PrimeSourceControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.JankoFourInvolutionSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceImageNormal
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.CoreCentralizing
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NormalImage
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FullSpan
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource

public import Theory.GroupTheory.CommonNormalSubgroup

/-!
# Finding a common normal subgroup

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §C.5, printed pp.154–163.

The original C.5.8 common-normal conclusion is assembled over the complete
known-simple catalogue in `theorem_C_5_8_knownSimple`. Every auxiliary and
larger-span embedding case used by the source is proved. The original C.5.1 and simple QTKE hypotheses
are unchanged; all block, module, Sylow and conjugator data are constructed.
The general commutator and conjugate-pair arguments are re-exported from
`Theory.GroupTheory.CommonNormalSubgroup`.

The lemma below proves the Frattini case in the proof of C.5.12 (p.163):
C_N(V) centralizes U ≤ V, so its Sylow normalizer controls the action of N
on U. This elementary case remains available independently of the source
assembly.
-/

namespace CFSG.Quasithin.ChapterC.Section05

open Subgroup

/-- The centralizing case of the normalizer-control reduction in C.5.12.
In the source application N = N_X(T₁), U = U₁ and the Sylow image is P₁. -/
public theorem normalizer_control_of_centralizing_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N U V : Subgroup G) (hUV : U ≤ V)
    (hNV : N ≤ normalizer (V : Set G))
    (P : Sylow p (N ⊓ centralizer (V : Set G) : Subgroup G))
    (hcontrol : N ⊓ normalizer
      ((P : Subgroup (N ⊓ centralizer (V : Set G) : Subgroup G)).map
        (N ⊓ centralizer (V : Set G)).subtype : Set G) ≤
      normalizer (U : Set G)) : N ≤ normalizer (U : Set G) := by
  have hcentralizer : normalizer (V : Set G) ≤
      normalizer (centralizer (V : Set G) : Set G) :=
    le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (V : Set G))
  have hNC : N ≤ normalizer ((N ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
    (le_inf N.le_normalizer (hNV.trans hcentralizer)).trans
      inf_normalizer_le_normalizer_inf
  exact le_normalizer_of_sylow_normalizer_le
    (N ⊓ centralizer (V : Set G)) N U inf_le_left hNC
    (inf_le_right.trans (centralizer_le hUV)) P hcontrol

end CFSG.Quasithin.ChapterC.Section05
