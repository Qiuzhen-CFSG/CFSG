module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.ElementaryCover
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CompleteCover

/-!
# The full-W ordinary contradiction with native coverage discharged

The completed Kleidman--Wilson cover places the whole normalizer of every
nonzero elementary subgroup in four actual embedded locals. Its second row
is the original ATLAS subgroup; the certified conjugator identifies that row
with the first involution centralizer. Its third row is the full normalizer
of the native F, equal to M_F, whose intrinsic two-core quotient is SL5(2),
and hence PSL5(2) by the canonical projective map.

These literal identifications discharge every native premise of ElementaryCover.
That argument applies the cover above the full normalizer of the actual
projected radical, then excludes all four rows using the original C.2.8
action. The full W and covering residual B are retained. In particular the
ordinary odd-normalizer consumer uses its own B=(L intersect H)^infinity;
there is no shortness, W=V, order-64 or full-Sylow assumption.

Source: Kleidman--Wilson (1988), Section 2, pp.488--493 and p.509;
Aschbacher--Smith C.3.5, pp.150--151, and 4.2.13/4.4.3, pp.611--612,622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
open WeakClosure.Generation
open Janko4.LocalStructure.LinearFive (M_F M_F_eq_fullNormalizer M_F_intrinsicQuotient)
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem source_conjugate_eq_first (g : Janko4.Model) :
    sourceSubgroup.map (MulAut.conj g).toMonoidHom =
      Janko4.InvolutionCentralizers.First.centralizer.map
        (MulAut.conj (g * h)).toMonoidHom := by
  rw [Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.firstCentralizer_eq_source_conjugate,
    map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The independently proved native cover, with its literal max2 conjugator
and embedded linear-five local. No source-geometry or symmetry input remains. -/
theorem native_janko_elementaryNormalizerCover : JankoElementaryNormalizerCover M_F := by
  intro E hE hEE
  let := hEE
  obtain ⟨i,g,hg⟩ :=
    Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.elementary_normalizer_cover_unconditional
      E hE
  fin_cases i
  · exact Or.inl ⟨g,hg⟩
  · refine Or.inr (Or.inl ⟨g * h,?_⟩)
    change normalizer (E : Set Janko4.Model) ≤
      sourceSubgroup.map (MulAut.conj g).toMonoidHom at hg
    rwa [source_conjugate_eq_first] at hg
  · refine Or.inr (Or.inr (Or.inl ⟨g,?_⟩))
    rw [M_F_eq_fullNormalizer]
    exact hg
  · exact Or.inr (Or.inr (Or.inr ⟨g,hg⟩))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual J4 C.2.8 configuration is impossible, with the full radical
normalizer covered and every native premise discharged. -/
theorem c28_covering_jankoFour_false
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) : False :=
  c28_covering_jankoFour_false_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S h hstrict hn hBL hc hVB e he K hK ek

/-- The shared ordinary full-W exclusion, including both surviving component
models, on the original covering residual and inclusion-compatible quotient. -/
theorem c28_covering_ordinary_false
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K) : False :=
  c28_covering_ordinary_false_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S h hstrict hn hBL hc hVB e he K hK

/-- The ordinary odd-normalizer source case is excluded with its own covering
residual and full module. Its assembly owner retains the separate moved case. -/
theorem no_pushingUpFieldFourCase
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput) (A : Subgroup G) :
    ¬ OddNormalizer.PushingUpFieldFourCase D S A :=
  no_pushingUpFieldFourCase_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S A

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
