module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssemblyInputs
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion.CanonicalDescent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceImage

/-!
# The actual half-field tensor in Hermitian coordinates

The absolute tensor descends on the original representation through its given
central covering map. The same coordinates identify the component and put
the original faithful actor in a source overgroup with its exact residual.
For any larger faithful actor normalizing that marked component, conjugation
of operators embeds the entire actor in the literal Hermitian normalizer.
The inner image and the full-normalizer bound give its exact two-rank 4n.

The Chapter 12 consumer transports the full ambient automizer of the original
chosen orbit. These results supply the dimension and two-rank entries of
Table 7.2.1; they do not prove the global weak-closure or centralizer bounds.
Their assembly remains with qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith, 3.2.9(4), Table 7.2.1, H.4.4(6–7), and K.3.2,
printed pp.582–583, 698, 381, and 454–456 (refs/quasithin.pdf).
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

variable {A U : Type*} [Group A] [Finite A] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) A U} {Q : Subgroup A}

omit [Finite A] in
/-- Descent on the original action, retaining its central covering map. -/
theorem exists_component_coordinates (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (B : BinaryField) (C : LinearCover B 3 Q) (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible ρ C hs.irreducible
      schurDegree (inflated ρ C) = n)
    (hfield : B.degree = 2 * n)
    (hmodel : let := inflated_irreducible ρ C hs.irreducible
      HasAbsoluteTwistedModel (inflated ρ C) n) :
    ∃ d : ActionEquiv (ρ.comp Q.subtype) (overgroupAction n (binaryImage n)),
      ∃ a : Cover n ≃* SL(3,B.Carrier),
        ∀ g : Cover n, (d.groupEquiv (C.projection (a g))).val = binaryActionHom n g := by
  let := inflated_irreducible ρ C hs.irreducible
  obtain ⟨a, ⟨e⟩⟩ := TwistedExclusion.exists_binary_hermitian_equiv n (inflated ρ C)
    (by rw [B.card_eq, hfield]) hdegree hmodel
  let π := C.projection.comp a.toMonoidHom
  have hπ : Function.Surjective π := C.surjective.comp a.surjective
  let d := hermitianActionEquiv (ρ.comp Q.subtype) n π hπ
    (hs.faithful.comp Q.subtype_injective) e
  exact ⟨d, a, hermitianActionEquiv_cover (ρ.comp Q.subtype) n π hπ
    (hs.faithful.comp Q.subtype_injective) e⟩

omit [FiniteDimensional (ZMod 2) U] in
/-- The given quotient marking supplies the residual equation for the
original ambient action in these same coordinates. -/
theorem coordinates_are_source (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (B : BinaryField) (eQ : (Q ⧸ center Q) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (ρ.comp Q.subtype) (overgroupAction n (binaryImage n))) :
    SourceOvergroup n (sourceImage ρ Q n d) := by
  let : IsQuasisimple Q := hs.quasisimple
  let : Q.Normal := hs.layer_normal
  exact sourceImage_isSource ρ Q n d hs.fitting B eQ

omit [FiniteDimensional (ZMod 2) U] in
/-- In particular the source actor itself has the exact Hermitian two-rank. -/
theorem actor_rank (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (B : BinaryField) (eQ : (Q ⧸ center Q) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (ρ.comp Q.subtype) (overgroupAction n (binaryImage n))) :
    primeRank 2 A = 4 * n := by
  rw [primeRank_equiv 2 (sourceActionEquiv ρ Q n d hs.faithful).groupEquiv]
  exact ChapterH.Section01To04.HermitianTensor.ImageOuter.source_twoRank_eq n _
    (coordinates_are_source hs B eQ n d)

omit [Finite A] [FiniteDimensional (ZMod 2) U] in
/-- The dimension is proved from the actual intertwiner, independently of
any dimension clause supplied by the family sieve. -/
theorem coordinates_dimension (n : ℕ) [NeZero n]
    (d : ActionEquiv (ρ.comp Q.subtype) (overgroupAction n (binaryImage n))) :
    Module.finrank (ZMod 2) U = 9 * n :=
  d.linearEquiv.finrank_eq.trans (finrank_binary n)

/-- The genuine family row supplies the component intertwiner and the
residual equation, with degree one retained. -/
theorem exists_source_coordinates (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hrow : NonMathieuAssembly.HermitianRow hs) :
    ∃ n : ℕ, ∃ _hn : NeZero n,
      ∃ d : ActionEquiv (ρ.comp Q.subtype) (overgroupAction n (binaryImage n)),
        SourceOvergroup n (sourceImage ρ Q n d) := by
  obtain ⟨B, C, ⟨eQ⟩, hn, hfield, _, hmodel⟩ := hrow
  let := inflated_irreducible ρ C hs.irreducible
  let n := schurDegree (inflated ρ C)
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨d, _, _⟩ := exists_component_coordinates hs B C n rfl hfield hmodel
  exact ⟨n, inferInstance, d, coordinates_are_source hs B eQ n d⟩

section NormalRange
variable {H K W : Type*} [Group H] [Group K]
  [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) H W) (n : ℕ) [NeZero n]
  (i : K →* H) [i.range.Normal]
  (q : K →* binaryImage n) (hq : Function.Surjective q)
  (e : W ≃ₗ[ZMod 2] Space n)
  (he : ∀ k v, e (σ (i k) v) = overgroupAction n (binaryImage n) (q k) (e v))

include he in
omit [i.range.Normal] in
private theorem coordinate_component (k : K) :
    coordinateHom σ n e (i k) = (q k).val := by
  apply LinearEquiv.ext
  intro X
  rw [coordinateHom_apply, he, e.apply_symm_apply]
  rfl

include hq he in
omit [i.range.Normal] in
private theorem coordinate_range :
    i.range.map (coordinateHom σ n e) = binaryImage n := by
  ext x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [coordinate_component σ n i q e he]
    exact (q k).property
  · intro hx
    obtain ⟨k, hk⟩ := hq ⟨x, hx⟩
    refine ⟨i k, ⟨k, rfl⟩, ?_⟩
    rw [coordinate_component σ n i q e he, hk]

include hq he in
/-- Normality is relative to the actual larger actor. The resulting
embedding intertwines every element, not only the component. -/
theorem exists_normalizer_embedding (hσ : Function.Injective σ) :
    ∃ j : H →* binaryNormalizer n, Function.Injective j ∧
      (∀ g v, e (σ g v) = overgroupAction n (binaryNormalizer n) (j g) (e v)) ∧
      (∀ k, (j (i k)).val = (q k).val) := by
  have hn (g : H) : coordinateHom σ n e g ∈ binaryNormalizer n := by
    change coordinateHom σ n e g ∈ normalizer (binaryImage n : Set _)
    rw [← coordinate_range σ n i q hq e he]
    exact i.range.le_normalizer_map (coordinateHom σ n e)
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j := (coordinateHom σ n e).codRestrict (binaryNormalizer n) hn
  refine ⟨j, ?_, ?_, ?_⟩
  · intro x y hxy
    exact coordinateHom_injective σ n hσ e (congrArg Subtype.val hxy)
  · intro g v
    change e (σ g v) = e (σ g (e.symm (e v)))
    rw [e.symm_apply_apply]
  · exact coordinate_component σ n i q e he

include hq he in
/-- The original larger actor contains the marked image and embeds in its
normalizer, so its two-rank is exactly 4n. -/
theorem rank_of_marked_normal_range [Finite H] (hσ : Function.Injective σ) :
    primeRank 2 H = 4 * n := by
  obtain ⟨j, hj, _, _⟩ := exists_normalizer_embedding σ n i q hq e he hσ
  apply le_antisymm
  · exact (primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n)
        ⟨FieldSections.centralizerEquiv n⟩)
  · have hcomponent : primeRank 2 i.range = 4 * n := by
      rw [primeRank_equiv 2 (i.range.equivMapOfInjective (coordinateHom σ n e)
        (coordinateHom_injective σ n hσ e)), coordinate_range σ n i q hq e he]
      exact OuterRank.binaryImage_twoRank n
    rw [← hcomponent]
    exact primeRank_le_of_injective 2 i.range.subtype i.range.subtype_injective
end NormalRange
end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
