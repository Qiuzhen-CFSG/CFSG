module
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneSetup
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneRank
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOneExclusions

/-!
# Marked rank-one models and automizer ranks on the chosen orbit

The unitary and Suzuki quotient witnesses give natural models on the unchanged
orbit representation. Unitary recognition uses the proved covering lift; the
Suzuki group equivalence retains the specified central-quotient map. Binary
coordinates then intertwine the original L-conjugation action on the literal
subgroup W. The Sylow in the faithful actor is explicitly the image of the
original T, and both families' omega and fixed-space calculations use it.

The full automizer has two-rank at most s+1 in the unitary row and 2m+1 in
the Suzuki row. The imported ambient setup supplies E.6.1. The global w/r
bounds and the two source exclusions remain to be proved in this theorem
family; none is asserted by these local calculations.

The private `import all` is an intentional internal continuation of Actor.Orbit,
used to prove the conjugation formula for its unexposed `orbitComponentHom`.
It changes neither that definition nor its public visibility.
Source: Aschbacher--Smith, K.3.3, K.3.6, 7.2.1 and 7.5.2,
printed pp.456--457,698,700, applied in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full ambient automizer is bounded by the full linear normalizer of
the literal component action, through the original subgroup coordinates. -/
theorem sourceOrbit_automizer_rank_le_normalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    primeRank 2 (ChapterE.Automizer D.sourceOrbit) ≤
      primeRank 2 (linearNormalizer (D.orbitRepresentation.comp D.orbitComponent.subtype)) := by
  apply Chapter7.NormalizedSource.automizer_rank_le_marked_normalizer
    D.sourceOrbit L D.sourceOrbit_component_normalizes (D.sourceOrbit_normalizer_le h)
    (D.orbitRepresentation.comp D.orbitComponent.subtype)
    D.orbitComponentHom D.orbitComponentHom_surjective D.sourceOrbitCoordinates
  intro l v
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [sourceOrbitCoordinates_apply]
  rfl

/-- The actual automizer bound in the unitary row of Table 7.2.1. -/
theorem sourceOrbit_unitary_automizer_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s)) :
    primeRank 2 (ChapterE.Automizer D.sourceOrbit) ≤ s + 1 :=
  (D.sourceOrbit_automizer_rank_le_normalizer h.toHypothesis1221).trans
    (Chapter7.NormalizedSource.unitary_normalizer_rank hs hs2 hq)

/-- The actual automizer bound in the Suzuki row of Table 7.2.1. -/
theorem sourceOrbit_suzuki_automizer_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    primeRank 2 (ChapterE.Automizer D.sourceOrbit) ≤ 2 * m + 1 :=
  (D.sourceOrbit_automizer_rank_le_normalizer h.toHypothesis1221).trans
    (Chapter7.NormalizedSource.suzuki_normalizer_rank hs hm e)

/-- The Sylow in the faithful orbit actor is the image of the original T. -/
def sourceOrbitSylow : Sylow 2 D.orbitActor :=
  (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).mapSurjective
    D.orbitHom_surjective

/-- The image Sylow retains the literal restriction of the original T to LT. -/
theorem sourceOrbitSylow_coe :
    (D.sourceOrbitSylow : Subgroup D.orbitActor) =
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map D.orbitHom := by
  rfl

omit [Finite G] in
/-- The chosen coordinates intertwine the original L conjugation action
with its specified surjection onto the orbit component. -/
theorem sourceOrbitCoordinates_component_intertwines (l : L) (v : D.orbitSpace) :
    D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitComponentHom l) v) =
      ChapterE.automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) (D.sourceOrbitCoordinates v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change _ = (l : G) * ((D.sourceOrbitCoordinates v).toMul : G) * (l : G)⁻¹
  simp only [sourceOrbitCoordinates_apply]
  rfl

omit [Finite G] in
/-- Natural unitary coordinates on the literal subgroup, with the original
component homomorphism rather than an arbitrary equivalent actor. -/
theorem sourceOrbit_unitary_coordinates_intertwine
    {F : Type*} [Field F] [Algebra (ZMod 2) F] {J : HermitianForm 3 F}
    (M : ChapterK.RankOne.UnitaryModel J D.orbitRepresentation D.orbitComponent)
    (l : L) (v : Additive D.sourceOrbit) :
    (D.sourceOrbitCoordinates.symm.trans M.coordinates)
      (ChapterE.automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) v) =
      Matrix.mulVec (M.groupEquiv (D.orbitComponentHom l)).val.val
        ((D.sourceOrbitCoordinates.symm.trans M.coordinates) v) := by
  have ht := D.sourceOrbitCoordinates_component_intertwines l (D.sourceOrbitCoordinates.symm v)
  simp only [LinearEquiv.apply_symm_apply] at ht
  have hu := congrArg D.sourceOrbitCoordinates.symm ht
  simp only [LinearEquiv.symm_apply_apply] at hu
  change M.coordinates (D.sourceOrbitCoordinates.symm _) =
    Matrix.mulVec _ (M.coordinates (D.sourceOrbitCoordinates.symm v))
  exact (congrArg M.coordinates hu.symm).trans
    (M.intertwines (D.orbitComponentHom l) (D.sourceOrbitCoordinates.symm v))

omit [Finite G] in
/-- The same literal conjugation marking for the natural Suzuki coordinates. -/
theorem sourceOrbit_suzuki_coordinates_intertwine {m : ℕ}
    (M : ChapterK.RankOne.SuzukiModel m D.orbitRepresentation D.orbitComponent)
    (l : L) (v : Additive D.sourceOrbit) :
    (D.sourceOrbitCoordinates.symm.trans M.coordinates)
      (ChapterE.automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) v) =
      Matrix.mulVec (M.groupEquiv (D.orbitComponentHom l)).val.val
        ((D.sourceOrbitCoordinates.symm.trans M.coordinates) v) := by
  have ht := D.sourceOrbitCoordinates_component_intertwines l (D.sourceOrbitCoordinates.symm v)
  simp only [LinearEquiv.apply_symm_apply] at ht
  have hu := congrArg D.sourceOrbitCoordinates.symm ht
  simp only [LinearEquiv.symm_apply_apply] at hu
  change M.coordinates (D.sourceOrbitCoordinates.symm _) =
    Matrix.mulVec _ (M.coordinates (D.sourceOrbitCoordinates.symm v))
  exact (congrArg M.coordinates hu.symm).trans
    (M.intertwines (D.orbitComponentHom l) (D.sourceOrbitCoordinates.symm v))

/-- The unitary natural action is recognized on the original orbit. Its
coordinates retain every component element, including the possible cubic center. -/
theorem sourceOrbit_unitary_model
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra (ZMod 2) F)
        (J : HermitianForm 3 F),
      Nat.card F = (2 ^ s) ^ 2 ∧ (∀ x : F, J.conj x = x ^ (2 ^ s)) ∧
      Nonempty (ChapterK.RankOne.UnitaryModel J D.orbitRepresentation D.orbitComponent) ∧
      Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 6 * s := by
  have hc := hs.unitary_case_of_cover_lifting hs2 hq
    (fun F _ _ J hcard hconj e =>
      ChapterB.SourceClassification.unitary_central_quotient hs J hs2 hcard hconj e)
    D.sourceOrbitSylow
  obtain ⟨⟨F, hF, hfin, halg, J, hcard, hconj, hfixed, ⟨M⟩, houter⟩, hrest⟩ := hc
  refine ⟨F, hF, hfin, halg, J, hcard, hconj, ⟨M⟩, ?_⟩
  rw [← D.sourceOrbitCoordinates.finrank_eq]
  exact M.finrank_eq hcard

/-- The Suzuki coordinates use the given central-quotient map on every
component element; the dimension is on the literal subgroup orbit. -/
theorem sourceOrbit_suzuki_model
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    ∃ M : ChapterK.RankOne.SuzukiModel m D.orbitRepresentation D.orbitComponent,
      (∀ q : D.orbitComponent, M.groupEquiv q = e (QuotientGroup.mk q)) ∧
      Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 4 * (2 * m + 1) := by
  refine ⟨hs.suzukiModel hm e, hs.suzukiModel_groupEquiv_apply hm e, ?_⟩
  rw [← D.sourceOrbitCoordinates.finrank_eq]
  exact (hs.suzukiModel hm e).finrank_eq

/-- The unitary omega and fixed-space calculations use the image of the
original T and its literal intersection with the orbit component. -/
theorem sourceOrbit_unitary_sylow_parameters
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s)) :
    let A := omegaOneAmbient
      ((D.sourceOrbitSylow : Subgroup D.orbitActor) ⊓ D.orbitComponent)
    IsElementaryTwo A ∧ rank A = s ∧
      Module.finrank (ZMod 2) (fixedSpace D.orbitRepresentation A) = 4 * s ∧
      quadraticRatio D.orbitRepresentation = 2 ∧ cubicRatio D.orbitRepresentation = 2 := by
  have hc := hs.unitary_case_of_cover_lifting hs2 hq
    (fun F _ _ J hcard hconj e =>
      ChapterB.SourceClassification.unitary_central_quotient hs J hs2 hcard hconj e)
    D.sourceOrbitSylow
  obtain ⟨_, _, hquad, hcubic, _, helem, hrank, hfixed, _⟩ := hc
  exact ⟨helem, hrank, hfixed, hquad, hcubic⟩

/-- The Suzuki omega and fixed-space calculations are on the faithful image
of the original T; the image subgroup is specified by `sourceOrbitSylow_coe`. -/
theorem sourceOrbit_suzuki_sylow_parameters
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    (D.sourceOrbitSylow : Subgroup D.orbitActor) ≤ D.orbitComponent ∧
      IsElementaryTwo (omegaOneAmbient (D.sourceOrbitSylow : Subgroup D.orbitActor)) ∧
      rank (omegaOneAmbient (D.sourceOrbitSylow : Subgroup D.orbitActor)) = 2 * m + 1 ∧
      Module.finrank (ZMod 2) (fixedSpace D.orbitRepresentation
        (omegaOneAmbient (D.sourceOrbitSylow : Subgroup D.orbitActor))) = 2 * (2 * m + 1) ∧
      quadraticRatio D.orbitRepresentation = 2 ∧ cubicRatio D.orbitRepresentation = 2 := by
  obtain ⟨_, _, hT, helem, hrank, _, hfixed, _, _, _, hquad, hcubic, _⟩ :=
    hs.suzuki_case_of_quotient hm e D.sourceOrbitSylow
  exact ⟨hT, helem, hrank, hfixed, hquad, hcubic⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
