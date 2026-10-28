module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Definitions
public import Theory.SpecificGroups.SU3.FixedCentralizerRigidity

/-!
# Rigidity of the second unitary centralizer action

The second centralizer is identified with an actual SU₃ or PSU₃ model by
`second_cover`. Its literal normalizer action is an outer involution by
`noninner` and the given ambient involution. Intrinsic model rigidity then
proves the precise input to `centralizerActor_eq_zpowers`, preserving both
commutation with the action and pointwise fixation of its fixed subgroup.

Source: GLS4, Chapter 2, Lemma 13.3, invoking Chapter 4, Lemma 3.4(d1).
No ambient generation or homocyclic placement premise is needed here.
-/

public section
namespace BenderSuzuki.ZD.UnitaryExclusion
open BenderSuzuki.MatrixGroups

/-- The intrinsic fixed-centralizer statement for either literal unitary cover. -/
theorem unitaryCover_fixedCentralizerRigidity
    {H : Type*} [Group H] {n : ℕ} (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n H)
    (a : MulAut H) (ha : a ^ 2 = 1) (houter : ¬ ∃ x, a = MulAut.conj x) :
    FixedCentralizerRigidity a := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hmodel⟩ := hcover
  change MulAut.FixedCentralizerRigid a
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    apply (MulAut.fixedCentralizerRigid_congr_iff e a).mp
    apply J.projective_outer_fixedCentralizerRigid hn hJ hcard hfixed (MulAut.congr e a)
    · rw [← map_pow, ha, map_one]
    · exact fun hi => houter ((MulAut.congr_inner_iff e a).mp hi)
  · obtain ⟨e⟩ := hmodel
    apply (MulAut.fixedCentralizerRigid_congr_iff e a).mp
    apply J.special_outer_fixedCentralizerRigid hn hJ hcard hfixed (MulAut.congr e a)
    · rw [← map_pow, ha, map_one]
    · exact fun hi => houter ((MulAut.congr_inner_iff e a).mp hi)

variable {G : Type*} [Group G]
    {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- The normalizer action used in the source has square one. -/
theorem secondInvolution_sq_eq_one (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) : secondInvolution d ^ 2 = 1 := by
  change (distinguishedCentralizer Z d.torus).normalizerMonoidHom ⟨u, d.normalizes⟩ ^ 2 = 1
  rw [← map_pow]
  have he : (⟨u, d.normalizes⟩ :
      Subgroup.normalizer (distinguishedCentralizer Z d.torus : Set G)) ^ 2 = 1 :=
    Subtype.ext hu.sq_eq_one
  rw [he, map_one]

/-- `noninner` is exactly noninnerness of the literal normalizer automorphism. -/
theorem secondInvolution_not_inner
    (d : SecondCentralizerData Z M z t u n) :
    ¬ ∃ x, secondInvolution d = MulAut.conj x := by
  rintro ⟨v, hv⟩
  apply d.noninner
  refine ⟨v, v.property, ?_⟩
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun hv ⟨x, hx⟩)

/-- Chapter 4, 3.4(d1), applied to the actual second-centralizer action in
Chapter 2, Lemma 13.3. All intrinsic model and central-cover premises are discharged. -/
theorem secondInvolution_fixedCentralizerRigidity (hn : 2 ≤ n)
    (hu : PFAppendixIII.IsInvolution u) (d : SecondCentralizerData Z M z t u n) :
    FixedCentralizerRigidity (secondInvolution d) :=
  unitaryCover_fixedCentralizerRigidity hn d.second_cover (secondInvolution d)
    (secondInvolution_sq_eq_one hu d) (secondInvolution_not_inner d)

end BenderSuzuki.ZD.UnitaryExclusion
