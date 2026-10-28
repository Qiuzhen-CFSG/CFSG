module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Parabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.MinimalParabolicSource

/-!
# The original linear-two exclusion

Characteristic exclusion from the original15.3.29 supplies the exact
minimal-parabolic chi-zero orbit theorem. Its factors form the residual
block product consumed by the marked Borel argument. The genuine invariant
four-group rules out the alternating-five block; the natural linear-two
block forces the component into the first-plane normalizer, a contradiction.

Source: Aschbacher–Smith15.3.30, pp.1131–1132; C.1.26, p.132.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06
open RankOneConfiguration
variable {G : Type*} [Group G] [Finite G]

/-- All local inputs of the marked block calculation follow from the
original component and plane producers. -/
theorem source_linearTwo_earlier
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) : LinearTwo.Earlier d I c := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hline := source_lineData hG d hempty hM hu hmany hshadow hI
  exact {
    component_normal := source_lemma_15_3_27_1 hG d hempty hM hu hmany hshadow hI hf c
    contains := source_lemma_15_3_27_2 hG d hempty hM hu hmany hshadow hI hf c
    theta_eq := hline.theta_eq
    normalizer_eq := hline.normalizer_eq
    plane_eq := hline.plane_eq
    plane_full := hline.plane_full
    plane_le_span := hline.plane_le_span
    span_elementary := d.UI_elementary h11.sylow
      (d.Z_le_S (d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le))) hf }

/-- The actual characteristic-exclusion theorem constructs the entire
residual block product; no universal pushing-up premise remains. -/
theorem source_residualBlockProduct
    {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hf : generalizedFitting H = pCore 2 H)
    (P : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver P ⊤)
    (hno : ∀ A : Subgroup P, A.Characteristic → A ≠ ⊥ →
      ¬ (A.map (P : Subgroup H).subtype).Normal) :
    Nonempty (LinearTwo.PushingUp.ResidualBlockProduct H P) := by
  obtain ⟨F,hF,hblocks,hgen,hcomm,hinv,htrans,hmove⟩ :=
    ChapterC.RankOne.ChiProduct.residual_chiZero_orbit_of_characteristic_exclusion hH hf P hP hno
  exact ⟨⟨F,hF,hblocks,hgen,hcomm,hinv,htrans,hmove⟩⟩

/-- Original15.3.30 for the literal marked Borel from15.3.28. -/
theorem source_lemma_15_3_30
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
    (b : LinearTwo.BorelIdentification d I c n F) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI.1
  obtain ⟨P,hP⟩ := h11.sylow
  have h := source_linearTwo_earlier hG d hempty hM hu hmany hshadow hI.1 hf c
  obtain ⟨hpush,hnorm,hVY⟩ := source_lemma_15_3_29 hG d hempty hM hu hmany hshadow hI.1
  have hpar := LinearTwo.PushingUp.Geometry.minimalParabolic_I b h hI P hP h11.centralizer_le
  obtain ⟨product⟩ := source_residualBlockProduct (OutsideStructure.outside_sqtk hG d hI.1) hf
    P hpar (LinearTwo.PushingUp.characteristic_exclusion_transport P hP hpush)
  have hblocks := (LinearTwo.PushingUp.block_recognition d h hI P hP product).2
  rcases hblocks with ⟨m,hblock⟩ | hblock
  · have hres := (source_lemma_15_3_26_1 hG d hempty hM hu hmany hshadow hI.1).residual
    have hVL : d.V₁ ≤ centralizer (c.L : Set G) :=
      (le_inf (LinearTwo.plane_one_le_sylow d) hVY).trans
        (LinearTwo.sylow_centralizer_yplus_le_component b h P hP hblock hres)
    exact c.outside ((le_centralizer_iff.mp hVL).trans
      ((Subgroup.centralizer_le_normalizer _).trans hnorm))
  · exact LinearTwo.AlternatingFive.not_isAlternatingBlock b h P hP hblock

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
