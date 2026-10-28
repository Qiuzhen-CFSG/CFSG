module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoMaximalSection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreKernelSectionIndices
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionOffender
public import Theory.Representation.BinaryConjugationSection.ReducedImage

/-!
# An actual faithful offender above the maximal centralizing denominator

The normal core of F intersect C_G(V) supplies the same original denominator
D and the same Sylow-central numerator H. The two quintic supports give the
section-index comparison for V. Conjugation coordinates then construct the
faithful core-free action on this literal H/D, with the original V-image as
an offender. No partner cardinality or quotient Thompson premise is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The canonical maximal centralizing denominator yields an actual
faithful, core-free section action with the original V-image as offender. -/
theorem PreparedChosenModule.decomposable_five_core_or_maximal_section_offender
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D₀ := ((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore
      let D := D₀.map Mc.subtype
      let W := F ⊓ commutatorPreimage (T : Subgroup G) (T : Subgroup G) D
      let H := conjugateSpanBy W Mc
      V ≤ Mc.pCoreIn 2 ∨
        (D < W ∧ D < F ∧ D ≤ centralizer (V : Set G) ∧
          Mc ≤ normalizer (D : Set G) ∧ D ≤ H ∧ H ≤ F ∧
          Mc ≤ normalizer (H : Set G) ∧
          ∃ he : IsElementaryAbelian 2 H,
            letI := he
            ∃ ρ : Representation (ZMod 2) Mc (Additive (H ⧸ D.subgroupOf H)),
              Nonempty (BinaryConjugationSection Mc H D ρ) ∧
              Function.Injective (Representation.BinaryOffender.imageRepresentation ρ) ∧
              (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype =
                commutatorPreimage Mc H D ∧
              Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) =
                (commutatorPreimage Mc H D).relIndex V ∧
              pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ ∧
              IsOffender (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D₀ := ((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore
  let D := D₀.map Mc.subtype
  let W := F ⊓ commutatorPreimage (T : Subgroup G) (T : Subgroup G) D
  let H := conjugateSpanBy W Mc
  rcases h.decomposable_five_core_or_maximal_reduced_section
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with
    hcore | ⟨hDW, hDF, hDC, hnD, hDH, hHF, hnH, heH, hnoncentral, hred⟩
  · exact Or.inl hcore
  right
  obtain ⟨_, hne, hi⟩ := h.decomposable_five_normal_section_indices
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
    H D hDH hHF hDF hnD hnoncentral
  have hUE : localModule T Mc ≤ E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le (hUE.trans inf_le_left))
  have hCMc : C ≤ Mc := localModule_centralizer_le_partner T Mc hu
  have hFMc : F ≤ Mc := (conjugateSpanBy_le_self (inf_le_left.trans hVC)).trans hCMc
  let : IsElementaryAbelian 2 H := heH
  obtain ⟨ρ, ⟨dH⟩, hfaith, hker, hcard, hoff⟩ :=
    DecomposableQuinticControl.exists_faithful_section_offender_of_kernel_index
      Mc H D V (hHF.trans hFMc) hDH hnH hnD (hVC.trans hCMc) hne hi
  refine ⟨hDW, hDF, hDC, hnD, hDH, hHF, hnH, heH, ρ,
    ⟨dH⟩, hfaith, hker, hcard, ?_, hoff⟩
  have hD₀eq : D.subgroupOf Mc = D₀ := by
    ext a
    constructor
    · rintro ⟨x, hx, he⟩
      exact Mc.subtype_injective he ▸ hx
    · intro ha
      exact mem_map_of_mem Mc.subtype ha
  exact dH.actionImage_twoCore_eq_bot_of_reduced_image
    (QuotientGroup.mk' D₀) ((QuotientGroup.ker_mk' D₀).trans hD₀eq.symm)
    (QuotientGroup.mk'_surjective D₀) hred

end CFSG.Quasithin.Chapter15.Section01
