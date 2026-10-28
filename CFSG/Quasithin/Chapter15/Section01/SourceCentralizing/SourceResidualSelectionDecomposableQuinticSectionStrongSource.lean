module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreKernelPairing
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionStrong
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSectionReduced
public import Theory.Representation.BinaryConjugationSection.ReducedImage

/-!
# The original quintic module is a strong offender on the partner section

When the partner module has order four, either the original module lies in
the partner two-core or its own image is a strong offender on the literal F/Uc
section. The two original quintic supports supply the strict index comparison.
The faithful action and its exact kernel are then constructed, retaining
the original actor V and the original denominator Uc.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original module lies in the partner core, or its actual image is an
strong offender on the faithful action of the original partner section. -/
theorem PreparedChosenModule.decomposable_five_core_or_section_strong_offender
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
      Nat.card (localModule T Mc) = 4 →
      let Uc := localModule T Mc
      let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
      V ≤ Mc.pCoreIn 2 ∨
        ∃ he : IsElementaryAbelian 2 F,
          letI := he
          ∃ ρ : Representation (ZMod 2) Mc (Additive (F ⧸ Uc.subgroupOf F)),
            Nonempty (BinaryConjugationSection Mc F Uc ρ) ∧
            Function.Injective (Representation.BinaryOffender.imageRepresentation ρ) ∧
            (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype =
              commutatorPreimage Mc F Uc ∧
            Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) =
              (commutatorPreimage Mc F Uc).relIndex V ∧
            pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ ∧
            IsStrongOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  rcases h.decomposable_five_core_or_strict_section_indices
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU with
    hcore | hstrict
  · exact Or.inl hcore
  right
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let F := conjugateSpanBy E C
  have hUE : Uc ≤ E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le (hUE.trans inf_le_left))
  have hCMc : C ≤ Mc := localModule_centralizer_le_partner T Mc hu
  have hFMc : F ≤ Mc := (conjugateSpanBy_le_self (inf_le_left.trans hVC)).trans hCMc
  obtain ⟨_, _, _, heF, _, hnF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := heF
  obtain ⟨ρ, ⟨dF⟩, hfaith, hker, hcard, hoff⟩ :=
    DecomposableQuinticControl.exists_faithful_section_strong_offender_of_kernel_index
    Mc F Uc V hFMc (hUE.trans (le_conjugateSpanBy E C)) hnF
    (le_normalizer_conjugateSpanBy _ _) (hVC.trans hCMc)
    hstrict
  refine ⟨heF, ρ, ⟨dF⟩, hfaith, hker, hcard, ?_, hoff⟩
  let : (Uc.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy (centralInvolutions T) Mc)
  exact dF.actionImage_twoCore_eq_bot_of_reduced_image
    (QuotientGroup.mk' (Uc.subgroupOf Mc)) (QuotientGroup.ker_mk' _)
    (QuotientGroup.mk'_surjective _)
    (h.decomposable_five_partner_four_section_reduced
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU)

end CFSG.Quasithin.Chapter15.Section01
