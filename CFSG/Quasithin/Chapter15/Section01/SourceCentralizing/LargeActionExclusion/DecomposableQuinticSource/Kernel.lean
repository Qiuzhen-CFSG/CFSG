module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Span
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.SectionThreeComplement

/-!
# The actual quintic section kernel and its cubic obstruction

The original section H/E now exists for every partner-module size. Its
literal kernel centralizes E and normalizes V, placing it in the original
intersection M and C_G(E). Original H-star chief actions show that the
centralizer image on this same section has no normal three-complement.
The internal import reuses that general chief-action proof without changing
its frozen predecessor or exporting its private helper.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original centralizer image on H/E has no normal three-complement,
with its unchanged kernel lying inside M and centralizing E. -/
theorem PreparedChosenModule.decomposable_five_section_kernel_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      let H := conjugateSpanBy V (centralizer (E : Set G))
      let K := (commutatorPreimage Mc H E).subgroupOf Mc
      commutatorPreimage Mc H E ≤ M ⊓ centralizer (E : Set G) ∧
      ∃ hK : K.Normal, letI := hK
        ¬ HasNormalPComplement 3
          (((centralizer (E : Set G)).subgroupOf Mc).map (QuotientGroup.mk' K)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let E := thompsonFixed T V
  let C := centralizer (E : Set G)
  let H := conjugateSpanBy V C
  let K := (commutatorPreimage Mc H E).subgroupOf Mc
  obtain ⟨_,hNE,_,hMcH,_⟩ := h.decomposable_five_span_section
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive
  have hMcE : Mc ≤ normalizer (E : Set G) := hNE.ge
  have hVH : V ≤ H := le_conjugateSpanBy V C
  have hKE := h.decomposable_five_section_kernel_centralizes
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive
    H hVH hMcE
  have hKM : commutatorPreimage Mc H E ≤ M := by
    apply le_trans ?_ (hM.1.1.2
      ⟨V,h.nontrivial,IsElementaryAbelian.isPGroup 2 V,rfl⟩ h.normalized)
    apply le_normalizer_iff_commutator_le_right.mpr
    exact ((commutator_mono le_rfl hVH).trans
      (commutator_commutatorPreimage_le Mc H E hMcE)).trans inf_le_left
  have hn : K.Normal := normal_subgroupOf_of_le_normalizer
    (commutatorPreimage_normalized Mc H E Mc hMcE Mc.le_normalizer hMcH hMcE)
  let := hn
  refine ⟨le_inf hKM hKE,hn,?_⟩
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hMcC.1,hTMc⟩
  have he : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left
  have hJE : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (E : Set G) :=
    hJ.trans (centralizer_le (inf_le_left.trans h.le_local))
  exact source_section_centralizer_not_complement hG T hempty hM hJ h hMc hne.symm
    hVH hMcH hMcE he hJE hKE (QuotientGroup.mk' K) (QuotientGroup.ker_mk' K)

end CFSG.Quasithin.Chapter15.Section01
