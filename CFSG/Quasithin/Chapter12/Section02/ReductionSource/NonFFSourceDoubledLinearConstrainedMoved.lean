module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearConstrainedModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearResidualPair
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourModule
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedFixedModule
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorMoved
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# The original nonbinary pair inside the actual constrained moved module

Literal residual placement and W=[W,LH] put the complete original orbit
inside the K-moved star module. The inclusion retains its original ambient
elements and is injective; the complete B.5.1 source conclusion uses this
same moved section and its full central kernel. No replacement module or
parabolic marking is introduced.
Source: Aschbacher--Smith C.4.5--8 and 7.3.4, printed pp.152--154,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The whole original orbit lies in the literal K-moved star subgroup. -/
theorem sourceOrbit_linear_witness_constrained_moved_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let Kg := K.map H.subtype
    let R := J.pCoreIn 2
    D.sourceOrbit ≤ (⁅starV Kg R,Kg.subgroupOf (Kg ⊔ R)⁆).map (Kg ⊔ R).subtype := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_linear_witness_hypothesisC28 h hd F hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan := hc.normalized_span_eq hn
  obtain ⟨_,hLK⟩ := D.sourceOrbit_linear_witness_constrained_placement
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hLKg : LH ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) hLK
    rwa [map_subgroupOf_eq_of_le hLH] at hh
  have hcomm : D.sourceOrbit = ⁅D.sourceOrbit,LH⁆ := by
    simpa only [hspan] using hc.module_commutator
  dsimp only
  rw [map_commutator,map_subgroupOf_eq_of_le (show K.map H.subtype ≤ K.map H.subtype ⊔ J.pCoreIn 2
    from le_sup_left),hcomm]
  exact commutator_mono (hc.constrained_module_le_starV K hK hq hout hfK) hLKg

/-- B.5.1 on the actual star module contains the complete original orbit
inside its literal moved space, by the inclusion of original ambient elements. -/
theorem sourceOrbit_linear_witness_constrained_classified_embedding
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let ρ := starRepresentation (K.map H.subtype) (J.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    ∃ _hCO : C ≤ O,
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp O.subtype) (C.subgroupOf O),
      ∃ i : Additive D.sourceOrbit →ₗ[ZMod 2] c.sectionData.space.toSubmodule,
        (∀ v, (((i v).val.toMul : ((K.map H.subtype) ⊔ (J.pCoreIn 2) : Subgroup G)) : G) = v.toMul) ∧
        Function.Injective i := by
  let Kg := K.map H.subtype
  let R := J.pCoreIn 2
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_linear_witness_hypothesisC28 h hd F hmodel hw hWJ hJC
  obtain ⟨_,hLK⟩ := D.sourceOrbit_linear_witness_constrained_placement
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hLKg : LH ≤ Kg := by
    have hh := map_mono (f := H.subtype) hLK
    rwa [map_subgroupOf_eq_of_le hLH] at hh
  obtain ⟨f,hf,hfambient,_⟩ :=
    constrained_module_star_fixed_embedding hc K hK hq hout hfK (le_refl D.sourceOrbit)
  obtain ⟨hCO,⟨c⟩⟩ := ChapterC.C27Source.star_moved_section_from_source
    (hc.constrained_source_input K hK hq hout hfK)
  have hs : c.sectionData.space.toSubmodule =
      NormalElementaryQuotient.commutatorSpace (starV Kg R) (Kg.subgroupOf (Kg ⊔ R)) := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (starV Kg R)
      (QuotientGroup.mk' (starKernel Kg R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _),c.sectionData.space_eq]
    change subspaceCommutator _ ⊤ _ = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCO]
    rfl
  have hm : f.range ≤ c.sectionData.space.toSubmodule := by
    rw [hs]
    rintro _ ⟨v,rfl⟩
    have hv := D.sourceOrbit_linear_witness_constrained_moved_placement
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK v.toMul.property
    obtain ⟨w,hw,hwe⟩ := hv
    have he : w = (f v).toMul.val := Subtype.ext ((hwe.trans (hfambient v).symm))
    change (f v).toMul.val ∈ ⁅starV Kg R,Kg.subgroupOf (Kg ⊔ R)⁆
    exact he ▸ hw
  let i := f.codRestrict c.sectionData.space.toSubmodule (fun v => hm ⟨v,rfl⟩)
  refine ⟨hCO,c,i,hfambient,?_⟩
  intro v w he
  exact hf (congrArg Subtype.val he)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
