module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixConstrainedPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixResidualPair
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourModule
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedFixedModule
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorMoved
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# The original A₆ eight-space in the actual constrained moved section

Literal residual placement puts the complete original orbit in the K-moved
star module. Its residual fixed subgroup is trivial, so the original orbit
also embeds after the full central projection. Both embeddings are fixed by
the actual radical image. The complete B.5.1 source conclusion and original
ambient inclusion are retained; no standard module marking is substituted.

Source: Aschbacher--Smith C.4.5--8 and 7.3.4, printed pp.152--154,699,
refs/quasithin.pdf.
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
theorem sourceOrbit_six_witness_constrained_moved_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
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
  have hc := D.sourceOrbit_six_witness_hypothesisC28 h hd hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan := hc.normalized_span_eq hn
  obtain ⟨_,hLK⟩ := D.sourceOrbit_six_witness_constrained_placement
    h hd hmodel hw hWJ hJC K hK hq hout hfK
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

private theorem quotient_injective
    {E Y Z : Type*} [Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) (f : Z →ₗ[ZMod 2] Y) (hf : Function.Injective f)
    (hm : f.range ≤ s.space.toSubmodule) (hd : Disjoint f.range (fixedSpace ρ C)) :
    Function.Injective (s.central.toSubmodule.mkQ.comp
      (f.codRestrict s.space.toSubmodule (fun v => hm ⟨v,rfl⟩))) := by
  let i := f.codRestrict s.space.toSubmodule (fun v => hm ⟨v,rfl⟩)
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  change s.central.toSubmodule.mkQ (i v) = 0 at hv
  have hc : i v ∈ s.central.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hv
  rw [s.central_eq] at hc
  have hc' : f v ∈ fixedSpace ρ C := fun x => congrArg Subtype.val (hc x)
  have hz : f v = 0 := Submodule.disjoint_def.mp hd (f v) ⟨v,rfl⟩ hc'
  exact hf (hz.trans f.map_zero.symm)

/-- An embedding of a eight-space in a moved section which survives the full
central projection, fixed by the specified radical in both modules. -/
@[expose] def EightSpaceMovedEmbedding
    {E Y Z : Type*} [Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) (A : Subgroup E)
    (i : Z →ₗ[ZMod 2] s.space.toSubmodule) : Prop :=
  Function.Injective i ∧
  i.range ≤ fixedSpace s.space.toRepresentation A ∧
  Function.Injective (s.central.toSubmodule.mkQ.comp i) ∧
  (s.central.toSubmodule.mkQ.comp i).range ≤
    fixedSpace s.central.quotientRepresentation A ∧
  8 ≤ Module.finrank (ZMod 2) s.space.toSubmodule ∧
  8 ≤ Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule)

/-- B.5.1 on the actual star module contains the original orbit even after
its literal central projection, with the original radical-fixed embedding. -/
theorem sourceOrbit_six_witness_constrained_classified_embedding
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
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
        EightSpaceMovedEmbedding c.sectionData
          ((starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2)).subgroupOf O) i := by
  let Kg := K.map H.subtype
  let R := J.pCoreIn 2
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_six_witness_hypothesisC28 h hd hmodel hw hWJ hJC
  obtain ⟨hKn,hLK⟩ := D.sourceOrbit_six_witness_constrained_placement
    h hd hmodel hw hWJ hJC K hK hq hout hfK
  let := hKn
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hLKg : LH ≤ Kg := by
    have hh := map_mono (f := H.subtype) hLK
    rwa [map_subgroupOf_eq_of_le hLH] at hh
  obtain ⟨f,hf,hfambient,hfrad⟩ :=
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
    have hv := D.sourceOrbit_six_witness_constrained_moved_placement
      h hd hmodel hw hWJ hJC K hK hq hout hfK v.toMul.property
    obtain ⟨w,hw,hwe⟩ := hv
    have he : w = (f v).toMul.val := Subtype.ext ((hwe.trans (hfambient v).symm))
    change (f v).toMul.val ∈ ⁅starV Kg R,Kg.subgroupOf (Kg ⊔ R)⁆
    exact he ▸ hw
  have hdis : Disjoint f.range (fixedSpace
      ((starRepresentation Kg R).comp (offenderSubgroup (starRepresentation Kg R)).subtype)
      ((starImage Kg R Kg).subgroupOf (offenderSubgroup (starRepresentation Kg R)))) := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hCO]
    apply Submodule.disjoint_def.mpr
    rintro _ ⟨v,rfl⟩ hv
    have hcentral := (NormalElementaryQuotient.mem_fixedSpace_image (starV Kg R)
      (QuotientGroup.mk' (starKernel Kg R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) (Kg.subgroupOf (Kg ⊔ R)) (f v)).mp hv
    have hfixed : (v.toMul : G) ∈ D.sourceOrbit ⊓ centralizer (LH : Set G) := by
      refine ⟨v.toMul.property,?_⟩
      intro l hl
      have hh := congrArg Subtype.val
        (hcentral ⟨l,mem_sup_left (hLKg hl)⟩ (hLKg hl))
      change l * (((f v).toMul : (Kg ⊔ R : Subgroup G)) : G) =
        (((f v).toMul : (Kg ⊔ R : Subgroup G)) : G) * l at hh
      rwa [hfambient] at hh
    have hv1 := (D.sourceOrbit_six_witness_fixed_eq_bot h hd hmodel hw).le hfixed
    have hv0 : v = 0 := Additive.toMul.injective (Subtype.ext hv1)
    rw [hv0,f.map_zero]
  let i := f.codRestrict c.sectionData.space.toSubmodule (fun v => hm ⟨v,rfl⟩)
  have hgi := quotient_injective c.sectionData f hf hm hdis
  have hdim := LinearMap.finrank_le_finrank_of_injective hgi
  rw [D.sourceOrbit_six_dimension h hd hmodel] at hdim
  refine ⟨hCO,c,i,hfambient,?_,?_,hgi,?_,hdim.trans
    c.sectionData.central.toSubmodule.finrank_quotient_le,hdim⟩
  · intro v w he
    exact hf (congrArg Subtype.val he)
  · rintro _ ⟨v,rfl⟩ a
    apply Subtype.ext
    exact hfrad ⟨v,rfl⟩ ⟨a.val.val,a.property⟩
  · rintro _ ⟨v,rfl⟩ a
    change c.sectionData.central.toSubmodule.mkQ (c.sectionData.space.toRepresentation a (i v)) =
      c.sectionData.central.toSubmodule.mkQ (i v)
    congr 1
    apply Subtype.ext
    exact hfrad ⟨v,rfl⟩ ⟨a.val.val,a.property⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
