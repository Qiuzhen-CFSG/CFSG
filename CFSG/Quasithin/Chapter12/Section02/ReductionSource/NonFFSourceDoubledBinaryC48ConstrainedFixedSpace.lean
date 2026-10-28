module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedMoved
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OffenderRadical
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.RadicalFixedBound

/-!
# Fixed-space exclusions on the literal constrained section

The actual radical-offender intersection is nontrivial. Its six-dimensional
fixed embedding survives the full central projection, excluding faithful
six-dimensional quotients. In a whole-actor row the actual component radical
is nontrivial and radical, so natural-plus-dual fixed-space bounds exclude
every degree-four/five marking on this same moved section.
Source: Aschbacher--Smith B.5.1, C.2.7, C.4.8 and 12.1.11.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
private theorem faithful_fixed_embedding_impossible
    {E Y Z : Type*} [Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    [FiniteDimensional (ZMod 2) Y] [FiniteDimensional (ZMod 2) Z]
    (ρ : Representation (ZMod 2) E Y) (B : Subgroup E) (hB : B ≠ ⊥)
    (hρ : Function.Injective ρ) (f : Z →ₗ[ZMod 2] Y) (hf : Function.Injective f)
    (hfix : f.range ≤ fixedSpace ρ B)
    (hdim : Module.finrank (ZMod 2) Z = Module.finrank (ZMod 2) Y) : False := by
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf
  apply hB
  apply bot_unique
  intro b hb
  change b = 1
  apply hρ
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := hsurj v
  simpa only [map_one,Module.End.one_apply,MonoidHom.comp_apply,Subgroup.coe_subtype]
    using hfix ⟨w,rfl⟩ ⟨b,hb⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original radical-fixed six-space excludes a faithful central quotient
of dimension six on this same source section. -/
theorem sourceOrbit_binary_witness_constrained_no_faithful_six
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
 :
    let Kg := K.map H.subtype
    let R := J.pCoreIn 2
    let ρ := starRepresentation Kg R
    let O := offenderSubgroup ρ
    let C := starImage Kg R Kg
    ∀ (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp O.subtype) (C.subgroupOf O))
      (i : Additive D.sourceOrbit →ₗ[ZMod 2] c.sectionData.space.toSubmodule),
      SixSpaceMovedEmbedding c.sectionData ((starImage Kg R R).subgroupOf O) i →
      Function.Injective c.sectionData.action →
      Module.finrank (ZMod 2)
        (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) ≠ 6 := by
  intro Kg R ρ O C c i hi hf hdim
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  exact faithful_fixed_embedding_impossible c.sectionData.central.quotientRepresentation
    ((starImage Kg R R).subgroupOf O)
    (ChapterC.C27Source.star_radical_offender_ne_bot_from_source
      (hc.constrained_source_input K hK hq hout hfK))
    hf (c.sectionData.central.toSubmodule.mkQ.comp i) hi.2.2.1 hi.2.2.2.1
    ((D.sourceOrbit_binary_dimension h hd F hF hmodel).trans hdim.symm)

/-- Whole-actor natural-plus-dual rows are impossible on the same original
moved section, in both remaining binary linear degrees. -/
theorem sourceOrbit_binary_witness_constrained_no_whole_natural_dual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
 :
    let Kg := K.map H.subtype
    let R := J.pCoreIn 2
    let ρ := starRepresentation Kg R
    let O := offenderSubgroup ρ
    let C := starImage Kg R Kg
    C ≤ O →
    ∀ (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp O.subtype) (C.subgroupOf O))
      (i : Additive D.sourceOrbit →ₗ[ZMod 2] c.sectionData.space.toSubmodule),
      SixSpaceMovedEmbedding c.sectionData ((starImage Kg R R).subgroupOf O) i →
      C.subgroupOf O = ⊤ →
      ∀ n, n = 4 ∨ n = 5 →
        ¬ IsNaturalPlusDual (c.sectionData.space.toRepresentation.comp (C.subgroupOf O).subtype) n := by
  intro Kg R ρ O C hCO c i hi hwhole n hn hnat
  let P := (starImage Kg R R).subgroupOf C
  let eC : C ≃* C.subgroupOf O := (subgroupOfEquivOfLe hCO).symm
  let P' := P.map eC.toMonoidHom
  let σ := c.sectionData.space.toRepresentation.comp (C.subgroupOf O).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hP := ChapterC.C27Source.star_intersection_radical_of_whole_offender_from_source
    (hc.constrained_source_input K hK hq hout hfK) hwhole
  have hfix : i.range ≤ fixedSpace σ P' := by
    rintro _ ⟨v,rfl⟩ ⟨_,x,hx,rfl⟩
    exact hi.2.1 ⟨v,rfl⟩ ⟨⟨x.val,hCO x.property⟩,hx⟩
  let f := i.codRestrict (fixedSpace σ P') (fun v => hfix ⟨v,rfl⟩)
  have hf : Function.Injective f := by
    intro v w he
    exact hi.1 (congrArg Subtype.val he)
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  rw [D.sourceOrbit_binary_dimension h hd F hF hmodel] at hdim
  have hbound := NaturalDualCentralizer.finrank_radical_fixed_le σ P'
    (hP.map_equiv eC) (by omega : 0 < n) hnat
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
