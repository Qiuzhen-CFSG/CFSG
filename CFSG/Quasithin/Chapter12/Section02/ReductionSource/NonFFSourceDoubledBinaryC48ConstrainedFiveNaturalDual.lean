module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedFiveFlag
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedMoved
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.RadicalFixedBound

/-!
# Excluding the actual constrained SL5 natural-plus-dual module

The original orbit embeds as a six-dimensional fixed subspace for the literal
radical image in the actual moved star module. The SL5 source proves that the
radical intersection is nontrivial and radical. Every natural-plus-dual marking
would bound this fixed space by its natural degree, at most five. Thus the
original B.5.1 natural-plus-dual row is impossible without identifying the
parabolic residual. The full source conclusion and original embedding remain.
Source: Aschbacher--Smith B.5.1, C.4.8 and 12.1.11, pp.99,154,794.
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

/-- The original five-dimensional star retains its actual moved conclusion,
with every degree-four/five natural-plus-dual marking excluded. -/
theorem sourceOrbit_binary_witness_constrained_five_no_natural_dual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    let ρ := starRepresentation (K.map H.subtype) (J.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    ∃ _hCO : C ≤ O,
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp O.subtype) (C.subgroupOf O),
      ∃ i : Additive D.sourceOrbit →ₗ[ZMod 2] c.sectionData.space.toSubmodule,
        (∀ v, (((i v).val.toMul : ((K.map H.subtype) ⊔ (J.pCoreIn 2) : Subgroup G)) : G) = v.toMul) ∧
        SixSpaceMovedEmbedding c.sectionData
          ((starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2)).subgroupOf O) i ∧
        (∃ n, (n = 4 ∨ n = 5) ∧ SixSpaceMovedCases c.sectionData n) ∧
        ∀ n, n = 4 ∨ n = 5 →
          ¬ IsNaturalPlusDual (c.sectionData.space.toRepresentation.comp (C.subgroupOf O).subtype) n := by
  obtain ⟨hCO,c,i,hi,hdata,hcases⟩ := D.sourceOrbit_binary_witness_constrained_moved_sieve
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK (Or.inr ⟨e⟩)
  refine ⟨hCO,c,i,hi,hdata,hcases,?_⟩
  intro n hn hnat
  let Kg := K.map H.subtype
  let R := J.pCoreIn 2
  let ρ := starRepresentation Kg R
  let O := offenderSubgroup ρ
  let C := starImage Kg R Kg
  let P := (starImage Kg R R).subgroupOf C
  let eC : C ≃* C.subgroupOf O := (subgroupOfEquivOfLe hCO).symm
  let P' := P.map eC.toMonoidHom
  let σ := c.sectionData.space.toRepresentation.comp (C.subgroupOf O).subtype
  have hP := (D.sourceOrbit_binary_witness_constrained_five_flag
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK e).1
  have hfix : i.range ≤ fixedSpace σ P' := by
    rintro _ ⟨v,rfl⟩ ⟨_,x,hx,rfl⟩
    exact hdata.2.1 ⟨v,rfl⟩ ⟨⟨x.val,hCO x.property⟩,hx⟩
  let f := i.codRestrict (fixedSpace σ P') (fun v => hfix ⟨v,rfl⟩)
  have hf : Function.Injective f := by
    intro v w he
    exact hdata.1 (congrArg Subtype.val he)
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  rw [D.sourceOrbit_binary_dimension h hd F hF hmodel] at hdim
  have hbound := NaturalDualCentralizer.finrank_radical_fixed_le σ P'
    (hP.map_equiv eC) (by omega : 0 < n) hnat
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
