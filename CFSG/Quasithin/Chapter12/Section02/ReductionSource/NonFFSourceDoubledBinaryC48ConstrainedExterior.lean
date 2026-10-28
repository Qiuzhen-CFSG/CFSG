module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedLinearModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedFixedSpace
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedRepeated

/-!
# The surviving constrained binary exterior row

The actual source section contains the original six-space in both its moved
module and its full central quotient. Natural dimensions are too small;
faithfulness excludes the orthogonal quotient; actual whole-actor radical
fixed spaces exclude natural-plus-dual; and the original two simple summands
exclude every repeated-natural multiplicity. The sole surviving actor is
SL5(2), with the actual irreducible ten-dimensional module and its B.5.1
end-node offender data. No exterior-coordinate recognition is assumed.
Source: Aschbacher--Smith B.5.1, C.4.8 and 12.1.11.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The literal surviving exterior row, retaining its actor and offender marking. -/
@[expose] def ConstrainedExteriorSection
    {E Y : Type*} [Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) : Prop :=
  C = ⊤ ∧ Function.Injective s.action ∧
  IsIrreducible (s.action.comp C.subtype) ∧
  Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10 ∧
  ∃ e : C ≃* SL(5,ZMod 2),
    (∀ A, IsBestOffender s.action A → IsEndNodeRadical ((A.subgroupOf C).map e.toMonoidHom)) ∧
    quadraticRatio s.action = 1 ∧
    IsIrreducible (s.space.toRepresentation.comp C.subtype) ∧
    Module.finrank (ZMod 2) s.space.toSubmodule = 10

private theorem exterior_of_exclusions
    {E Y : Type*} [Group E] [Finite E] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y] {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hc : BinaryActor.ActionCase ρ C s n)
    (hm : 6 ≤ Module.finrank (ZMod 2) s.space.toSubmodule)
    (hq : 6 ≤ Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule))
    (hfaith : Function.Injective s.action →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≠ 6)
    (hdual : C = ⊤ → ¬ IsNaturalPlusDual (s.space.toRepresentation.comp C.subtype) n)
    (hrep : NoSmallRepeatedMoved s) : ConstrainedExteriorSection s := by
  cases hc with
  | naturalDual hw hd => exact (hdual hw hd).elim
  | repeatedNatural r _ _ _ hr => exact (hrep n hn r hr).elim
  | irreducible hi hf hir hs he =>
    cases hs with
    | natural _ e _ =>
      have hd := e.linearEquiv.finrank_eq
      change Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) =
        Module.finrank (ZMod 2) (Fin n → ZMod 2) at hd
      simp at hd
      omega
    | orthogonal _ _ _ e _ _ =>
      apply (hfaith hf _).elim
      rw [e.linearEquiv.finrank_eq,BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
      rfl
    | symmetricEight _ _ e _ =>
      apply (hfaith hf _).elim
      rw [e.action.linearEquiv.finrank_eq,
        BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
      rfl
    | exterior hd hg hw e hdim ho hr =>
      subst n
      have hcase : BinaryActor.ActionCase ρ C s 5 :=
        .irreducible hi hf hir (.exterior rfl hg hw e hdim ho hr) he
      have hmove := BinaryActor.movedCase (Or.inr rfl) hcase
      have hmi : IsIrreducible (s.space.toRepresentation.comp C.subtype) ∧
          Module.finrank (ZMod 2) s.space.toSubmodule = 10 := by
        cases hmove with
        | natural a =>
          have hd := a.linearEquiv.finrank_eq
          change Module.finrank (ZMod 2) s.space.toSubmodule =
            Module.finrank (ZMod 2) (Fin 5 → ZMod 2) at hd
          simp at hd
          omega
        | orthogonal h _ _ _ => omega
        | exterior _ _ hi hd => exact ⟨hi,hd⟩
        | naturalDual hd => exact (hdual hw hd).elim
        | repeatedNatural r _ _ hr => exact (hrep 5 (Or.inr rfl) r hr).elim
      exact ⟨hw,hf,hir,hdim,e,ho,hr,hmi⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original constrained source has only the literal SL5 exterior row left. -/
theorem sourceOrbit_binary_witness_constrained_exterior
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
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
        SixSpaceMovedEmbedding c.sectionData
          ((starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2)).subgroupOf O) i ∧
        ConstrainedExteriorSection c.sectionData := by
  have hstar := D.sourceOrbit_binary_witness_constrained_linear_models
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  obtain ⟨hCO,c,i,hi,hdata⟩ := D.sourceOrbit_binary_witness_constrained_classified_embedding
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK hstar
  refine ⟨hCO,c,i,hi,hdata,?_⟩
  have hm : ∃ n, (n = 4 ∨ n = 5) ∧ Nonempty (
      ((starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (K.map H.subtype) (J.pCoreIn 2)))) ≃*
          SL(n,ZMod 2)) := by
    rcases hstar with h8 | h5
    · obtain ⟨e⟩ := h8
      exact ⟨4,Or.inl rfl,⟨(subgroupOfEquivOfLe hCO).trans (e.trans
        (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm.trans
          (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))))⟩⟩
    · obtain ⟨e⟩ := h5
      exact ⟨5,Or.inr rfl,⟨(subgroupOfEquivOfLe hCO).trans e⟩⟩
  obtain ⟨n,hn,⟨e⟩⟩ := hm
  apply exterior_of_exclusions c.sectionData hn (BinaryActor.actionCase _ hn e c.clause_one)
    hdata.2.2.2.2.1 hdata.2.2.2.2.2
  · exact D.sourceOrbit_binary_witness_constrained_no_faithful_six
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK c i hdata
  · intro hwhole
    exact D.sourceOrbit_binary_witness_constrained_no_whole_natural_dual
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK hCO c i hdata hwhole n hn
  · exact D.sourceOrbit_binary_witness_constrained_not_repeated_embedding
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK hstar hCO c i hi hdata.1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
