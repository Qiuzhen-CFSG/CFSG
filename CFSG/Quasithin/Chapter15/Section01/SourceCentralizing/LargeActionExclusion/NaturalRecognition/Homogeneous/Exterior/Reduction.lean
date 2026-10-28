module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.SourceCore
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition
public import Theory.Representation.BinaryOffender.FixedSummandTransport

/-!
# The two inputs to the exterior branch of original 15.1.28

The source supplies a best offender in the two-core of the original seed's
pointwise stabilizer. Split exterior coordinates transport this same offender
and this same core to the concrete exterior square. The cube is included by
the graph-compatible recognition theorem.

Two inputs remain explicit here: constructing these split coordinates from
the original degree-ten branch, and excluding a best offender from the core
of a nonzero Sylow-fixed exterior seed. The conditional consumer below does
not assert that either input has already been established.

Source: Aschbacher--Smith 15.1.28, printed p.1103.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
namespace ExteriorReduction
open Representation.SL5TenDimensional

variable {D U : Type*} [_root_.Group D] [AddCommGroup U] [Module (ZMod 2) U]

/-- Actual coordinates on the whole source module, including its fixed factor.
The seed is projected through this equivalence; no parabolic or core identity
is part of this data. -/
structure SeedCoordinates (σ : Representation (ZMod 2) D U)
    (P : Submodule (ZMod 2) U) where
  actor : D ≃* Group
  coordinates : U ≃ₗ[ZMod 2] ExteriorModule 2 × σ.invariants
  intertwines : ∀ g v, coordinates (σ g v) =
    (exteriorAction 2 (actor g) (coordinates v).1, (coordinates v).2)
  projected_ne_bot : P.map (splitSeedProjection coordinates) ≠ ⊥
  sylow : Sylow 2 Group
  fixed : P.map (splitSeedProjection coordinates) ≤
    BinaryOffender.fixedSpace (exteriorAction 2) sylow

/-- Source fixedness and movement suffice once the full split coordinates
are constructed. The Sylow subgroup uses the same actor isomorphism. -/
noncomputable def SeedCoordinates.of_split
    [Finite D]
    {σ : Representation (ZMod 2) D U} {P : Submodule (ZMod 2) U}
    (actor : D ≃* Group) (coordinates : U ≃ₗ[ZMod 2] ExteriorModule 2 × σ.invariants)
    (he : ∀ g v, coordinates (σ g v) =
      (exteriorAction 2 (actor g) (coordinates v).1, (coordinates v).2))
    (R : Sylow 2 D) (hfixed : P ≤ BinaryOffender.fixedSpace σ R)
    (hmoving : ¬ P ≤ σ.invariants) : SeedCoordinates σ P where
  actor := actor
  coordinates := coordinates
  intertwines := he
  projected_ne_bot := projected_seed_ne_bot_of_fixed_summand σ (exteriorAction 2)
    actor coordinates he P hmoving
  sylow := R.mapSurjective (f := actor.toMonoidHom) actor.surjective
  fixed := projected_seed_fixed_of_fixed_summand σ (exteriorAction 2)
    actor coordinates he P R hfixed

/-- The concrete geometric obligation, independent of the ambient source group.
Its proof must identify the Sylow-fixed seed stabilizer and exclude its offenders. -/
def ModelSeedCoreExclusion : Prop :=
  ∀ (R : Sylow 2 Group) (P : Submodule (ZMod 2) (ExteriorModule 2)),
    P ≠ ⊥ → P ≤ BinaryOffender.fixedSpace (exteriorAction 2) R →
      ∀ A : Subgroup Group, IsBestOffender (exteriorAction 2) A →
        ¬ A ≤ (subspaceKernel (exteriorAction 2) P ⊤).pCoreIn 2

/-- The original offender and core survive the full-module projection. -/
theorem false_of_seed_coordinates [FiniteDimensional (ZMod 2) U]
    {σ : Representation (ZMod 2) D U} {P : Submodule (ZMod 2) U}
    (e : SeedCoordinates σ P) (hmodel : ModelSeedCoreExclusion)
    {A : Subgroup D} (hA : IsBestOffender σ A)
    (hcore : A ≤ (subspaceKernel σ P ⊤).pCoreIn 2) : False := by
  obtain ⟨hb, hc⟩ := seed_core_offender_of_fixed_summand σ (exteriorAction 2)
    e.actor e.coordinates e.intertwines P hA hcore
  exact hmodel e.sylow _ e.projected_ne_bot e.fixed _ hb hc

end ExteriorReduction

open Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Literal source consumer of the two exterior prerequisites. The full
original context and the selected B.5 section are retained. Completion of
15.1.28 still requires constructing `e` and proving `hmodel`. -/
theorem HasExchangedLinearSource.exterior_false_of_seed_coordinates_and_model_core
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (_hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (_hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (_hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      BinaryActor.ActionCase (ρ.comp B.subtype) K c.sectionData 5 →
      IsIrreducible (c.sectionData.space.toRepresentation.comp K.subtype) →
      Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = 10 →
      ExteriorReduction.SeedCoordinates (ρ.comp B.subtype) (d.exchangedSeedSpace t J) →
      ExteriorReduction.ModelSeedCoreExclusion → False := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K _c _hc _hirr _hdim e hmodel
  obtain ⟨A, _hA, _hb, hbB, hcore⟩ :=
    s.original_seed_core_offender hG hM hu h t ht htS
  exact ExteriorReduction.false_of_seed_coordinates e hmodel hbB hcore

/-- The dimension-only row recognizes the selected source moved module,
preserving a prescribed component marking or its explicit graph twist.
This is recognition of the moved module, not yet the full split coordinates. -/
theorem HasExchangedLinearSource.original_exterior_moved_coordinates
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (_hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (_hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (_hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (_htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      BinaryActor.ActionCase (ρ.comp B.subtype) K c.sectionData 5 →
      IsIrreducible (c.sectionData.space.toRepresentation.comp K.subtype) →
      Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = 10 →
      ∀ mark : K ≃* Representation.SL5TenDimensional.Group,
        ∃ (actor : K ≃* Representation.SL5TenDimensional.Group)
          (coordinates : c.sectionData.space.toSubmodule ≃ₗ[ZMod 2]
            Representation.SL5TenDimensional.ExteriorModule 2),
          (actor = mark ∨ actor = mark.trans Representation.SL5ExteriorSquare.Duality.graph) ∧
          ∀ g v, coordinates ((c.sectionData.space.toRepresentation.comp K.subtype) g v) =
            Representation.SL5TenDimensional.exteriorAction 2 (actor g) (coordinates v) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c _hc hirr hdim mark
  let := hirr
  exact Representation.SL5ExteriorSquare.square_coordinates_of_finrank_ten
    (c.sectionData.space.toRepresentation.comp K.subtype) mark hdim

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
