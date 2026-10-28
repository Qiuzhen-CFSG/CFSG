module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadius
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalTensorAssembly

/-!
# Conditional original tensor consumers of a radius bound

The proved lower bound on the original radius quotient contradicts a strict
upper bound of 256. This sufficient numerical criterion feeds both original
tensor consumers through the existing marked-plane assembly. The upper bound
is explicitly unproved; it is not a claimed consequence of MS93 or of the
tensor model. These consumers do not complete SymplecticPlaneRecognition.

Source target: Aschbacher--Smith 9.3.10 and its final paragraph, pp.734--735,
and 13.3.2(2), pp.884--885; MS93 (5.7)--(5.12), pp.919--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB.QuasisimpleSource Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

/-- A sufficient numerical route on the original geometry. The bound is an
explicit unproved criterion; it is not part of the tensor model. -/
@[expose] def SymplecticRadiusBound (m : SourceA5TensorModel D e) : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) →
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∃ _geometry : Geometry R, (Z R (alpha R)).relIndex (V R (alpha R)) < 256

/-- The original radius bound would close the remaining symplectic branch. -/
theorem symplecticPlaneRecognition_of_radius_bound
    (hsource : m.SymplecticRadiusBound) : m.SymplecticPlaneRecognition := by
  apply symplecticPlaneRecognition_of_core_bound
  intro c eK
  obtain ⟨geometry,hsmall⟩ := hsource c eK
  exact (Nat.not_lt_of_ge (c.original_radius_index_ge_256 eK geometry _ rfl) hsmall).elim

theorem false_of_generationTwo_source_inputs_of_radius_bound
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion) (hsource : m.SymplecticRadiusBound) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (symplecticPlaneRecognition_of_radius_bound hsource)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 Chapter10.SourceA5TensorModel ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_minimal_point_control_of_tensor_radius_bound
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnormal : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.NonzeroCoreCartanNormalization)
    (hzero : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.ZeroCoreLineCentralization)
    (hcontain : A5PairContainment G)
    (hrows : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.LinearAndG2Exclusion)
    (hsource : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.SymplecticRadiusBound) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  apply exists_original_minimal_point_control_of_tensor_source_inputs h e hn ht htn hmany
    hnormal hzero hcontain hrows
  intro D hD m
  exact symplecticPlaneRecognition_of_radius_bound (hsource D hD m)
end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
