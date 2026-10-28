module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Movement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.WeightFour
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.CubicSpan
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Applications

/-!
# The natural weight-four source branches with movement discharged

The component at the original local supplies point-core movement in G₁.
Both A₇ and S₇ weight-four branches then contradict the centralizer rank
bound through their literal group and module quotients. The group, Sylow
and word markings remain explicit; constructing these from the source
partition argument is required before the final RowExclusions application.
Source: Aschbacher–Smith 14.7.50, printed pp.1064–1065, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open BinaryPermutation.SevenSourceCubics
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The symmetric weight-four branch for the original component, with no
extra point-core movement premise. -/
theorem local_symmetric_weight_four_of_component_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 7))
    (m : Representation.Equiv ((BinaryPermutation.coreRepresentation (Fin 7)).comp
      b.toMonoidHom) N.quotientRepresentation)
    (hT : ((T : Subgroup G).subgroupOf I).map
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = standardTwo)
    (hword : ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
      m.symm (N.toSubmodule.mkQ (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) = 0 ∨
      m.symm (N.toSubmodule.mkQ (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) = point) : False := by
  exact local_symmetric_weight_four_quotient_impossible_at h hab structural previous faithful
    (local_alternating_seven_plane_moved_at d h hab structural previous faithful earlier
      source47 I hI C hC e) I hI a N hN b m hT hword

/-- The alternating weight-four branch for the original component, with
its full kernel and its alternating Sylow marking. -/
theorem local_alternating_weight_four_of_component_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (b : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (m : Representation.Equiv ((BinaryPermutation.alternatingCoreRepresentation (Fin 7)).comp
      b.toMonoidHom) N.quotientRepresentation)
    (hT : ((T : Subgroup G).subgroupOf I).map
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = Alternating.two)
    (hword : ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
      m.symm (N.toSubmodule.mkQ (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) = 0 ∨
      m.symm (N.toSubmodule.mkQ (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) = point) : False := by
  exact local_alternating_weight_four_quotient_impossible_at h hab structural previous faithful
    (local_alternating_seven_plane_moved_at d h hab structural previous faithful earlier
      source47 I hI C hC e) I hI a N hN b m hT hword

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
