module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceTensorComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5BorelModule

/-!
# The original terminal catalogue with its A₅ seed module

The completed larger-actor degree theorem makes the normalized A₅
embedding onto, identifying that whole component action with the binary
five-point augmentation core. The general terminal catalogue retains the
same normalized component together with an embedded core containing the
original seed, or the independently handled L₂(8) row.

Both conclusions are obtained from the original source prefix, without a
module-recognition callback. Ambient field-four recognition and the Borel
contradiction remain with the terminal-solvability owner; the independent
L₂(8) source exclusion is still required for final assembly.
Source: Aschbacher–Smith 14.3.6 and 14.3.14–15, printed pp.991,993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- The entire larger-actor A₅ action is the orthogonal five-point core,
with the original ambient lift, normalization and component marking. -/
theorem exists_normalized_orthogonal_a5_lift :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      K = conjugateSpanBy K (T : Subgroup G) ∧
      ∃ e5 : F.terminalDot K ≃* alternatingGroup (Fin 5),
        Nonempty (Representation.Equiv
          ((F.terminalRepresentation.comp (F.terminalDot K).subtype).comp e5.symm.toMonoidHom)
          (BinaryPermutation.alternatingCoreRepresentation (Fin 5))) := by
  obtain ⟨K,hK,⟨e5⟩,hspan⟩ := s.exists_normalized_a5_lift
  exact ⟨K,hK,hspan,e5,source_single_a5_equiv_core_of_four s.simple T s.empty
    s.maximal s.unique_overgroup s.many_overgroups s.seed_card s.centralizer_quotient.some
    F s.nonabelian s.not_model g s.parabolic_mem s.normalizer_not_mem s.hypothesis
    hK e5 hspan s.degree_eq_four⟩
end LargeActorSource

section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hyp

/-- The normalized branch of the original terminal catalogue carries an
actual embedded orthogonal A₅ module containing the source seed. No action
recognition premise is added, and the selected ambient component is unchanged. -/
theorem source_normalized_a5_seed_core_or_eight
    (hn : ¬ Group.IsSolvable F.TerminalHdot) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      ((K = conjugateSpanBy K (T : Subgroup G) ∧
        ∃ e5 : F.terminalDot K ≃* alternatingGroup (Fin 5),
          ∃ f : IntertwiningMap (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
            ((F.terminalRepresentation.comp (F.terminalDot K).subtype).comp e5.symm.toMonoidHom),
            Function.Injective f ∧
              hatSpace F (rankTwoSeed T M) ≤ LinearMap.range f.toLinearMap) ∨
        EightImageRow F K) := by
  obtain ⟨K,hK,⟨hspan,⟨e5⟩⟩ | h8⟩ := source_normalized_a5_or_eight
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hn
  · exact ⟨K,hK,Or.inl ⟨hspan,e5,source_single_a5_seed_core_embedding
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan⟩⟩
  · exact ⟨K,hK,Or.inr h8⟩
end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
