module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterModule
public import CFSG.Quasithin.ChapterE.Section03.Parameters.MovedAction
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive.Local
public import Theory.Representation.BinaryConjugationSection.Relabel
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# Passing the local parameter from the moved module to the whole omega span

For the actual reduced U=V_H, the moved subgroup W=[U,O²(H)] has exactly
C_H(U) as its centralizer. The induced action on W therefore retains every
actor on U. Restricting fixed-space equalities bounds a(H,U) by a(H,W).
This supplies the full fixed-layer transport in 12.4.1. In particular the
single deleted A₅ module calculation now applies to all of U, with its
original H-action and its original residual quotient.

Source: Aschbacher–Smith 12.3.2 and 12.4.1, printed pp.807,812, using
B.2.14. LocalParameterModels supplies the doubled A₅ branch. The production
of the local classification remains with qt-d-1241-l3-conjugate.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

/-- The commutator is taken in G with the literal embedded two-residual. -/
abbrev localMoved (T : Sylow 2 G) (H : Subgroup G) : Subgroup G :=
  ⁅localModule T H,localResidual H⁆

omit [Finite G] in
theorem localMoved_le (T : Sylow 2 G) (H : Subgroup G) : localMoved T H ≤ localModule T H :=
  le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (localModule_normalized T H))

omit [Finite G] in
theorem localMoved_normalized (T : Sylow 2 G) (H : Subgroup G) :
    H ≤ normalizer (localMoved T H : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅localModule T H,localResidual H⁆).map _ = _
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (localModule_normalized T H hh),
    mem_normalizer_iff_map_conj_eq.mp (localResidual_normalized H hh)]

omit [Finite G] in
theorem localMoved_subgroupOf (hTH : (T : Subgroup G) ≤ H) :
    (localMoved T H).subgroupOf H = ⁅(localModule T H).subgroupOf H,pResidual 2 H⁆ := by
  have he : (⁅(localModule T H).subgroupOf H,pResidual 2 H⁆ : Subgroup H).map H.subtype =
      localMoved T H := by
    rw [map_commutator,map_subgroupOf_eq_of_le (localModule_le hTH)]
  rw [←he]
  exact comap_map_eq_self_of_injective H.subtype_injective _

/-- Restriction to the moved subgroup loses no actual H-automorphism. -/
theorem localMoved_centralizer_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    centralizer ((localMoved T H).subgroupOf H : Set H) =
      centralizer ((localModule T H).subgroupOf H : Set H) := by
  have hr := localModule_reduced h hH
  let := hr.normal
  let := hr.elementary
  rw [localMoved_subgroupOf hH.1.1.2]
  exact hr.centralizer_moved_eq _

/-- The parameter on the entire original U is bounded by its moved part. -/
theorem localModule_parameter_le_moved
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (localModule T H)] [IsElementaryAbelian 2 (localMoved T H)] :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤
    moduleA ((automizerRepresentation (localMoved T H)).comp
      (inducedAutomizer (localMoved T H) H).subtype) :=
  moduleA_induced_le_of_centralizer_eq _ _ _ (localMoved_le T H)
    (localModule_le hH.1.1.2) (localModule_normalized T H) (localMoved_normalized T H)
    (localMoved_centralizer_eq h hH)

/-- The single deleted A₅ branch, including the outer H-action and all fixed layers. -/
theorem localModule_parameter_of_single_deleted
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (localModule T H)]
    (q : localResidual H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : Representation.BinaryConjugationSection (localResidual H) (localMoved T H) ⊥
      (((BinaryPermutation.naturalRepresentation (Fin 5)).comp
        (alternatingGroup (Fin 5)).subtype).comp q)) :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1 := by
  let : IsElementaryAbelian 2 (localMoved T H) := IsElementaryAbelian.of_le (localMoved_le T H)
  exact (localModule_parameter_le_moved h hH).trans
    (moduleA_local_deleted_section_le_one _ _ _ q hq c (map_subtype_le _)
      (inf_le_left.trans (localResidual_normalized H)))

/-- The same bound in the augmentation-core coordinates used by the
source module classification. The actor and the section kernel are unchanged. -/
theorem localModule_parameter_of_single_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (localModule T H)]
    (q : localResidual H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : Representation.BinaryConjugationSection (localResidual H) (localMoved T H) ⊥
      ((BinaryPermutation.alternatingCoreRepresentation (Fin 5)).comp q)) :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1 := by
  let e : Representation.Equiv (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
      ((BinaryPermutation.naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype) := {
    __ := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      exact BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) g.val v }
  exact localModule_parameter_of_single_deleted h hH q hq (c.relabel q e)

/-- Literal source single-module application: K is the embedded O²(H),
the marking is K/O₂(K), and the supplied section is [⟨Zᴷ⟩,K]. -/
theorem localModule_parameter_of_source_single
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (localModule T H)]
    (q : (localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection (localResidual H)
      ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆ ⊥
      ((BinaryPermutation.alternatingCoreRepresentation (Fin 5)).comp
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localResidual H)))))) :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1 := by
  apply localModule_parameter_of_single_core h hH
    (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localResidual H))))
    (q.surjective.comp (QuotientGroup.mk'_surjective _))
  simpa only [localMoved,localModule_eq_residual_span hH.1.1.2] using c
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
