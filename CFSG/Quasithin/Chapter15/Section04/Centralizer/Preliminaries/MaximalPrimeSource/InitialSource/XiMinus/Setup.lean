module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.TheoremCInputs
public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The original local group and module in the empty-family Xi argument

The genuine universal Theorems A and C imply that every maximal two-local
over the original Sylow subgroup is solvable. The solvable embedding theorem
therefore identifies N_G(X) as the unique maximal two-local over XT, without
using 3.2.13 or the general nonsolvable cases of 1.3.7.

We retain the literal module V = [R₂(XT), X]. Its elementary structure and
containment in O₂(X), hence in O₂(N_G(X)), follow from normality and the
definition of R₂. Its nontriviality, reducedness and exact Sylow centralizer
are separate source obligations; none is built into these definitions.

Source: Aschbacher--Smith, 3.2.13, printed pp.584--585, and the independent
solvability deduction 15.4.2(1--2), printed pp.1155--1156.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G]

/-- The original join XT, inside G. -/
abbrev sourceGroup (T X : Subgroup G) := X ⊔ T

/-- The original commutator module, inside XT. -/
@[expose] def sourceModule (T X : Subgroup G) : Subgroup (sourceGroup T X) :=
  ⁅reducedTwoSubgroup (sourceGroup T X), X.subgroupOf (sourceGroup T X)⁆

/-- The commutator is contained in the literal R₂(XT). -/
theorem sourceModule_le_reduced (T X : Subgroup G) :
    sourceModule T X ≤ reducedTwoSubgroup (sourceGroup T X) :=
  commutator_le_left _ _

/-- Elementary structure does not require the missing reducedness theorem. -/
instance sourceModule_elementary (T X : Subgroup G) :
    IsElementaryAbelian 2 (sourceModule T X) := by
  let := (isPReduced_reducedPSubgroup (p := 2) (G := sourceGroup T X)).elementary
  exact IsElementaryAbelian.of_le (sourceModule_le_reduced T X)

/-- The actual Xi invariance makes both inputs normal in XT. -/
theorem sourceModule_normal {T X : Subgroup G} (hX : X ∈ Chapter1.Xi G T) :
    (sourceModule T X).Normal := by
  let := hX.normal_in_join
  unfold sourceModule
  infer_instance

/-- The core of XT centralizes its original commutator module. -/
theorem sourceModule_core_centralizes (T X : Subgroup G) :
    pCore 2 (sourceGroup T X) ≤
      centralizer (sourceModule T X : Set (sourceGroup T X)) :=
  le_centralizer_iff.mp ((sourceModule_le_reduced T X).trans
    (reducedPSubgroup_le_centralizer_pCore 2 (sourceGroup T X)))

variable [Finite G]

/-- A normal elementary commutator contained in X lies in its two-core. -/
theorem sourceModule_le_intrinsicCore {T X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G T) :
    (sourceModule T X).map (sourceGroup T X).subtype ≤ X.pCoreIn 2 := by
  let H := sourceGroup T X
  let Y := X.subgroupOf H
  let := hX.normal_in_join
  let := sourceModule_normal hX
  have hVY : sourceModule T X ≤ Y := commutator_le_right _ _
  have hcore : sourceModule T X ≤ Y.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) hVY
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hm := map_mono (f := H.subtype) hcore
  rwa [map_pCoreIn_of_ker_isPGroup H.subtype
    (IsPGroup.ker_isPGroup_of_injective H.subtype_injective),
    map_subgroupOf_eq_of_le (show X ≤ H from le_sup_left)] at hm

/-- Normality of X in its normalizer supplies the core containment needed
by 15.4.2(4); no earlier prime restriction is used. -/
theorem sourceModule_le_normalizerCore {T X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G T) :
    (sourceModule T X).map (sourceGroup T X).subtype ≤
      (normalizer (X : Set G)).pCoreIn 2 :=
  (sourceModule_le_intrinsicCore hX).trans
    (pCoreIn_mono_of_normalizes X.le_normalizer le_rfl)

omit [Finite G] in
/-- The literal centralizer's two-core is O₂(XT). This equality needs
normality and core centralization, but not reducedness of the module. -/
theorem source_centralizer_core {T X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G T) :
    (centralizer (sourceModule T X : Set (sourceGroup T X))).pCoreIn 2 =
      pCore 2 (sourceGroup T X) := by
  let := sourceModule_normal hX
  let H := sourceGroup T X
  let C := centralizer (sourceModule T X : Set H)
  apply le_antisymm
  · exact le_sSup ⟨by change ((pCore 2 C).map C.subtype).Normal; infer_instance,
      isPGroup_pCoreIn 2 C⟩
  · exact le_pCoreIn_of_normalizes pCore_isPGroup (sourceModule_core_centralizes T X)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)

variable
  (hA : ∀ (K : Type u) [Group K] [Finite K],
    ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple K)
  (hC : ∀ (K : Type u) [Group K] [Finite K],
    ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple K)

include hA hC in
/-- The independent source solvability step, with all model facts supplied
by genuine Theorem C and the full known-simple catalogue. -/
theorem source_maximalTwoLocal_solvable (T : Sylow 2 G) (h : SourceHypotheses T)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) :
    Group.IsSolvable M :=
  InitialSource.source_lemma_15_4_2_two
    (fun _K _ _ hK hO S B hB => ChapterA.Section03.SourceComponents.containment
      hA (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC hC)
      hK hO S B hB)
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    (fun _K _ _ hK hO => ChapterA.Section03.SourceComponents.generation
      hA (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC hC) hK hO)
    T h hM hTM

include hA hC in
/-- The exact normalizer and maximal-two-local uniqueness used in 3.2.13,
specialized to the actual empty-family hypotheses of Theorem E. -/
theorem source_normalizer_unique (T : Sylow 2 G) (h : SourceHypotheses T)
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G)) :
    IsMaximalTwoLocal (normalizer (X : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M} =
        {normalizer (X : Set G)} :=
  Chapter1.XiEmbedding.normalizer_unique_of_solvable_maximalTwoLocals h.simpleQTKE T
    (fun _ hM hTM => source_maximalTwoLocal_solvable hA hC T h hM hTM) hX

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
