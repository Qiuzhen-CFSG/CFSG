module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveReduced
public import Theory.Alternating.FivePairOuterTwo

/-!
# The literal alternating-five diagonal core splitting

Once the original selected component is an alternating-five block, its
intrinsic layer is exactly W_K=[R₂(KAT),K]. The complete C.1.13(c) theorem
therefore supplies both the direct two-core decomposition and disjointness
required by the diagonal endgame. The block marking also gives the original
center-free A₅ quotient and its two-group outer automorphism group.

Only the separate source noncontainment, residual fixation and chief-count
commutator bound remain in this application. Source: Aschbacher--Smith,
13.3.14, final paragraph on p.893.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
variable {G : Type*} [Group G] [Finite G]

/-- Recognition as an A₅ block identifies the original W_K without a separate
module-coordinate premise. -/
theorem movedModule_eq_of_alternatingFive (K A T : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hA : A ≤ normalizer (K : Set G))
    (hT : T ≤ normalizer (K : Set G)) :
    movedModule K A T = (ChapterC.blockU K).map K.subtype :=
  hK.normalizer_reduced_commutator K (localGroup K A T)
    (le_sup_left.trans le_sup_left) (sup_le (sup_le K.le_normalizer hA) hT)

/-- C.1.13(c) on the exact local group used in the ordinary diagonal source. -/
theorem core_split_of_alternatingFive (K A T : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hA : A ≤ normalizer (K : Set G))
    (hT : T ≤ normalizer (K : Set G)) :
    ((localGroup K A T).pCoreIn 2 ⊓ centralizer (K : Set G)) ⊔
        movedModule K A T = (localGroup K A T).pCoreIn 2 ∧
      Disjoint ((localGroup K A T).pCoreIn 2 ⊓ centralizer (K : Set G))
        (movedModule K A T) :=
  hK.normalizer_core_reduced_decomposition K (localGroup K A T)
    (le_sup_left.trans le_sup_left) (sup_le (sup_le K.le_normalizer hA) hT)

omit [Finite G] in
/-- The marked block supplies exactly the quotient and outer-action hypotheses
used to construct the diagonal residual supplement. -/
theorem quotient_data_of_alternatingFive (K : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5) :
    center (K ⧸ pCore 2 K) = ⊥ ∧ IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) := by
  obtain ⟨e⟩ := hK.2.2.quotient_iso
  refine ⟨?_,Theory.AlternatingFive.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm⟩
  apply bot_unique
  intro z hz
  apply e.injective
  have hez : e z ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨x,rfl⟩ := e.surjective a
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hz x)
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hez
  simpa only [map_one] using hez

/-- The exact diagonal contradiction, with both core factors and quotient
structure discharged by the recognized alternating-five block. -/
theorem contradiction_of_alternatingFive (K A T : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hn : A ≤ normalizer (K : Set G)) (hT : T ≤ normalizer (K : Set G))
    (hA : IsPPerfect 2 A) (hJ : localGroup K A T ∈ Chapter1.He G)
    (hout : ¬ A ≤ K)
    (hfix : centralizerResidual K A hn ≤ centralizer (movedModule K A T : Set G))
    (hm : ⁅(localGroup K A T).pCoreIn 2,A⁆ ≤ movedModule K A T) : False := by
  have hsplit := core_split_of_alternatingFive K A T hK hn hT
  have hquot := quotient_data_of_alternatingFive K hK
  exact contradiction_of_core_decomposition K A T hn hK.2.1.twoPerfect hA
    hquot.1 hquot.2 hJ hout hfix hsplit.1 hsplit.2 hm
end CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
