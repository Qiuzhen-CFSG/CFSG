module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.BaumannEscape
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.MovedComponent
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.ReductionG

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalUnitaryNoncentrality.BaumannEscape`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal diagonal radical has the same Baumann subgroup as O₂(KT).
An arbitrary original chosen module of K suffices; the larger moved module
need not first be identified with it. -/
theorem unitary_baumann_identity_of_selected_five
    {T : Sylow 2 G} {L : Subgroup G} (h : Hypothesis1331 T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (five : OriginalAlternatingFiveModules1332At T L)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K A : Subgroup G) (hf : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hAK : A ≤ normalizer (K : Set G)) (hp : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hout : ¬ A ≤ K) (hgen : ⁅K,A⁆ = K) :
    ChapterB.baumann ((A ⊔ (T : Subgroup G)).pCoreIn 2) =
      ChapterB.baumann ((K ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := inferInstance
  have hq : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eK.symm
  have h12 : Hypothesis1223 KnownSimple.IsKnownSimple T K :=
    h.hypothesis1311.hypothesis1223
      ⟨source1332_faithful_maximal h.qtke T h1332 hf,
        ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hf).2⟩ hq
  have hTK := (h1332 K hf).1
  obtain ⟨I,⟨C⟩⟩ := h12.toHypothesis1221.exists_chosen_of_normalizes hTK
  let := C.elementary
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    ((structural K h12).2.2 I C).1
  have hmodel := five h K hf ⟨eK⟩ I C
  have hfactor := Diagonal.point_radical_eq_component_sylow_sup_core A K T
    hTA hAK hTK hp hc hout hgen eK
  have hIR : I ≤ (A ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [hfactor]
    exact (le_inf C.le_sylow C.le_component).trans le_sup_left
  exact Diagonal.baumann_eq_of_a5_radical_factor K I _ T hTK C.le_component hIR
    (sup_le C.normalizes hTI) hmodel hfactor

/-- Escape of the selected component forces the normalizer escape on printed
p.893, using the same point radical as original 13.3.10(2). -/
theorem unitary_baumann_escape_of_selected_five
    {T : Sylow 2 G} {L : Subgroup G} (h : Hypothesis1331 T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (five : OriginalAlternatingFiveModules1332At T L)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K A : Subgroup G) (hf : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hAK : A ≤ normalizer (K : Set G)) (hp : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hout : ¬ A ≤ K) (hgen : ⁅K,A⁆ = K)
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    ¬ normalizer (ChapterB.baumann ((A ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) ≤
      normalizer (L : Set G) := by
  have hB := unitary_baumann_identity_of_selected_five h structural five h1332
    K A hf eK hTA hAK hp hc hout hgen
  rw [hB]
  apply fun hn => hKM (le_trans ?_ hn)
  exact (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left).trans
    (((K ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))).trans
      (Stellmacher.normalizer_le_normalizer_baumann _))
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
