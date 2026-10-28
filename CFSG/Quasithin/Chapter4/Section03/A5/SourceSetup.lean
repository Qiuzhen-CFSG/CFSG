module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28
/-!
# The original A₅ context enters the source proof of 4.3.2

The actual A₅ action supplies the quasisimple two-core quotient, and the
proved local maximality and uniqueness over LT give the genuine normalized
pushing-up hypothesis 4.1.1. If uniqueness over L fails, the existing maximal
counterexample construction produces C.2.8. Starting with I=L forces the
selected overgroup to contain this same L; its perfect residual is therefore
literally L. The same conjugator transports the original chosen module into
the full omega-center module, with its section-Sylow identity retained.

This is the source entry to 4.3.2, not the uniqueness conclusion. The
subsequent C.3/C.4 model analysis and 4.3.3–7 contradictions remain separate.
Source: Aschbacher–Smith 4.2.1–4 and 4.2.12, printed pp.608–611, and the
opening proof of 4.3.2, printed p.613 (`refs/quasithin.pdf`).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Chapter1.Section02 Chapter1.Section02.Adequate Chapter4
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The original context satisfies the genuine normalized Section 12.2 hypotheses. -/
theorem section1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L := by
  refine ⟨d.hypothesis.qtke,⟨d.maximal_local,?_⟩,?_⟩
  · exact ((mem_faithfulLocalComponents_iff T L).mp d.hypothesis.local_component).2
  · exact IsQuasisimple.of_mulEquiv d.quotient.symm

/-- The genuine 1.2.7 source makes N(L) a maximal two-local. -/
theorem normalizer_maximal_twoLocal : IsMaximalTwoLocal (normalizer (L : Set G)) := by
  have hu := nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    d.hypothesis.qtke T d.maximal_local
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    apply iSup_le
    intro t
    exact (mem_normalizer_iff_map_conj_eq.mp (d.normalizes_L t.property)).le
  simpa only [horbit] using hu.normalizer_maximal

/-- The available uniqueness is over the original Sylow join LT. -/
theorem source_unique_sylow_join : UniqueMaximalOvergroup
    (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
  ⟨d.normalizer_maximal_twoLocal, sup_le L.le_normalizer d.normalizes_L,
    d.unique_maximal_overgroup⟩

/-- Original normalized pushing-up hypotheses, without uniqueness over L. -/
theorem source_hypothesis411 : Hypothesis411 KnownSimple.IsKnownSimple T
    (normalizer (L : Set G)) L :=
  Chapter4.source_hypothesis411 d.section1221 d.source_unique_sylow_join

/-- The original chosen module lies in the nontrivial two-core of L. -/
theorem source_core_nontrivial : L.pCoreIn 2 ≠ ⊥ := by
  intro he
  exact d.chosen.ne_bot (bot_unique (d.chosen.le_componentCore.trans_eq he))

/-- Failure of uniqueness produces C.2.8 on the same L and the actual full module. -/
theorem source_C28_of_not_unique
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L L) ∧
      L ≤ J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ H ⊓ normalizer (L : Set G) < H ∧
      J.pCoreIn 2 ≤ (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        L (J.pCoreIn 2)
        (Section02.Unitary.fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤
          Section02.Unitary.fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) := by
  have hcover : (L : Set G) ⊆ (L : Set G) * (L.pCoreIn 2 : Set G) := by
    intro x hx
    exact ⟨x, hx, 1, one_mem _, mul_one x⟩
  obtain ⟨J,H,S,hJ,hLJ,hH,hJH,hout,hlt,hRS,hC,hm⟩ :=
    Section02.Unitary.exists_source_C28_of_not_unique d.section1221 d.chosen
      d.source_unique_sylow_join L.le_normalizer hcover d.source_core_nontrivial hnot
  have hLJ' : L ≤ J := by
    intro x hx
    exact (hLJ.2 ⟨hx,hx⟩).1
  have hLH := hLJ'.trans hJH
  have he : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype = L := by
    rw [inf_eq_left.mpr hLH]
    let := d.perfect
    rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  rw [he] at hC
  exact ⟨J,H,S,hJ,hLJ',hH,hJH,hout,hlt,hRS,hC,hm⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
