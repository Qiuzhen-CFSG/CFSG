module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.LinearThree
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Source1331

/-!
# The PSL₃ exclusion for the original 13.3.1 counterexample

Select the same genuine maximal nonquasisimple overgroup as in the 13.3.2
source reduction. For any involution and full centralizer action satisfying
the preceding orbit/action inputs, its canonical odd radical cannot have
its two-core equal to the full unipotent subgroup of a marked PSL₃ component
containing that radical. The Borel placement and complement irreducibility
are proved by the preceding source adapter.

The original 13.1.10 markings and the component sieve must still construct
the remaining model data, and other component rows remain separate.
Source: Aschbacher–Smith, 13.3.2, printed p.884, using 13.1.12, p.875.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceCentralizerComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The maximal counterexample selected by the actual source 3.1.8 theorem
excludes the marked PSL₃ full-unipotent row of the later component sieve. -/
theorem Hypothesis1331.nonquasisimple_linearThree_unipotent_exclusion
    (h : Hypothesis1331 T L₀) (h318 : Chapter3.SourceTheorem318One G)
    (hn0 : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ L ∈ LStar G T, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      L ∈ nonquasisimpleFaithful T ∧
      ∀ {p : ℕ} [Fact p.Prime]
        (_ho : Odd p) (_hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
        (u : G)
        (_hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
        (_hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
          (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
            ∀ a ∈ A, xiFrattiniAction
              (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
              (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤)
        (F : Type*) [Field F] [Finite F] [CharP F 2]
        {n : ℕ} (_hF : Nat.card F = 2 ^ n)
        (K : Subgroup G) (_hXK : XiP p L ≤ K) (e : K ≃* PSL(3,F)),
        (((XiP p L).pCoreIn 2).subgroupOf K).map e.toMonoidHom ≠ unipotent F := by
  obtain ⟨L,hL,hL0,hf,hn,_⟩ := h.nonquasisimple_centralizer_structure h318 hn0
  refine ⟨L,hL,hL0,hf,hn,?_⟩
  intro p hp ho hd u hXMu hirr F hField hFinite hChar n hF K hXK e hA
  exact source_centralizer_linearThree_unipotent_row_excluded h.qtke T hL hn.2 ho hd
    u hXMu hirr F hF K hXK e hA

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
