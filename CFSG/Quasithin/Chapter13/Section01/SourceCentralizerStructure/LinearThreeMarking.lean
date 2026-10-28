module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.LinearThreeMarking
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Source1331

/-!
# The constructed PSL₃ exclusion at the original 13.3.1 counterexample

The original 3.1.8 source theorem selects the same maximal nonquasisimple
overgroup as the source 13.3.2 reduction and supplies T-normalization.
In the irreducible component-normalizer branch, the literal source local
Sylow and action data now exclude a concrete PSL₃ component without assuming
radical containment or a full-unipotent marking. Both are constructed by
the preceding source theorem. Central covers and the model-recognition
sieve remain separate from this particular concrete row.

Source: Aschbacher–Smith, 13.3.2, p.884, using 13.1.12, pp.874–875.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceCentralizerComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The genuine maximal counterexample excludes the concrete PSL₃ row in
the irreducible component-normalizer branch; all marking premises and the
earlier A/C inputs are discharged. -/
theorem Hypothesis1331.nonquasisimple_linearThree_irreducible_exclusion
    (h : Hypothesis1331 T L₀) (h318 : Chapter3.SourceTheorem318One G)
    (hn0 : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ L ∈ LStar G T, L₀ ≤ L ∧ FaithfulMaximalLocal T L ∧
      L ∈ nonquasisimpleFaithful T ∧
      ∀ {p : ℕ} [Fact p.Prime]
        (_ho : Odd p) (_hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
        (u : G) (_hu : orderOf u = 2)
        (_hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)))
        (_hindex : ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2)
        (_hcentral : ∀ g : G,
          (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
            centralizer ({g * u * g⁻¹} : Set G) ≤ normalizer (L : Set G))
        (_hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
        (K : Subgroup G) (_hK : K ∈ cComponentsIn (centralizer ({u} : Set G)))
        (_hQK : IsQuasisimple (XiQuotient K))
        (_hXnK : XiP p L ≤ normalizer (K : Set G)) (_hmove : ⁅K,XiP p L⁆ = K)
        (_hirrK : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
          (∀ s : ((normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) ⊓
              normalizer (K : Set G) : Subgroup G), ∀ a ∈ A,
            xiFrattiniAction
              ((normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) ⊓ normalizer (K : Set G))
              (XiP p L) (inf_le_left.trans (XiP_invariant p inf_le_left)) s a ∈ A) →
                A=⊥ ∨ A=⊤)
        (F : Type*) [Field F] [Finite F] [CharP F 2]
        {n : ℕ} (_hnF : 2 ≤ n) (_hF : Nat.card F = 2 ^ n),
        ¬ Nonempty (K ≃* PSL(3,F)) := by
  obtain ⟨L,hL,hL0,hf,hn,_,hjoin,_,_⟩ := h.maximal_counterexample_of_source318 h318 hn0
  refine ⟨L,hL,hL0,hf,hn,?_⟩
  intro p hp ho hd u hu hlocal hindex hcentral hXMu K hK hQK hXnK hmove hirrK
    F hField hFinite hChar n hnF hF he
  obtain ⟨e⟩ := he
  exact source_centralizer_linearThree_irreducible_row_excluded h.qtke T hL hn.2
    ho hd u hu (le_sup_right.trans hjoin) hlocal hindex hcentral hXMu
    K hK hQK hXnK hmove hirrK F hnF hF e

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
