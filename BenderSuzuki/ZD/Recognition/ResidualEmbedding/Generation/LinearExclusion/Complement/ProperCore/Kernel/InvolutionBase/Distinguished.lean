module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.LinearBorel

/-!
# The distinguished closure inside the source two-core

The actual PSL₂ Borel marking makes `A = ⟨Z ∩ M⟩` elementary abelian of
order `2^n`. Transport that statement into `M`. Each distinguished generator
is central in a Sylow two-subgroup contained in `M`; the normal two-core lies
in this Sylow subgroup. Thus `A` centralizes `O₂(M)`.

These facts supply the central square-one layer for the involution-base
counting argument. Neither containment in `[R,K]` nor any involution census
is asserted here. Source: GLS, Volume 4, Chapter 2, Lemma 15.2(h) and the
last paragraph of Lemma 15.6, `refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

/-- The distinguished `Z`-closure, viewed inside `M`, has square one,
centralizes the two-core, and has the order of the genuine PSL₂ root group. -/
public theorem linear_distinguishedClosure_internal_facts {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    (∀ a ∈ (closure (Z ∩ (M : Set G))).subgroupOf M, a ^ 2 = 1) ∧
      (closure (Z ∩ (M : Set G))).subgroupOf M ≤ centralizer (pCore 2 M : Set M) ∧
      Nat.card ((closure (Z ∩ (M : Set G))).subgroupOf M) = 2 ^ n := by
  let A := closure (Z ∩ (M : Set G))
  obtain ⟨hAe, hAc⟩ := psl2_distinguishedClosure_elementary_card
    h r hz hzM ht htM hL ⟨e⟩ hn hAL
  let : IsElementaryAbelian 2 A := hAe
  have hcent : A ≤ (centralizer (pCore 2 M : Set M)).map M.subtype := by
    apply (closure_le _).mpr
    intro a ha
    refine ⟨⟨a, ha.2⟩, ?_, rfl⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨S, _, hS⟩ := r.two_central a ha.1
    have hSM : (S : Subgroup G) ≤ M := by
      intro s hs
      exact mem_of_commute h ha.1 ha.2 (hS ⟨s, hs⟩)
    have hcore : pCore 2 M ≤ (S.subtype hSM : Subgroup M) :=
      IsPGroup.le_sylow_of_normal pCore_isPGroup (S.subtype hSM)
    apply Subtype.ext
    exact (hS ⟨v, hcore hv⟩).eq.symm
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
  · intro a ha
    obtain ⟨b, hb, he⟩ := hcent ha
    have hba : b = a := Subtype.ext he
    exact hba ▸ hb
  · exact (Nat.card_congr (subgroupOfEquivOfLe
      (distinguishedClosure_le (Z := Z) (M := M))).toEquiv).trans hAc
end BenderSuzuki.ZD
