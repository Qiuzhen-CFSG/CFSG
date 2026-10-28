module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.ActionReduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.LinearAction.Ambient

/-!
# The binary linear Borel action in E.6.8

For the marked PSL₂(2ⁿ) component, V normalizes L and fixes its marked Sylow
pointwise. The component's escape from M makes this action nontrivial.
The intrinsic matrix and ambient calculations then identify C_V(L ∩ M)
with C_V(L), give the exact displacement order 2ⁿ, and construct the actual
cyclic induced action of order 2ⁿ − 1.

The equality between the Sylow normalizer and L ∩ M is an independent
explicit input. This includes n = 2 conditionally and does not assert that
the source places the PSL₂(4) Borel in M. The rank-one assembly owner supplies
placement before applying the common coprime-action reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1),
printed pp.247–248 (PDF pp.258–259), using the argument of E.6.7 on p.246.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}

/-- The three remaining action clauses of E.6.8(1) for binary PSL₂.
The actual Borel intersection is an explicit independent input. -/
theorem linear_actionCalculation
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : sylowBorel S = L ⊓ M) : ActionCalculation M V L n := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hfix : ∀ v ∈ V, ∀ x : S,
      v * ((x : L) : G) * v⁻¹ = ((x : L) : G) := by
    intro v hv x
    have hx : ((x : L) : G) ∈ L ⊓ sylowCentralizer (T : Subgroup G) V :=
      hS ▸ mem_map_of_mem L.subtype x.property
    rw [(mem_centralizer_iff.mp hx.2.2) v hv]
    simp
  have hne : ¬ V ≤ centralizer (L : Set G) := by
    intro hc
    exact component_not_le h earlier hU hL
      ((le_centralizer_iff.mp hc).trans h.centralizer_le)
  obtain ⟨hf, hd, hc⟩ := LinearAction.intrinsic_action e hq
    (component_normalized_by_V h hU hL) S hfix hB.symm
    (component_intersection_normalizes h hU hL.1) hne
  exact ⟨hf, hd.trans hF, hF ▸ hc⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
