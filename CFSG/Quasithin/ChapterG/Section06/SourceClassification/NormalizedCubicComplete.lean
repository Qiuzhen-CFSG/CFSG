module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.NormalizedCubicReduction
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorExclusion
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Inputs

/-!
# The complete normalized-cubic G.6 source implication

The original G.6 actor with a rank-one involution and a Sylow-normalized cubic
inverted by that same involution is S3 or S7. Complete B.5 source induction
supplies all cases; the quasisimple actor sieve selects S7, the solvable
single-factor case selects S3, and intrinsic permutation plus rank-one
selection excludes the literal two-factor case.

The only remaining universal premises are the genuine earlier A.2, A.3.6 and
corrected B.4 implications for the full known-simple catalogue. The resulting
public source input is exactly the one consumed by the original C.5.12
centralizer-quotient construction. The unrestricted module conclusion of
G.6.4 is a separate statement; this theorem proves its required C.5.12 route.
Source: Aschbacher–Smith, C.5.12, p.163, and G.6.4, pp.345–346.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u v

theorem Hypotheses.actor_models_of_earlier_classification
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {a : G}
    {Cover : Type u} [Group Cover] {q : Cover →* G}
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (S : Sylow 2 G) (c : G) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G)) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 7)) := by
  rcases h.normalized_cubic_source_reduction hA h36 h4 ht S c hc hcne hi hn with hm | hd
  · exact hm
  · obtain ⟨d⟩ := hd
    exact (h.not_two_factors_of_normalized_inverted_cubic ht d S c hcne hi hn).elim

/-- The exact original C.5.12 source input, discharged by the earlier source theorems. -/
theorem normalizedCubicSourceInput_knownSimple_of_earlier_classification
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple) :
    NormalizedCubicSourceInput.{u,v} KnownSimple.IsKnownSimple := by
  apply NormalizedCubicSourceInput.of_forall
  intro G _ V _ _ ρ a Cover _ q h ht S c hc hcne hn hi
  exact h.actor_models_of_earlier_classification hA h36 h4 ht S c hc hcne hi hn
end CFSG.Quasithin.ChapterG.Section06
