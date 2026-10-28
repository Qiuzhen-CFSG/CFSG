module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Contracts

/-!
# Reduction of Proposition E.6.27 to its two parabolic branches

The finite-group reduction and faithful Cartan transport are proved in the
imported modules. The assembly below consumes actual minimal parabolics of
`O^{2'}(C_G(U))`, the genuine E.1.6 parameter, and the complete E.3.37 witness.
The large branch either supplies a faithful Cartan witness or a nontrivial
odd subgroup whose local normalizer escapes `M`. The two numerical and
odd-local hypotheses of E.6.27 exclude these alternatives.

This is an intermediate assembly, not yet Proposition E.6.27. The source
proof still has to construct the Sylow placement and its normalizer bound
from the higher Thompson hypothesis, apply exact E.6.26 in the small branch,
and derive the Cartan/odd-local alternative from E.2.2 and 4.4.13. Those
obligations must be discharged before exporting the source proposition.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Proposition
E.6.27, printed p.257 (PDF p.268).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

open Subgroup

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual E.6.27 hypotheses rule out the large-parabolic output.
The Cartan alternative remains a construction obligation, not an earlier
source input bundled into the hypotheses of the final proposition. -/
theorem not_large_parabolic_alternative
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U H : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    {j n : ℕ} (hlarge : j < n)
    (hn : nPrime (inducedAutomizer V (M ⊓ centralizer (U : Set G))) ≤ j)
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ M ⊓ centralizer (V : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ M) :
    ¬ ParabolicCartanAlternative V M U H n := by
  rintro (⟨w, _, hfaithful⟩ | ⟨X, hne, hle, ho, hescape⟩)
  · exact hlarge.not_ge ((faithful_cartan_bound
      (h.localCentralizer_le_normalizer hU hUV) w hfaithful).trans hn)
  · exact hescape (inf_le_right.trans (hodd X hne
      (le_inf (hle.trans (inf_le_left.trans inf_le_right))
        (hle.trans inf_le_right)) ho))

/-- A consumer of Sylow promotion, residual generation, the small branch
and the constructed large-parabolic alternative. The source assembly must
prove `hN`, `hsmall`, and `hlarge` from its permitted earlier inputs. -/
theorem centralizer_le_of_parabolic_branches
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (j : ℕ)
    (hn : nPrime (inducedAutomizer V (M ⊓ centralizer (U : Set G))) ≤ j)
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ M ⊓ centralizer (V : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ M)
    (P : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hN : normalizer ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype : Set G) ≤ M)
    (hsmall : ∀ S : Sylow 2 (centralizer (U : Set G)),
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
        (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
          (M ⊓ centralizer (U : Set G)).subtype →
      ∀ H : Subgroup (primeToResidual 2 (centralizer (U : Set G))),
        ChapterB.IsMinimalParabolicOver (residualSylow S) H →
        generationParameter H ≤ j →
        (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype ≤ M)
    (hlarge : ∀ S : Sylow 2 (centralizer (U : Set G)),
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
        (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
          (M ⊓ centralizer (U : Set G)).subtype →
      ∀ H : Subgroup (primeToResidual 2 (centralizer (U : Set G))),
        ChapterB.IsMinimalParabolicOver (residualSylow S) H →
        j < generationParameter H →
        ¬ (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype ≤ M →
        ParabolicCartanAlternative V M U
          ((H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
            (centralizer (U : Set G)).subtype) (generationParameter H)) :
    centralizer (U : Set G) ≤ M := by
  obtain ⟨S, hS⟩ := exists_sylow_of_local_normalizer P hN
  apply le_of_residual_minimalParabolics S (hS ▸ hN)
  intro H hH
  by_cases hsmallH : generationParameter H ≤ j
  · exact hsmall S hS H hH hsmallH
  · by_contra hescape
    have hlargeH := Nat.lt_of_not_ge hsmallH
    exact not_large_parabolic_alternative h hU hUV hlargeH hn hodd
      (hlarge S hS H hH hlargeH hescape)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

end
