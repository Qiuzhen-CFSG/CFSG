module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.ActionInput
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics

/-!+# Centralization and uniform cases from local recognition

The proper residual model supplies the strict ambient degree bound and the
prime-divisor congruence. The local recognition data supplies the literal
fixed-coset and Thompson mixed-fiber counts. Applying the arithmetic exclusion
to these proved inputs rules out every noncentral field action, giving both
clauses of Lemma 12.9 and the uniform model and degree alternatives.

Only the earlier Lemmas 12.3–12.4 local-recognition data remains explicit.
The numerical witnesses and action input are constructed here, with no
centralization, collapse, or ambient degree premise. The unitary alternative
is retained for the separate Section 13 argument in `UniformCases.Collapse`.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Corollary 7.12 and Lemmas 12.8–12.10.
-/

namespace BenderSuzuki.ZD
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Every involution of the actual pair stabilizer centralizes the proper
residual group. Both the numerical count and the earlier action input of the
noncentral field-action exclusion are discharged from the source hypotheses. -/
public theorem proper_residualGenerated_centralizes_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      v ∈ centralizer (residualGenerated M z t : Set G) :=
  proper_residualGenerated_centralizes_of_numerics h r ha hz hzM ht htM hL heven hlocal
    (proper_residualGenerated_numerics_of_local h r ha hz hzM ht htM hL heven hlocal)
    (proper_residualGenerated_arithmeticInput h r ha hz hzM ht htM hL heven)

/-- Both clauses of GLS4, Chapter 2, Lemma 12.9: a pair-stabilizer involution
centralizes the distinguished closure, and its distinguished centralizer
closure contains `L`. Only the preceding local recognition remains explicit. -/
public theorem proper_residualGenerated_lemma129_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) ∧
        residualGenerated M z t ≤ centralizerClosure Z v :=
  proper_residualGenerated_lemma129_of_numerics h r ha hz hzM ht htM hL heven hlocal
    (proper_residualGenerated_numerics_of_local h r ha hz hzM ht htM hL heven hlocal)
    (proper_residualGenerated_arithmeticInput h r ha hz hzM ht htM hL heven)

/-- The uniform model and degree alternatives of Lemma 12.10, including
the literal fixed-coset counts and the actual unitary cover. The same field
exponent is tied to the distinguished closure and every centralizer model. -/
public theorem proper_residualGenerated_uniform_cases_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n ∧
      ResidualCentralizerCases Z M z t n :=
  proper_residualGenerated_uniform_cases_of_numerics h r ha hz hzM ht htM hL heven hlocal
    (proper_residualGenerated_numerics_of_local h r ha hz hzM ht htM hL heven hlocal)
    (proper_residualGenerated_arithmeticInput h r ha hz hzM ht htM hL heven)

end BenderSuzuki.ZD
