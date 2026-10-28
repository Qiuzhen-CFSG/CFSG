module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction.Construction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction.CentralizerReduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction.ModelCentralizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction.QuotientCentralizers

/-!
# Assembly of the native Suzuki odd-normalizer action

The conjugation action and all its order and kernel properties are proved
in Construction. ModelCentralizer proves C_D(K) ≤ KJ using the genuine
Suzuki marking, and CentralizerReduction gives C_{N∩D}(K) = KU.
QuotientCentralizers lifts centralizers through M° and S/M° separately.
Together these construct ActionData from the earlier local source inputs,
with no additional action or centralizer premise. The enclosing weak-closure
assembly retains the construction of those inputs and the Fitting argument
needed to finish Lemma 14.9.
Source: GLS4, Chapter 2, Lemma 14.9, refs/KGroup/GLS4/Chapter2.tex.
-/

namespace BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
open Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Assemble the literal action with its independently proved torus centralizers.
The source assembly must discharge both centralizer premises. -/
public theorem actionData_of_torus_centralizers
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g)
    (hcentralizers : ∀ x ∈ torusImage g, x ≠ 1 →
      centralizer ({x} : Set (quotient g)) ≤ normalizer (torusImage g : Set (quotient g)))
    (htorus : centralizer (torusImage g : Set (quotient g)) = torusImage g) :
    Nonempty (ActionData d g) :=
  ⟨{ action := nativeAction d g he
     faithful := nativeAction_faithful d g s hU he
     conjugation := nativeAction_conjugation d g he
     odd := quotient_odd g s
     torus_cyclic := torusImage_cyclic d g s
     torus_card := torusImage_card d g s
     element_centralizers := hcentralizers
     torus_centralizer := htorus }⟩

/-- The faithful literal N_M(S)/S action required in GLS4, Chapter 2,
Lemma 14.9, from the earlier local geometry, semiregularity and embedding.
The model centralizer and both quotient centralizer clauses are discharged
here; the enclosing weak-closure proof supplies these earlier source inputs. -/
public theorem actionData
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g) :
    Nonempty (ActionData d g) := by
  have hambient := normalizer_pair_torus_centralizer d g s f hf hU
  obtain ⟨hcentralizers, htorus⟩ :=
    torusImage_centralizer_clauses d g hsemi s he hambient
  exact actionData_of_torus_centralizers d g s hU he hcentralizers htorus

end BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
