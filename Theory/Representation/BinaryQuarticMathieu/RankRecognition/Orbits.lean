module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Data
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits.Tree
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Orbits.Preservers

/-!
# Quartic-preserving transports for every binary vector

The two literal invertible maps preserve the actual determinant-sum quartic.
The checked tree in `Orbits/Tree.lean` connects each of the 1024 words to the
representative of its published class. Induction on its strictly decreasing
depth composes the maps to give the required transport. Every root, label and
edge is checked against `source/orbit-witnesses.json`; that file is only a
source of witnesses, not an assumption. No histogram, group order, full
stabilizer identification, Mathieu recognition or J4 hypothesis is used.
-/

public section

namespace BinaryQuarticMathieu.RankRecognition
open Orbits
attribute [local irreducible] quartic
/-- Every word is the image of its class representative under an actual
invertible linear map preserving the published quartic. -/
theorem orbit_transport (n : Word) : ∃ g : U ≃ₗ[F] U,
    Preserves quartic g ∧ g (decode (representative (wordClass n))) = decode n := by
  have hg (n : Word) : Preserves quartic (treeGenerator n) := by
    unfold treeGenerator
    split
    · exact generatorB_preserves
    · exact generatorA_preserves
  suffices hh : ∀ d, ∀ n : Word, (treeRow n).depth = d →
      ∃ g : U ≃ₗ[F] U, Preserves quartic g ∧
        g (decode (representative (wordClass n))) = decode n by
    exact hh _ n rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n hn
    by_cases hz : (treeRow n).depth = 0
    · refine ⟨LinearEquiv.refl F U, preserves_refl quartic, ?_⟩
      change decode (representative (wordClass n)) = decode n
      rw [← tree_labels n, ← tree_roots n hz]
    · obtain ⟨hd, hc⟩ := tree_descent n hz
      obtain ⟨g, hgp, hgv⟩ := ih _ (by simpa [hn] using hd) (treeRow n).parent rfl
      refine ⟨g.trans (treeGenerator n), hgp.trans (hg n), ?_⟩
      change treeGenerator n (g (decode (representative (wordClass n)))) = decode n
      rw [← hc, hgv]
      exact tree_edges n hz
end BinaryQuarticMathieu.RankRecognition
