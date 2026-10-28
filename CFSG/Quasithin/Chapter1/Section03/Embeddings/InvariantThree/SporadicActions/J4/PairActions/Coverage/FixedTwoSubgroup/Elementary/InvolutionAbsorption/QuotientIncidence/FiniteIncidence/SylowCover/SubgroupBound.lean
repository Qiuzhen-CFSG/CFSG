module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover.WordActions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover.SubgroupData

/-!
# A certified 256-element subgroup lower bound

The finite check validates distinct sorted pairs using a left inverse and
validates every edge using the four certified generator matrices. The orbit tree stays inside the fixed generated subgroup.
The soundness lemmas in Core transfer these checks to actual group elements.
See source/README.md and source/generate.py for witness provenance.
-/

@[expose] public section
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.QuotientOrderCertificate

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.SylowCover.SubgroupBound
open SubgroupData
attribute [local irreducible] Janko4.modelGroup quotientSubgroup baseSubgroup

set_option maxRecDepth 100000 in
private theorem checked : ∀ i : Fin 256,
    (codes i).1.toNat ≤ (codes i).2.toNat ∧
    index (key (codes i)) = i ∧
    (i ≠ 0 → parent i < i ∧ Step (codes (parent i)) (codes i) (sylowRows (letter i))) := by
  apply forall_fin_of_range
  decide +kernel

theorem distinct : Function.Injective (fun i => point (codes i)) :=
  points_injective codes (fun i => (checked i).1)
    (Function.LeftInverse.injective (fun i => (checked i).2.1))

theorem lower_bound : 256 ≤ Nat.card baseSubgroup := by
  apply orbit_lower (fun i => point (codes i)) parent letter
    (fun i hi => ((checked i).2.2 hi).1) _ distinct
  intro i hi
  exact step_sound (codes (parent i)) (codes i) (sylowGenerator (letter i))
    (sylowRows (letter i)) (sylowGenerator_val _) ((checked i).2.2 hi).2

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.SylowCover.SubgroupBound
