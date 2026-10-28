module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryCovers.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.CentralizingCovers

/-!
# The centralizing-extension conclusion of GLS Lemma 12.3

The odd-center unitary lifting theorem discharges the final covering input
on the actual local quotient. The existing same-parameter recognition and
embedding arguments then retain exactly the projective or special unitary
extension of the original linear subgroup, with the same fixed-field size.

Source: GLS IV, Chapter 2, Lemma 12.3; Chapter 4, Lemmas 2.8(a) and 3.9(a).
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open _root_.BenderSuzuki.MatrixGroups

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- GLS IV, Chapter 2, Lemma 12.3: the unitary-cover source input is now
discharged on the actual centralizer quotient, retaining both PSU₃ and SU₃. -/
public theorem proper_residualGenerated_centralizing_extension
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ∀ v ∈ centralizer (residualGenerated M z t : Set G), v ≠ 1 →
      centralizerClosure Z v = residualGenerated M z t ∨
        ∃ n : ℕ, 2 ≤ n ∧ Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n ∧
          Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup n) ∧
          residualGenerated M z t < centralizerClosure Z v ∧
          IsUnitaryCentralizerCoverAt n (centralizerClosure Z v) := by
  refine proper_residualGenerated_centralizing_extension_of_unitary_covers
    ?_ h r ha hz hzM ht htM hL heven
  intro F _ _ n hn E _ _ J _hJ hcard hfixed hperfect hodd he
  obtain ⟨e⟩ := he
  exact RankOneModelGeometry.unitary_centralCover_alternative_of_odd_center
    J hn hcard hfixed hperfect hodd e

end BenderSuzuki.ZD
