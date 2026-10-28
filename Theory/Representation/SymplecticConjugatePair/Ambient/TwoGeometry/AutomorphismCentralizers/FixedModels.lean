module

public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers.RankTransfer
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification
public import Theory.SpecificGroups.Suzuki.TwoRank
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Sharp ranks of the standard symplectic fixed groups

Field descent identifies the half-Frobenius fixed group with Sp₄ over the
half-size field. Graph descent identifies the full fixed group with the actual
Suzuki matrices, including Sz(2). At the binary endpoint the distinguished
order-four root subgroup is Sylow, so its two-rank is at most one.

Source: Aschbacher–Smith H.7 and 16.1.4, printed pp.389 and 1170–1173.
The full fixed groups here are not replaced by their derived subgroups.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace SymplecticConjugatePair.Ambient.AutomorphismCentralizers

open BenderSuzuki.MatrixGroups

/-- The binary Suzuki endpoint has a cyclic Sylow two-subgroup. -/
theorem suzuki_zero_rank_le_one : primeRank 2 (SuzukiMatrixGroup 0) ≤ 1 := by
  let R := zpowers suzukiZeroRootGenerator
  have hc : Nat.card R = 2 ^ 2 := by
    rw [Nat.card_zpowers, suzukiZeroRootGenerator_order]
    rfl
  have hp : IsPGroup 2 R := IsPGroup.of_card hc
  have hi : ¬ 2 ∣ R.index := by
    have he := R.card_mul_index
    rw [show Nat.card R = 4 from hc, suzukiZero_card] at he
    have : R.index = 5 := by omega
    simp [this]
  apply (hp.toSylow hi).primeRank_le_one_of_isCyclic
  change IsCyclic R
  infer_instance

/-- The sharp upper bound includes the non-simple parameter-zero carrier. -/
theorem suzuki_rank_le (m : ℕ) : primeRank 2 (SuzukiMatrixGroup m) ≤ 2 * m + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact suzuki_zero_rank_le_one
  · exact (suzuki_two_rank m hm).le

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Field transport followed by the proved matrix identification supplies the
actual Suzuki equivalence over any coefficient field of the required order. -/
def graph_fixed_equiv (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1)) :
    (ExceptionalGraph.graphAut (F := F) ^ (2 * m + 1)).fixedSubgroup ≃*
      SuzukiMatrixGroup m := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let e := (GaloisField.algEquivGaloisField 2 (2 * m + 1) hF).toRingEquiv
  exact (GraphFieldFixedResidual.fixedFieldEquiv m e).trans
    (GraphFieldFixedResidual.fixedSuzukiEquiv m)

/-- The graph-field fixed group has two-rank at most the field degree. -/
theorem graph_fixed_rank_le {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Odd n) :
    primeRank 2 (ExceptionalGraph.graphAut (F := F) ^ n).fixedSubgroup ≤ n := by
  obtain ⟨m, rfl⟩ := hn
  rw [primeRank_equiv 2 (graph_fixed_equiv m hF)]
  exact suzuki_rank_le m

/-- The half-Frobenius fixed group has the full symplectic rank, including
Sp₄(2) when the original field has four elements. -/
theorem field_fixed_rank {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) (he : Even n) :
    primeRank 2 (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2))).fixedSubgroup =
      3 * (n / 2) := by
  rw [primeRank_equiv 2 (FieldFixedResidual.fixedEquiv _)]
  have heq : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even he).symm
  exact EvenTwoRank.rank
    (FieldFixedResidual.card_halfField (F := F) (by omega) (heq ▸ hF)) (by omega)

end SymplecticConjugatePair.Ambient.AutomorphismCentralizers
