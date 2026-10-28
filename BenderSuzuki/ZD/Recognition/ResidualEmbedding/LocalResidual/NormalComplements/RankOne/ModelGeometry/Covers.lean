module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import BenderSuzuki.SE.Section11Lemma114Models

/-!
# The linear and Suzuki odd central covers

A perfect odd central extension of either family has trivial center: its
quotient has cyclic Sylow subgroups at every odd prime, and transfer kills
the odd central kernel. The resulting equivalence identifies the covering
group itself with the original matrix model, preserving its parameter.

The unitary case does not satisfy this cyclic-Sylow argument. Its special
unitary cover must be retained separately.
Source: GLS, Volume 4, Chapter 4, Lemma 2.8(a).
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- A perfect odd central cover of binary PSL₂ is the same linear model. -/
public theorem linear_oddCentralCover {n : ℕ} (hn : 2 ≤ n)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (e : (G ⧸ center G) ≃* PSL2BinaryMatrixGroup n) :
    center G = ⊥ ∧ Nonempty (G ≃* PSL2BinaryMatrixGroup n) := by
  have hbot : center G = ⊥ := lemma114_oddCentralCover_eq_bot hperfect (center G)
    rfl hodd (fun p _ hp P => lemma114_psl2_oddSylow_isCyclic_of_equiv hn e p hp P)
  let f : (G ⧸ center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨hbot, ⟨f.symm.trans e⟩⟩

/-- A perfect odd central cover of Suzuki is the same Suzuki model.
The source exponent remains `2*m+1`, and `m ≥ 1` is retained. -/
public theorem suzuki_oddCentralCover (m : ℕ) (_hm : 1 ≤ m)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (e : (G ⧸ center G) ≃* SuzukiMatrixGroup m) :
    center G = ⊥ ∧ Nonempty (G ≃* SuzukiMatrixGroup m) := by
  have hbot : center G = ⊥ := lemma114_oddCentralCover_eq_bot hperfect (center G)
    rfl hodd (fun p _ hp P => lemma114_suzuki_oddSylow_isCyclic_of_equiv e p hp P)
  let f : (G ⧸ center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨hbot, ⟨f.symm.trans e⟩⟩

end BenderSuzuki.ZD.RankOneModelGeometry
