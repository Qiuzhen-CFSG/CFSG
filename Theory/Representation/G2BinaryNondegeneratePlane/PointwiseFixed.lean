module
public import Theory.Representation.G2BinaryNondegeneratePlane.Stabilizer

/-!
# Fixed vectors of the pointwise nondegenerate-plane stabilizer

Every nonidentity element of the pointwise S₃ stabilizer fixes at most
sixteen vectors of the binary six-space. The actual SL₂ marking reduces
this to six matrices acting on two natural summands and two trivial lines.
The checked finite calculation is restricted to those six matrices and
sixty-four vectors.

This bound supplies Thompson containment in the original plane centralizer
in Aschbacher--Smith 13.3.12, printed p.889.
-/

public section
open scoped MatrixGroups
namespace Atlas.G2.Natural.BinaryNondegeneratePlane

private def firstAction (M : SL(2,K)) (v : W) : W :=
  ![v 0, M.val 0 0*v 1+M.val 0 1*v 2, M.val 1 0*v 1+M.val 1 1*v 2,
    M.val 0 0*v 3+M.val 0 1*v 4, M.val 1 0*v 3+M.val 1 1*v 4, v 5]

private theorem firstAction_fixed_card : ∀ M : SL(2,K), M ≠ 1 →
    Fintype.card {v : W // firstAction M v = v} ≤ 16 := by
  decide +kernel

theorem pointwise_nontrivial_fixed_card
    (g : Representation.BinaryOffender.subspaceKernel rho plane ⊤) (hg : g ≠ 1) :
    Nat.card {v : W // rho g.val v = v} ≤ 16 := by
  let M := Atlas.G2.PairStabilizer.fixingPairEquivSL2
    (MulEquiv.subgroupCongr pointwise_plane_eq_pair g)
  have hM : Atlas.G2.PairStabilizer.blockHom M = g.val :=
    congrArg Subtype.val (Atlas.G2.PairStabilizer.fixingPairEquivSL2.symm_apply_apply
      (MulEquiv.subgroupCongr pointwise_plane_eq_pair g))
  have hm : M ≠ 1 := by
    intro he
    apply hg
    apply Subtype.ext
    rw [← hM, he, map_one]
    rfl
  rw [← hM]
  have ha : (fun v : W => rho (Atlas.G2.PairStabilizer.blockHom M) v) = firstAction M := by
    funext v
    exact firstHom_action M v
  simp only [ha, Nat.card_eq_fintype_card]
  exact firstAction_fixed_card M hm

end Atlas.G2.Natural.BinaryNondegeneratePlane
