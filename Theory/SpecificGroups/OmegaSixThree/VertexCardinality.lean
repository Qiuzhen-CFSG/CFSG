module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.PointCardinality
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.UniquenessSystem
public import Theory.SpecificGroups.ClassicalOrthogonal.D3ExteriorComparison.Projective

/-!
# The order of the actual F.5 vertex stabilizer

The concrete Omega group is the already identified PSL₄(3). Its transitive
orbit on the 117 negative points therefore gives a stabilizer of order 51840.
This count is used only after constructing a faithful marked unitary-extension
homomorphism into that stabilizer.

Source: Aschbacher–Smith F.5.1(1), printed p.300.
-/

public noncomputable section
namespace OmegaSixThree
open OrthogonalityGraph

theorem card_omega : Nat.card omegaPlusSixThree = 6065280 :=
  (Nat.card_congr omegaEquivPSL.toEquiv).trans
    ClassicalOrthogonal.D3ExteriorComparison.psl4_three_card

theorem card_standard_vertex :
    Nat.card (MulAction.stabilizer omegaPlusSixThree standardFirst) = 51840 := by
  let e : MulAction.orbit omegaPlusSixThree standardFirst ≃ Point :=
    Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun a =>
      ⟨⟨a,vertex_transitive a⟩,rfl⟩⟩
  have ho : Nat.card (MulAction.orbit omegaPlusSixThree standardFirst) = 117 :=
    (Nat.card_congr e).trans card_point
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup omegaPlusSixThree standardFirst)
  rw [Nat.card_prod,ho,card_omega] at h
  omega

end OmegaSixThree
