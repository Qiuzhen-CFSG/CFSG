module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.LinearOvergroups
public import Theory.GroupTheory.PResidual.FiniteImage
public import FeitThompson.FinalTheorem

/-!
# The odd residual in the Ree local argument

Burnside transfer makes the two-residual odd when the Sylow two-subgroup is
cyclic. The checked odd-order theorem supplies solvability of that residual;
solvability of the ambient group is not a hypothesis. The existing binary
four-space calculation then gives a cyclic group of order fifteen, with its
regular action on the supplied group of order sixteen.

Residuals are transported by the literal quotient maps. In particular the
image of O²(Mc) in Mc/Q is used without requiring Q ≤ O²(Mc), a containment
which fails already in the actual full-Ree first parabolic.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.989.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity

/-- The source's residual modulo Q is its image, computed by surjective transport. -/
public theorem residual_quotient_image {M : Type*} [Group M] [Finite M]
    (Q : Subgroup M) [Q.Normal] :
    (pResidual 2 M).map (QuotientGroup.mk' Q) = pResidual 2 (M ⧸ Q) :=
  Subgroup.map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective Q)

/-- The corresponding image for the embedded local residual uses the same quotient map. -/
public theorem embedded_residual_quotient_image
    {H M : Type*} [Group H] [Finite H] [Group M]
    (QH : Subgroup H) [QH.Normal] (Q : Subgroup M) [Q.Normal]
    (i : H →* M) (hQ : QH ≤ Q.comap i) :
    ((pResidual 2 H).map i).map (QuotientGroup.mk' Q) =
      (pResidual 2 (H ⧸ QH)).map (QuotientGroup.map QH Q i hQ) := by
  rw [← residual_quotient_image QH, Subgroup.map_map, Subgroup.map_map]
  rfl

/-- No solvability assumption on M is needed: it is proved for the odd residual.
The action remains the supplied faithful action, restricted to the literal residual. -/
public theorem cyclic_fifteen_regular
    {M V : Type*} [Group M] [Finite M]
    [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (T : Sylow 2 M) (hT : IsCyclic T)
    (ρ : M →* MulAut V) (hρ : Function.Injective ρ)
    (hV : Nat.card V = 16)
    (K : Subgroup (pResidual 2 M)) (hK : Nat.card K = 5) (hproper : K < ⊤) :
    Nat.card (pResidual 2 M) = 15 ∧ IsCyclic (pResidual 2 M) ∧
      ∀ x y : V, x ≠ 1 → y ≠ 1 → ∃! a : pResidual 2 M, ρ a x = y := by
  have hodd := T.odd_card_twoResidual_of_isCyclic hT
  let σ := ρ.comp (pResidual 2 M).subtype
  have hσ : Function.Injective σ := hρ.comp Subtype.val_injective
  have hsolv := odd_order_theorem (pResidual 2 M) hodd
  obtain ⟨hcard, hcyc⟩ := Theory.GroupAction.cyclic_fifteen_of_odd_binary_four_five_lt_top
    hsolv σ hσ hodd hV K hK hproper
  let := hcyc
  exact ⟨hcard, hcyc, Theory.GroupAction.faithful_cyclic_fifteen_regular σ hσ hcard hV⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
