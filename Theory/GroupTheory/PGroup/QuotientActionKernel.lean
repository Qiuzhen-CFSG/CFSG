module
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# The kernel of an action on a quotient below the Frattini subgroup

Let B be a finite p-group with an action of P by automorphisms whose
kernel is a p-group. If Z is normal in B and lies in its Frattini subgroup,
then any compatible supplied action on B/Z also has p-group kernel.
The same action and its formula on quotient representatives are retained.

An actor trivial on B/Z acts trivially on B/Φ(B). Its original image
therefore lies in Burnside's Frattini automorphism kernel, a p-group.
Taking its preimage through the original action gives a p-group because
the original kernel is one, and it contains the new quotient kernel.

This standard Burnside basis-kernel transfer identifies the actual
next-stabilizer action kernel in Stellmacher (8.6), source (21), printed
p.45. The graph application supplies self-centralization of the two-core
to control the original conjugation kernel; no graph hypothesis enters here.
-/

namespace MonoidHom
public theorem isPGroup_ker_quotient_action
    {P B : Type*} [Group P] [Group B] [Finite B] {p : ℕ}
    (hB : IsPGroup p B) (action : P →* MulAut B)
    (hkernel : IsPGroup p action.ker)
    (Z : Subgroup B) [Z.Normal] (hZ : Z ≤ frattini B)
    (quotientAction : P →* MulAut (B ⧸ Z))
    (hcompat : ∀ a : P, ∀ b : B,
      quotientAction a (QuotientGroup.mk' Z b) = QuotientGroup.mk' Z (action a b)) :
    IsPGroup p quotientAction.ker := by
  have hpre := (Subgroup.isPGroup_quotientAut_frattini_kernel hB).comap_of_ker_isPGroup
    action hkernel
  apply hpre.to_le
  intro a ha
  change Subgroup.quotientAut (frattini B) (action a) = 1
  apply MulEquiv.ext
  intro b
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini B) b
  rw [Subgroup.quotientAut_apply_mk]
  change QuotientGroup.mk' (frattini B) (action a x) = QuotientGroup.mk' (frattini B) x
  apply QuotientGroup.eq.mpr
  apply hZ
  apply QuotientGroup.eq.mp
  have hfix := congrArg (fun f : MulAut (B ⧸ Z) => f (QuotientGroup.mk' Z x))
    (MonoidHom.mem_ker.mp ha)
  rw [hcompat] at hfix
  exact hfix
end MonoidHom
