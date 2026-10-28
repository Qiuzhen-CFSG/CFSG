module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.NormalizerActors.BinaryFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion.NormalizerActors.Lifting

/-!
# The actual normalizer actor facts in Janko's order-168 branch

The eight-point orbit makes the even binary hyperplane invariant. Restriction
identifies the actual faithful quotient with GL₃(2), whose involutions form
one class; lifting through E and correcting within Ea conjugates d to a
inside the actual normalizer. Independently, the parity-preserving centralizer
of a has exponent dividing four, so its preimage in N(E) is a two-group.

Neither conclusion assumes ambient actor fusion, a splitting of N(E), an A₆
quotient, or recognition of another involution centralizer. The parent
ActorFusion module owns their use in the ambient fusion argument.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.6.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
private theorem binaryActor_order_two (s : SymmetricFour) (hs : s ^ 2 = 1)
    (hne : twistedAction s (z 1).left ≠ (z 1).left) : orderOf (eNormalizerBinaryActor D k s) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    change twistedAction s ^ 2 = 1
    rw [← map_pow, hs, map_one]
  · intro h
    exact hne (congrArg (fun f : eNormalizerBinaryImage D k => f.val (z 1).left) h)

/-- The marked d and a are conjugate inside the literal N(E) in the
order-168 branch, with the actual ambient conjugation equation. -/
public theorem l27_actor_d_conjugate_a
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    ∃ n : normalizer (E D k : Set G),
      (n : G) * into D k d * (n : G)⁻¹ = into D k a := by
  apply l27_actor_d_conjugate_a_of_binary_isConj D k
  apply L27NormalizerActors.binary_involutions_conjugate
    (eNormalizerBinaryImage D k) (eNormalizerBinaryImage_parity_of_168 D k h168)
    (twistedAction_le_eNormalizerBinaryImage D k)
    ((eNormalizerBinaryImage_card D k).trans h168)
  · exact binaryActor_order_two D k d.right (by decide +kernel) (by decide +kernel)
  · exact binaryActor_order_two D k a.right (by decide +kernel) (by decide +kernel)

/-- Both local inputs to the parent's order-168 actor-fusion argument,
under exactly the numerical branch hypothesis. -/
public theorem l27_normalizer_actor_inputs
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    IsPGroup 2 ↥(centralizer ({into D k a} : Set G) ⊓ normalizer (E D k : Set G)) ∧
    ∃ n : normalizer (E D k : Set G),
      (n : G) * into D k d * (n : G)⁻¹ = into D k a :=
  ⟨l27_actor_normalizer_centralizer_isPGroup D k h168, l27_actor_d_conjugate_a D k h168⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
