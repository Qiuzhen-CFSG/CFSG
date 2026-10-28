module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.Transporters

/-!
# The actual normalizer action in Case II coordinates

Conjugation of N(E) on its actual E has kernel E, by the self-centralizing
hypothesis. Hence its restriction to any actual complement is faithful.
The complement supplied by local analysis also gives |N(E)| = 5760.
The coordinate map identifies E with the binary four-space, and the actors
inside the involution centralizer act by the specified parity-twisted S4
representation. These facts retain the marking supplied by k.

This does not identify an arbitrary extension with an unspecified semidirect
product or construct its characters. The remaining character-table proof must
use this actual action and the actual A6 complement.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 2–6, especially Lemma 6 and pp.10–11.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)

/-- Conjugation on the actual elementary subgroup. -/
@[expose] public def normalizerConjugation :
    normalizer (CaseII.E D k : Set G) →* MulAut (CaseII.E D k) :=
  (CaseII.E D k).normalizerMonoidHom

public theorem normalizerConjugation_apply
    (g : normalizer (CaseII.E D k : Set G)) (v : CaseII.E D k) :
    (normalizerConjugation D k g v : G) = (g : G) * (v : G) * (g : G)⁻¹ := rfl

/-- Self-centralization makes E exactly the action kernel. -/
public theorem normalizerConjugation_ker (L : LocalAnalysisData D k) :
    (normalizerConjugation D k).ker =
      (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) := by
  rw [normalizerConjugation, normalizerMonoidHom_ker, L.E_centralizer]

/-- Every genuine complement acts faithfully on E. -/
public theorem normalizerComplement_action_injective (L : LocalAnalysisData D k)
    (K : Subgroup (normalizer (CaseII.E D k : Set G)))
    (hK : ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K) :
    Function.Injective ((normalizerConjugation D k).comp K.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply (Subgroup.disjoint_def.mp hK.disjoint) _ x.property
  rw [← normalizerConjugation_ker D k L]
  exact hx

/-- The actual E16 and A6 complement give the normalizer order. -/
public theorem normalizer_E_card (L : LocalAnalysisData D k) :
    Nat.card (normalizer (CaseII.E D k : Set G)) = 5760 := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  have hE : Nat.card ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CaseII.E D k).le_normalizer).toEquiv).trans L.E_card
  have hC : Nat.card K = 360 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    norm_num
  rw [← hK.card_mul_card, hE, hC]

/-- The original binary coordinates as elements of E. -/
@[expose] public def normalizerVector : BinaryFour →* CaseII.E D k :=
  ((CaseII.into D k).comp (SemidirectProduct.inl : BinaryFour →* TwistedModel)).rangeRestrict

/-- The coordinate inclusion is a bijection onto the actual E. -/
public theorem normalizerVector_bijective : Function.Bijective (normalizerVector D k) := by
  constructor
  · intro v w h
    have hv : CaseII.into D k (SemidirectProduct.inl v) =
        CaseII.into D k (SemidirectProduct.inl w) :=
      congrArg (fun x : CaseII.E D k => (x : G)) h
    exact SemidirectProduct.inl_injective (CaseII.into_injective D k hv)
  · rintro ⟨x, v, rfl⟩
    exact ⟨v, rfl⟩

/-- The marked binary-space equivalence onto E. -/
@[expose] public def normalizerVectorEquiv : BinaryFour ≃* CaseII.E D k :=
  MulEquiv.ofBijective (normalizerVector D k) (normalizerVector_bijective D k)

/-- The original S4 actors as elements of the actual normalizer. -/
@[expose] public def normalizerActor :
    SymmetricFour →* normalizer (CaseII.E D k : Set G) :=
  ((CaseII.into D k).comp (SemidirectProduct.inr : SymmetricFour →* TwistedModel)).codRestrict _
    (fun s => centralizer_le_E_normalizer D k (k (SemidirectProduct.inr s)).property)

/-- The normalizer action restricts to the original parity-twisted action. -/
public theorem normalizerConjugation_actor (s : SymmetricFour) (v : BinaryFour) :
    normalizerConjugation D k (normalizerActor D k s) (normalizerVector D k v) =
      normalizerVector D k (twistedAction s v) := by
  apply Subtype.ext
  change CaseII.into D k (SemidirectProduct.inr s) *
    CaseII.into D k (SemidirectProduct.inl v) *
      (CaseII.into D k (SemidirectProduct.inr s))⁻¹ =
        CaseII.into D k (SemidirectProduct.inl (twistedAction s v))
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← SemidirectProduct.inl_aut]

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
