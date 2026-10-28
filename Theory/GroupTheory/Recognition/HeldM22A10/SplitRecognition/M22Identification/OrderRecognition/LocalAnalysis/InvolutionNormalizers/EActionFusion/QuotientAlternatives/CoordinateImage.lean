module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction

/-!
# The quotient as an overgroup of the exact twisted S4 action

The coordinate inclusion identifies the binary four-space with the actual
E. Transporting the faithful conjugation image along this equivalence
realizes N(E)/E as a subgroup of Aut(F₂⁴). The original centralizer's
actor complement maps to the specified parity-twisted S4 action, so its
whole image is contained in this subgroup. Both the quotient equivalence
and the inclusion are constructed from the actual ambient maps.

This isolates the finite linear-group recognition needed in the remaining
order-360 case of Janko's Lemma 6; it assumes no quotient identification.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Case II and Lemma 6, pp.3 and 6.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Coordinates on the actual E, induced by its defining inclusion. -/
@[expose] public noncomputable def eBinaryEquiv : BinaryFour ≃* E D k :=
  MonoidHom.ofInjective ((into_injective D k).comp SemidirectProduct.inl_injective)

omit [Finite G] in
public theorem eBinaryEquiv_coe (v : BinaryFour) :
    (eBinaryEquiv D k v : G) = into D k (SemidirectProduct.inl v) := rfl

/-- The actual conjugation image expressed in binary coordinates. -/
@[expose] public noncomputable def eNormalizerBinaryImage : Subgroup (MulAut BinaryFour) :=
  (E D k).normalizerMonoidHom.range.map (MulAut.congr (eBinaryEquiv D k).symm).toMonoidHom

/-- A faithful realization of the literal quotient in Aut(F₂⁴). -/
public noncomputable def eNormalizerQuotientEquivBinaryImage :
    eNormalizerQuotient D k ≃* eNormalizerBinaryImage D k :=
  (eNormalizerQuotientEquivAction D k).trans
    ((MulAut.congr (eBinaryEquiv D k).symm).subgroupMap _)

public theorem eNormalizerBinaryImage_card :
    Nat.card (eNormalizerBinaryImage D k) = Nat.card (eNormalizerQuotient D k) :=
  (Nat.card_congr (eNormalizerQuotientEquivBinaryImage D k).toEquiv).symm

omit [Finite G] in
public theorem twistedAction_le_eNormalizerBinaryImage :
    twistedAction.range ≤ eNormalizerBinaryImage D k := by
  rintro _ ⟨s, rfl⟩
  let n : normalizer (E D k : Set G) := ⟨into D k (SemidirectProduct.inr s),
    centralizer_le_normalizer_E D k (k (SemidirectProduct.inr s)).property⟩
  refine ⟨(E D k).normalizerMonoidHom n, ⟨n, rfl⟩, ?_⟩
  apply MulEquiv.ext
  intro v
  apply (eBinaryEquiv D k).injective
  apply Subtype.ext
  change (eBinaryEquiv D k
    ((eBinaryEquiv D k).symm ((E D k).normalizerMonoidHom n (eBinaryEquiv D k v))) : G) = _
  rw [MulEquiv.apply_symm_apply, eBinaryEquiv_coe]
  change into D k (SemidirectProduct.inr s) * into D k (SemidirectProduct.inl v) *
    (into D k (SemidirectProduct.inr s))⁻¹ = into D k (SemidirectProduct.inl (twistedAction s v))
  rw [SemidirectProduct.inl_aut, map_mul, map_mul, ← map_inv, ← map_inv]

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
