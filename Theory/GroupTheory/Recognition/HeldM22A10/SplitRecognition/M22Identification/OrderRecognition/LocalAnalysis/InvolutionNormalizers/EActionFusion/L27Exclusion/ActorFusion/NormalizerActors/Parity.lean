module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.CoordinateImage
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.Nonfusion

/-!
# Parity preserved by the order-168 normalizer

The eight odd vectors are already one orbit under the local twisted S₄.
The full normalizer orbit also has size eight, so these sets agree. Thus
its faithful binary action preserves parity and the even eight-group.
The action below is the literal conjugation action in the given coordinates.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.6.
-/

open Subgroup
open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy

namespace L27NormalizerActors
/-- The parity of a binary vector in the original four coordinates. -/
@[expose] public def parity (v : BinaryFour) : ZMod 2 := ∑ i, v.toAdd i

/-- The invariant eight-group, before transport to the ambient group. -/
@[expose] public def evenSpace : Subgroup BinaryFour where
  carrier := {v | parity v = 0}
  one_mem' := by decide +kernel
  mul_mem' := by
    have h : ∀ v w : BinaryFour, parity v = 0 → parity w = 0 → parity (v * w) = 0 := by
      decide +kernel
    exact h
  inv_mem' := by
    have h : ∀ v : BinaryFour, parity v = 0 → parity v⁻¹ = 0 := by decide +kernel
    exact h

private theorem odd_card : ({v : BinaryFour | parity v = 1} : Set BinaryFour).ncard = 8 := by
  change Nat.card {v : BinaryFour // parity v = 1} = 8
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem odd_local_orbit : ∀ v : BinaryFour, parity v = 1 →
    ∃ s : SymmetricFour, twistedAction s (z 1).left = v := by
  decide +kernel

public theorem parity_cases (v : BinaryFour) : parity v = 0 ∨ parity v = 1 := by
  have h : ∀ v : BinaryFour, parity v = 0 ∨ parity v = 1 := by decide +kernel
  exact h v
end L27NormalizerActors

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Conjugation by the actual normalizer, expressed in binary coordinates. -/
@[expose] public noncomputable def eNormalizerBinaryAction :
    normalizer (E D k : Set G) →* MulAut BinaryFour :=
  (MulAut.congr (eBinaryEquiv D k).symm).toMonoidHom.comp (E D k).normalizerMonoidHom

omit [Finite G] in
public theorem eNormalizerBinaryAction_apply
    (n : normalizer (E D k : Set G)) (v : BinaryFour) :
    (eBinaryEquiv D k (eNormalizerBinaryAction D k n v) : G) =
      (n : G) * (eBinaryEquiv D k v : G) * (n : G)⁻¹ := by
  change (eBinaryEquiv D k ((eBinaryEquiv D k).symm
    ((E D k).normalizerMonoidHom n (eBinaryEquiv D k v))) : G) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

omit [Finite G] in
public theorem eNormalizerBinaryAction_range :
    (eNormalizerBinaryAction D k).range = eNormalizerBinaryImage D k :=
  MonoidHom.range_comp _ _

omit [Finite G] in
public theorem eNormalizerBinaryAction_local (s : SymmetricFour) :
    eNormalizerBinaryAction D k
      ⟨into D k (SemidirectProduct.inr s),
        centralizer_le_normalizer_E D k (k (SemidirectProduct.inr s)).property⟩ =
      twistedAction s := by
  apply MulEquiv.ext
  intro v
  apply (eBinaryEquiv D k).injective
  apply Subtype.ext
  rw [eNormalizerBinaryAction_apply, eBinaryEquiv_coe, eBinaryEquiv_coe]
  rw [SemidirectProduct.inl_aut, map_mul, map_mul, ← map_inv, ← map_inv]

private theorem odd_image_eq_orbit
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    (eBinaryEquiv D k) '' {v | L27NormalizerActors.parity v = 1} =
      MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerZOnePoint D k) := by
  apply Set.eq_of_subset_of_ncard_le _ _ (Set.toFinite _)
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨s, rfl⟩ := L27NormalizerActors.odd_local_orbit v hv
    let n : normalizer (E D k : Set G) :=
      ⟨into D k (SemidirectProduct.inr s),
        centralizer_le_normalizer_E D k (k (SemidirectProduct.inr s)).property⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨n, ?_⟩
    apply Subtype.ext
    change (n : G) * into D k (z 1) * (n : G)⁻¹ = _
    rw [← eNormalizerBinaryAction_local D k s]
    rw [eNormalizerBinaryAction_apply]
    rfl
  · rw [Set.ncard_image_of_injective _ (eBinaryEquiv D k).injective,
      L27NormalizerActors.odd_card, eNormalizerZOnePoint_orbit_card_of_168 D k h168]

/-- In the order-168 branch the actual action preserves coordinate parity. -/
public theorem eNormalizerBinaryAction_parity_of_168
    (h168 : Nat.card (eNormalizerQuotient D k) = 168)
    (n : normalizer (E D k : Set G)) (v : BinaryFour) :
    L27NormalizerActors.parity (eNormalizerBinaryAction D k n v) =
      L27NormalizerActors.parity v := by
  have hodd : ∀ (m : normalizer (E D k : Set G)) (w : BinaryFour),
      L27NormalizerActors.parity w = 1 →
      L27NormalizerActors.parity (eNormalizerBinaryAction D k m w) = 1 := by
    intro m w hw
    have hwO : eBinaryEquiv D k w ∈
        MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerZOnePoint D k) := by
      rw [← odd_image_eq_orbit D k h168]
      exact ⟨w, hw, rfl⟩
    have hm := MulAction.mem_orbit_of_mem_orbit m hwO
    have he : m • eBinaryEquiv D k w =
        eBinaryEquiv D k (eNormalizerBinaryAction D k m w) := by
      apply Subtype.ext
      exact (eNormalizerBinaryAction_apply D k m w).symm
    rw [he, ← odd_image_eq_orbit D k h168] at hm
    obtain ⟨w', hw', he'⟩ := hm
    exact (eBinaryEquiv D k).injective he' ▸ hw'
  rcases L27NormalizerActors.parity_cases v with hv | hv
  · rcases L27NormalizerActors.parity_cases (eNormalizerBinaryAction D k n v) with h | h
    · exact h.trans hv.symm
    · have hi := hodd n⁻¹ (eNormalizerBinaryAction D k n v) h
      rw [map_inv, MulAut.inv_apply_self, hv] at hi
      exact (zero_ne_one hi).elim
  · exact (hodd n v hv).trans hv.symm

/-- Every element of the faithful image preserves the even eight-group. -/
public theorem eNormalizerBinaryImage_parity_of_168
    (h168 : Nat.card (eNormalizerQuotient D k) = 168)
    (f : eNormalizerBinaryImage D k) (v : BinaryFour) :
    L27NormalizerActors.parity (f.val v) = L27NormalizerActors.parity v := by
  have hf : f.val ∈ (eNormalizerBinaryAction D k).range := by
    simpa only [eNormalizerBinaryAction_range D k] using f.property
  obtain ⟨n, hn⟩ := hf
  rw [← hn]
  exact eNormalizerBinaryAction_parity_of_168 D k h168 n v

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
