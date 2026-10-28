module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Elementary

/-!
# Comparison of the actual and certified HS point stabilizers

The auxiliary subgroup `OrderCertificate.H1` consists exactly of the elements
of the published HS carrier fixing zero. The level-zero transitions decompose
each element of `H0` as a representative times an element of `H1`. Since the
representatives have distinct images of zero, an element fixing zero has the
identity representative. The checked generator words in `CarrierOrder` already
identify `H0` with the actual ATLAS carrier.

This gives a multiplicative equivalence preserving the underlying permutations
and transfers the certified order 443520 to the actual point stabilizer.
Source: the ATLAS HSG1-p100B0 action retained in `HS.lean`, and the checked chain
in `HS/OrderBound/Level0/{Data,Steps}.lean`. The source context for its use in the
HS outer-automorphism calculation is GLS3, Table 5.3m, printed p.274.
-/

public section
namespace Sporadic.LeechRelated.HS.SmallIndex
open Theory.GroupTheory OrderCertificate

private theorem h0_decomposition (g : Equiv.Perm (Fin 100)) (hg : g ∈ H0) :
    ∃ r : Fin 100, ∃ k : H1, g = rep0 r * (k : Equiv.Perm (Fin 100)) := by
  obtain ⟨w, rfl⟩ := hg
  induction w with
  | nil =>
      exact ⟨0, 1, by simp [evalWord, rep0_base]⟩
  | cons i w ih =>
      obtain ⟨r, k, hk⟩ := ih
      refine ⟨act0 i r,
        ⟨evalWord gen1 (factor0 i r) * (k : Equiv.Perm (Fin 100)),
          H1.mul_mem (evalWord_mem_wordSubgroup gen1 inv1 inv1_spec _) k.property⟩, ?_⟩
      change gen0 i * evalWord gen0 w = _
      rw [hk, ← mul_assoc, step0, mul_assoc]

/-- The certified subgroup consists exactly of the HS permutations fixing zero. -/
theorem certifiedStabilizer_mem_iff {g : Equiv.Perm (Fin 100)} :
    g ∈ OrderCertificate.H1 ↔ g ∈ generated ∧ g 0 = 0 := by
  constructor
  · intro hg
    exact ⟨NormalizerIndex.H0_eq_generated ▸ H1_le hg, next0_fix ⟨g, hg⟩⟩
  · rintro ⟨hg, hfix⟩
    have hg0 : g ∈ H0 := NormalizerIndex.H0_eq_generated.symm ▸ hg
    obtain ⟨r, k, hk⟩ := h0_decomposition g hg0
    have hr : r = 0 := by
      apply point0_injective
      change point0 r = 0
      rw [hk, Equiv.Perm.mul_apply, next0_fix, rep0_point] at hfix
      exact hfix
    rw [hr, rep0_base, one_mul] at hk
    exact hk ▸ k.property

/-- Inclusion into the symmetric group identifies the actual stabilizer with `H1`. -/
theorem pointStabilizer_map_inclusion :
    pointStabilizer.map inclusion = OrderCertificate.H1 := by
  ext g
  rw [Subgroup.mem_map, certifiedStabilizer_mem_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hg, hfix⟩
    exact ⟨⟨g, hg⟩, hfix, rfl⟩

/-- The actual HS point stabilizer and the certified subgroup are the same
permutation group, with the different subtype presentations identified. -/
def pointStabilizerEquivCertified : pointStabilizer ≃* CertifiedStabilizer where
  toFun g := ⟨inclusion g.val,
    certifiedStabilizer_mem_iff.mpr ⟨g.val.property, g.property⟩⟩
  invFun g := ⟨⟨g.val, (certifiedStabilizer_mem_iff.mp g.property).1⟩,
    (certifiedStabilizer_mem_iff.mp g.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The comparison preserves the underlying permutation. -/
@[simp] theorem pointStabilizerEquivCertified_coe (g : pointStabilizer) :
    (pointStabilizerEquivCertified g : Equiv.Perm (Fin 100)) = inclusion g.val := by
  rfl

/-- The inverse comparison also preserves the underlying permutation. -/
@[simp] theorem pointStabilizerEquivCertified_symm_coe (g : CertifiedStabilizer) :
    inclusion (pointStabilizerEquivCertified.symm g).val =
      (g : Equiv.Perm (Fin 100)) := by
  rfl

/-- The zero stabilizer in the actual degree-100 HS action has order 443520. -/
theorem pointStabilizer_card : Nat.card pointStabilizer = 443520 :=
  (Nat.card_congr pointStabilizerEquivCertified.toEquiv).trans certifiedStabilizer_card

end Sporadic.LeechRelated.HS.SmallIndex
