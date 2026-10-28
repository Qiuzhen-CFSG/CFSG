module

public import Theory.Mathieu.M22.CentralCoverPrelude
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Conjugation of literal local pullbacks in central covers of M₂₂

Lifting a native conjugating element conjugates the full preimages by the
same ambient element. Embedded residuals and the actual ambient center
respect this map. These are the transport steps in the arbitrary-J
intersection argument of Aschbacher–Smith I.2.2(6a), printed p.412.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22CentralCover
open Subgroup
variable {K : Type*} [Group K]

theorem preimage_map_conj (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) (k : K) :
    preimage e (H.map (MulAut.conj (projection e k)).toMonoidHom) =
      (preimage e H).map (MulAut.conj k).toMonoidHom := by
  ext x
  change projection e x ∈ H.map _ ↔ x ∈ (preimage e H).map _
  rw [mem_map_equiv, mem_map_equiv]
  change (projection e k)⁻¹ * projection e x * projection e k ∈ H ↔
    projection e (k⁻¹ * x * k) ∈ H
  simp only [map_mul, map_inv]

/-- The equivalence comes from an actual inner automorphism of the cover. -/
noncomputable def preimageConjEquiv (e : (K ⧸ center K) ≃* M22)
    (H : Subgroup M22) (k : K) :
    preimage e H ≃* preimage e (H.map (MulAut.conj (projection e k)).toMonoidHom) :=
  ((preimage e H).equivMapOfInjective (MulAut.conj k).toMonoidHom
    (MulAut.conj k).injective).trans (MulEquiv.subgroupCongr (preimage_map_conj e H k).symm)

variable [Finite K]

/-- Residual placement of the actual center transports under this conjugation. -/
theorem center_le_residual_conjugate (X : Subgroup K) (k : K)
    (h : center K ≤ (pResidual 2 X).map X.subtype) :
    center K ≤ (pResidual 2 (X.map (MulAut.conj k).toMonoidHom)).map
      (X.map (MulAut.conj k).toMonoidHom).subtype := by
  have hm := map_mono (f := (MulAut.conj k).toMonoidHom) h
  rw [Theory.GroupTheory.map_center_equiv, map_embedded_pResidual] at hm
  exact hm

end Sporadic.Mathieu.M22CentralCover
