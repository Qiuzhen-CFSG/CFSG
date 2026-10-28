module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.InvolutionCosets
public import Mathlib.FieldTheory.Finiteness

/-!
# The displacement bound for native Todd involutions

The existing fixed codimensions give displacement orders 16 and 32.
Thus any subspace of order at least 64 contains a vector outside the
displacement image. This is the exact comparison needed to fuse the
second Todd lifts into the original plane core in AS91 (6.4), p.602.
-/

@[expose] public section
open Sporadic.Mathieu Subgroup Representation.BinaryOffender
namespace MathieuCode.J4Fusion

noncomputable def displacement (s : M24) : Cocode →ₗ[ZMod 2] Cocode :=
  cocodeRepresentation s - LinearMap.id

lemma displacement_card_le (s : M24) (hs : orderOf s = 2) :
    Nat.card (LinearMap.range (displacement s)) ≤ 32 := by
  have hk : LinearMap.ker (displacement s) =
      fixedSpace cocodeRepresentation (zpowers s) := by
    ext v
    rw [LinearMap.mem_ker,mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  have hr := (displacement s).finrank_range_add_finrank_ker
  rw [hk] at hr
  have hf := fixedCodim_add_finrank cocodeRepresentation (zpowers s)
  have hcodim : fixedCodim cocodeRepresentation (zpowers s) ≤ 5 := by
    rcases M24InvolutionCentralizers.involution_classes s hs with ha | hb
    · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_z s ha]
      decide
    · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_t s hb]
  have hd : Module.finrank (ZMod 2) (LinearMap.range (displacement s)) ≤ 5 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hd).trans (by decide)

/-- A subgroup of order at least 64 cannot consist of involution displacements. -/
lemma exists_not_displacement (s : M24) (hs : orderOf s = 2)
    (U : Submodule (ZMod 2) Cocode) (hU : 64 ≤ Nat.card U) :
    ∃ v ∈ U, ¬ ∃ w : Cocode, v = cocodeRepresentation s w - w := by
  by_contra! hn
  have hi : U ≤ LinearMap.range (displacement s) := by
    intro v hv
    obtain ⟨w,hw⟩ := hn v hv
    exact ⟨w,hw.symm⟩
  have hb := Nat.card_le_card_of_injective (Submodule.inclusion hi)
    (Submodule.inclusion_injective hi)
  have hh := displacement_card_le s hs
  omega

end MathieuCode.J4Fusion
