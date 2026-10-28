module

public import Theory.Representation.HexacodeAction.SmallFixedSpace
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# The commutator four-space of a hexacode best offender

The pointwise kernel description makes the commutator invariant under the
full stabilizer of the fixed plane. It is a nonzero scalar subspace inside
that plane. A proper scalar subspace would have binary dimension two,
contradicting the proved projective-line normalizer calculation. Thus the
commutator equals the fixed four-space and contains a full-weight vector.

Source: Aschbacher–Smith, 12.7.2(4), 12.7.3 and 12.7.11, using K.1.3.
-/

public noncomputable section
open Subgroup Atlas.Codes Representation.BinaryOffender
namespace Representation.Hexacode

/-- The whole-module commutator of an actual even best offender is its fixed plane. -/
theorem bestOffender_commutator_eq_fixed (A : Subgroup HexEvenAutomorphisms)
    (hA : IsBestOffender evenAction A) :
    subspaceCommutator evenAction ⊤ A = fixedSpace evenAction A := by
  let := hA.1.2
  have hcard := (ThompsonOffenders.bestOffender_dimensions A hA).2.1
  have hdim := (ThompsonOffenders.bestOffender_dimensions A hA).2.2.2
  let P := fixedSpace evenAction A
  let C := subspaceCommutator evenAction ⊤ A
  have hk : A = subspaceKernel evenAction P ⊤ := ThompsonOffenders.bestOffender_eq_kernel A hA
  have hs := ThompsonOffenders.fixedSpace_scalar_stable A
  have hCP : C ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    exact ThompsonOffenders.plane_displacement P hs hdim a ((hk ▸ ha).2) v
  have hN : subspaceStabilizer evenAction P ≤ normalizer (A : Set HexEvenAutomorphisms) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    rw [hk] at hx ⊢
    refine ⟨mem_top _, ?_⟩
    intro v hv
    have hi := ((subspaceStabilizer evenAction P).inv_mem hg v).mpr hv
    change evenAction (g * x * g⁻¹) v = v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx.2 _ hi]
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hstable : subspaceStabilizer evenAction P ≤ subspaceStabilizer evenAction C :=
    subspaceCommutator_invariant_normalizer evenAction
      (le_subspaceStabilizer evenAction ⊤ (by intros; trivial)) hN
  have hscalar : hexZ ∈ subspaceStabilizer action C := by
    have hz : hexEvenZ ∈ subspaceStabilizer evenAction P := hs
    exact hstable hz
  have heven := scalarSubmodule_finrank C hscalar
  have hCne : C ≠ ⊥ := by
    intro hz
    have hh := (subspaceCommutator_eq_bot_iff evenAction ⊤ A).mp hz
    have ht : P = ⊤ := top_unique hh
    have hd := hdim
    change Module.finrank (ZMod 2) P = 4 at hd
    rw [ht, finrank_top, hexacode_finrank] at hd
    omega
  have hpos : 0 < Module.finrank (ZMod 2) C :=
    Nat.pos_of_ne_zero (fun hz => hCne (Submodule.finrank_eq_zero.mp hz))
  have hle := Submodule.finrank_mono hCP
  have hnot2 : Module.finrank (ZMod 2) C ≠ 2 := by
    intro hd
    exact ProjectiveLineNormalizer.fourGroup_no_invariant_two A hcard hdim C hd hstable
  have hdimC : Module.finrank (ZMod 2) C = 4 := by
    change Module.finrank (ZMod 2) C ≤ Module.finrank (ZMod 2) (fixedSpace evenAction A) at hle
    rw [hdim] at hle
    change 2 * Module.finrank F (scalarSubmodule C hscalar) =
      Module.finrank (ZMod 2) C at heven
    omega
  exact Submodule.eq_of_le_of_finrank_eq hCP (hdimC.trans hdim.symm)

/-- The literal commutator plane contains a vector in the full-weight orbit. -/
theorem bestOffender_commutator_full_weight (A : Subgroup HexEvenAutomorphisms)
    (hA : IsBestOffender evenAction A) :
    ∃ v ∈ subspaceCommutator evenAction ⊤ A, hammingNorm (v : HexWord) = 6 := by
  let := hA.1.2
  obtain ⟨x, hx, hxne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  have hx0 : x.val ≠ 1 := fun he => hxne (Subtype.ext he)
  have hd := (ThompsonOffenders.bestOffender_dimensions A hA).2.2.2
  have hfix : ∀ v ∈ fixedSpace evenAction A, action x.val v = v := fun v hv => hv ⟨x, hx⟩
  obtain ⟨v, hv, hw⟩ := full_weight_mem_of_large_fixed_subspace x.val hx0
    (fixedSpace evenAction A) hd.ge hfix
  exact ⟨v, (bestOffender_commutator_eq_fixed A hA).symm ▸ hv, hw⟩

end Representation.Hexacode
