module

public import Theory.Representation.PSL3Two.FanoCoreStructure

/-!
# Self-duality of the binary Fano core

The dot product restricts to an invariant perfect pairing on the actual
six-dimensional point core. Pairing with a point complement recovers the
corresponding coordinate, proving nondegeneracy. Equal dimensions then give
an equivariant linear equivalence with the contragredient representation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.5.2(6),
printed p.385.
-/

@[expose] public section

open Matrix Representation BinaryLinearThree BinaryLinearThree.FanoDecomposition
namespace BinaryLinearThree.FanoLocalStructure

/-- Restriction of the invariant dot product to the even-weight core. -/
def corePairing : Core →ₗ[ZMod 2] Module.Dual (ZMod 2) Core :=
  (BinaryPermutation.core Point).dualRestrict.comp
    ((dotProductEquiv (ZMod 2) Point).toLinearMap.comp (BinaryPermutation.core Point).subtype)

@[simp] theorem corePairing_apply (a b : Core) :
    corePairing a b = ∑ p : Point, a.val p * b.val p := rfl

/-- Pairing with a point complement recovers that coordinate on the core. -/
@[simp] theorem corePairing_pointSpike (a : Core) (p : Point) :
    corePairing a (pointSpike p) = a.val p := by
  rw [corePairing_apply]
  simp only [pointSpike_apply, mul_add, mul_one, Finset.sum_add_distrib]
  have ha : ∑ q : Point, a.val q = 0 := a.property
  rw [ha, add_zero]
  simp [Pi.single_apply]

/-- Nondegeneracy follows because the seven point complements detect every coordinate. -/
theorem corePairing_injective : Function.Injective corePairing := by
  intro a b h
  apply Subtype.ext
  funext p
  simpa only [corePairing_pointSpike] using
    congrArg (fun φ : Module.Dual (ZMod 2) Core => φ (pointSpike p)) h

/-- The dot product intertwines the core action and its actual contragredient action. -/
def corePairingMap : U₂.IntertwiningMap U₂.dual where
  toLinearMap := corePairing
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change (∑ p : Point, a.val ((pointPerm g).symm p) * b.val p) =
      ∑ p : Point, a.val p * b.val ((pointPerm g⁻¹).symm p)
    rw [← Equiv.sum_comp (pointPerm g) (fun p : Point =>
      a.val ((pointPerm g).symm p) * b.val p)]
    simp only [Equiv.symm_apply_apply, map_inv, Equiv.Perm.inv_def, Equiv.symm_symm]

/-- H.5.2(6): a genuine equivariant linear equivalence from U to its dual. -/
noncomputable def selfDual : U₂.Equiv U₂.dual :=
  corePairingMap.ofBijective ⟨corePairing_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp corePairing_injective⟩

@[simp] theorem selfDual_apply (a b : Core) :
    selfDual a b = ∑ p : Point, a.val p * b.val p := rfl

end BinaryLinearThree.FanoLocalStructure
