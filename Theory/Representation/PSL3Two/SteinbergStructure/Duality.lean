module

public import Theory.Representation.PSL3Two.AutomorphismAction
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility

/-!
# Duality and automorphism invariance of the binary Steinberg module

The trace pairing (A,B) ↦ tr(AB) on trace-zero endomorphisms is invariant
under conjugation. It is nonzero on E₀₁ and E₁₀, so irreducibility makes
its map into the dual injective; equal dimensions give self-duality.
The existing extension to the full automorphism group supplies an explicit
intertwining equivalence for every automorphism twist.

Source: Aschbacher–Smith H.6.3(2), printed p.387, combined manuscript
of 1 March 2004. Self-duality and automorphism invariance are proved as
distinct assertions about the actual module.
-/

public section

open Matrix Representation
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
noncomputable section

namespace BinaryLinearThree.SteinbergStructure

/-- The invariant trace pairing on the literal trace-zero adjoint space. -/
def tracePairing : Steinberg →ₗ[ZMod 2] Module.Dual (ZMod 2) Steinberg where
  toFun f :=
    { toFun h := LinearMap.trace (ZMod 2) Vector (f.val ∘ₗ h.val)
      map_add' h j := by simp [LinearMap.comp_add]
      map_smul' c h := by simp [LinearMap.comp_smul] }
  map_add' f h := by ext j; simp [LinearMap.add_comp]
  map_smul' c f := by ext j; simp [LinearMap.smul_comp]

private def tracePairingMap : S.IntertwiningMap S.dual where
  toLinearMap := tracePairing
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro h
    change LinearMap.trace (ZMod 2) Vector ((W g ∘ₗ f.val ∘ₗ W g⁻¹) ∘ₗ h.val) =
      LinearMap.trace (ZMod 2) Vector (f.val ∘ₗ (W g⁻¹ ∘ₗ h.val ∘ₗ W (g⁻¹)⁻¹))
    rw [inv_inv]
    simpa only [LinearMap.comp_assoc] using
      (LinearMap.trace_comp_comm' (W g) (f.val ∘ₗ W g⁻¹ ∘ₗ h.val)).symm

private theorem tracePairingMap_ne_zero : tracePairingMap ≠ 0 := by
  intro hz
  have hh := congrArg (fun f : S.IntertwiningMap S.dual =>
    f (coordinates.symm (Pi.single 0 1)) (coordinates.symm (Pi.single 2 1))) hz
  change LinearMap.trace (ZMod 2) Vector
    ((matrixOf (Pi.single 0 1)).toLin' ∘ₗ (matrixOf (Pi.single 2 1)).toLin') = 0 at hh
  rw [← Matrix.toLin'_mul, Matrix.trace_toLin'_eq] at hh
  have h : (matrixOf (Pi.single 0 1) * matrixOf (Pi.single 2 1)).trace = 1 := by decide
  rw [h] at hh
  exact one_ne_zero hh

/-- H.6.3(2): the trace pairing identifies the Steinberg module with its contragredient. -/
def selfDual : S.Equiv S.dual := by
  let : IsIrreducible S := steinberg_irreducible
  have hi := (IsIrreducible.injective_or_eq_zero tracePairingMap).resolve_right tracePairingMap_ne_zero
  exact tracePairingMap.ofBijective ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp hi⟩

/-- H.6.3(2): invariance under every automorphism of the actual group. -/
def autEquiv (a : MulAut Group) : S.Equiv (S.comp a.toMonoidHom) :=
  .mk (LinearMap.GeneralLinearGroup.toLinearEquiv
    (AutomorphismAction.steinbergAut.asGroupHom a)) (by
    intro g
    have hh (h : Group) : AutomorphismAction.steinbergAut (MulAut.conj h) = S h := by
      exact congrArg (fun ρ : Representation (ZMod 2) Group Steinberg => ρ h)
        AutomorphismAction.steinbergAut_comp_conj
    change AutomorphismAction.steinbergAut a * S g = S (a g) * AutomorphismAction.steinbergAut a
    rw [← hh, ← hh, ← map_mul, ← map_mul]
    congr 1
    ext h
    simp [MulAut.conj_apply])

/-- The self-duality equivalence is given by the actual trace pairing. -/
@[simp] theorem selfDual_apply (f h : Steinberg) :
    selfDual f h = LinearMap.trace (ZMod 2) Vector (f.val ∘ₗ h.val) := by
  rfl

end BinaryLinearThree.SteinbergStructure
end
