module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules
public import Mathlib.LinearAlgebra.Dual.Lemmas


/-!
# Equivariant duality for the native ten-dimensional M22 modules

The coordinate dot product descends through the constant line and the Golay
space. Evaluation at the distinguished pair is exactly `pairFunctional`, so
restricting to its kernel descends further through the pair line. The resulting
map to the dual of the literal cocode quotient is injective: a representative
annihilating the even core is constant, by double orthogonal complementation.
The proved dimensions ten make this map a linear equivalence. Invariance of
the coordinate pairing proves equivariance under the setwise pair stabilizer
and its native M22 subgroup. No irreducibility assumption enters this proof.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.13.1,
printed p.395 (PDF p.406).
-/

public section

noncomputable section
open Sporadic.Mathieu
namespace MathieuCode

private def m22CoreCodePairing : Core →ₗ[ZMod 2] Module.Dual (ZMod 2) Code :=
  (codeLine.liftQ ((LinearMap.comp (LinearMap.comp dotForm golay.subtype).flip Core.subtype).flip) (by
    intro v hv
    apply LinearMap.ext
    intro u
    change dotForm v.val u.val = 0
    have hu : u.val ∈ dotForm.orthogonal (BinaryPermutation.constants (Fin 24)) := by
      rw [← core_eq_orthogonal_constants]
      exact u.property
    exact hu v.val hv)).flip

/-- Coordinate pairing on the ambient quotients, used to descend at the marked pair. -/
private def m22AmbientPairing : Cocode →ₗ[ZMod 2] Module.Dual (ZMod 2) Code :=
  codeInCore.liftQ m22CoreCodePairing (by
    intro u hu
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change dotForm v.val u.val = 0
      exact golay_le_orthogonal hu v.val v.property)

private theorem m22AmbientPairing_mk (u : Core) (v : golay) :
    m22AmbientPairing (codeInCore.mkQ u) (codeLine.mkQ v) = dotForm v.val u.val := by rfl

private theorem m22AmbientPairing_pair (v : Code) :
    m22AmbientPairing m22PairClass v = pairFunctional v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact dotForm_m22PairWord v.val

private theorem m22AmbientPairing_nondegenerate_right (v : Code)
    (hv : ∀ u, m22AmbientPairing u v = 0) : v = 0 := by
  obtain ⟨w, rfl⟩ := codeLine.mkQ_surjective v
  apply (Submodule.Quotient.mk_eq_zero codeLine).mpr
  change w.val ∈ BinaryPermutation.constants (Fin 24)
  rw [← dotForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_symmetric.isRefl
    (BinaryPermutation.constants (Fin 24)),
    ← core_eq_orthogonal_constants]
  intro u hu
  rw [dotForm_symmetric.eq]
  exact hv (codeInCore.mkQ ⟨u, hu⟩)

/-- The dot product gives a functional on the literal M22 cocode quotient
for every vector of the existing code hyperplane. -/
def m22CodeToCocodeDual : M22Code →ₗ[ZMod 2] Module.Dual (ZMod 2) M22Cocode :=
  (m22PairLine.liftQ ((m22AmbientPairing.flip.comp m22Hyperplane.subtype).flip) (by
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    apply LinearMap.ext
    intro v
    change m22AmbientPairing (c • m22PairClass) v.val = 0
    rw [map_smul, LinearMap.smul_apply, m22AmbientPairing_pair]
    change c • pairFunctional v.val = 0
    rw [show pairFunctional v.val = 0 from v.property, smul_zero])).flip

private theorem m22CodeToCocodeDual_mk (v : M22Code) (u : Cocode) :
    m22CodeToCocodeDual v (m22PairLine.mkQ u) = m22AmbientPairing u v.val := by rfl

theorem m22CodeToCocodeDual_injective : Function.Injective m22CodeToCocodeDual := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply Subtype.ext
  apply m22AmbientPairing_nondegenerate_right
  intro u
  have h := LinearMap.congr_fun hv (m22PairLine.mkQ u)
  exact h

/-- Genuine linear duality induced by the coordinate dot product. -/
def m22CodeCocodeDuality : M22Code ≃ₗ[ZMod 2] Module.Dual (ZMod 2) M22Cocode :=
  m22CodeToCocodeDual.linearEquivOfInjective m22CodeToCocodeDual_injective (by
    rw [Subspace.dual_finrank_eq, finrank_m22Code, finrank_m22Cocode])

@[simp] theorem m22CodeCocodeDuality_apply (v : M22Code) :
    m22CodeCocodeDuality v = m22CodeToCocodeDual v := by rfl

private theorem m22AmbientPairing_invariant (g : M24) (u : Cocode) (v : Code) :
    m22AmbientPairing (cocodeRepresentation g u) (codeRepresentation g v) =
      m22AmbientPairing u v := by
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact dotForm_invariant g v.val u.val

/-- The pairing is invariant under the full setwise pair stabilizer. -/
theorem m22CodeToCocodeDual_invariant (g : m22PairStabilizer) (v : M22Code)
    (u : M22Cocode) :
    m22CodeToCocodeDual (m22OuterCodeRepresentation g v)
      (m22OuterCocodeRepresentation g u) = m22CodeToCocodeDual v u := by
  induction u using Submodule.Quotient.induction_on with
  | _ u => exact m22AmbientPairing_invariant g.val u v.val

/-- The actual code action is intertwined with the contragredient cocode action. -/
theorem m22CodeCocodeDuality_equivariant (g : m22PairStabilizer) (v : M22Code) :
    m22CodeCocodeDuality (m22OuterCodeRepresentation g v) =
      m22OuterCocodeRepresentation.dual g (m22CodeCocodeDuality v) := by
  apply LinearMap.ext
  intro u
  change m22CodeToCocodeDual (m22OuterCodeRepresentation g v) u =
    m22CodeToCocodeDual v (m22OuterCocodeRepresentation g⁻¹ u)
  have h := m22CodeToCocodeDual_invariant g v (m22OuterCocodeRepresentation g⁻¹ u)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using h

/-- The same coordinate duality restricts to the original native M22 action. -/
theorem m22CodeCocodeDuality_equivariant_native (g : M22) (v : M22Code) :
    m22CodeCocodeDuality (m22CodeRepresentation g v) =
      m22CocodeRepresentation.dual g (m22CodeCocodeDuality v) := by
  apply LinearMap.ext
  intro u
  change m22CodeToCocodeDual (m22CodeRepresentation g v) u =
    m22CodeToCocodeDual v (m22CocodeRepresentation g⁻¹ u)
  have h := m22CodeToCocodeDual_invariant (m22ToPairStabilizer g) v
    (m22CocodeRepresentation g⁻¹ u)
  change m22CodeToCocodeDual (m22CodeRepresentation g v)
    (m22CocodeRepresentation g (m22CocodeRepresentation g⁻¹ u)) = _ at h
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using h


/-- On representatives, the duality is precisely the native coordinate pairing. -/
theorem m22CodeCocodeDuality_apply_mk (v : golay) (hv : v.val 0 + v.val 9 = 0)
    (u : Core) :
    m22CodeCocodeDuality ⟨codeLine.mkQ v, hv⟩
      (m22PairLine.mkQ (codeInCore.mkQ u)) = dotForm v.val u.val := by rfl

end MathieuCode
