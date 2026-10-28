module
public import Theory.Representation.SymplecticOrbitCore
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Theory.Representation.SubspaceQuotient

/-!
# The quotient by an invariant Lagrangian is its actual dual

Restriction of the original symplectic pairing induces the equivariant
identification V/U ≃ U*. Its value on the original quotient map is recorded,
so subsequent natural-module recognition retains the marked quotient.
Source application: Aschbacher--Smith, G.10.4, printed p.358.
-/

public section
namespace Representation.BinaryOffender
open Module
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The literal quotient and inverse-dual action are identified by the
original alternating form. -/
theorem exists_lagrangian_quotient_dual_equiv (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (U : Subrepresentation ρ) (hU : B.orthogonal U.toSubmodule = U.toSubmodule) :
    ∃ e : Representation.Equiv U.quotientRepresentation U.toRepresentation.dual,
      ∀ v, e (U.toSubmodule.mkQ v) = submodulePairing ρ B U v := by
  let q := submodulePairing ρ B U
  have hk : q.ker = U.toSubmodule := by
    apply Eq.trans (b := B.orthogonal U.toSubmodule) ?_ hU
    ext v
    constructor
    · intro hv u hu
      have he := congrArg (fun f : Module.Dual (ZMod 2) U.toSubmodule => f ⟨u,hu⟩) hv
      exact hB.eq_iff.mp he
    · intro hv
      apply LinearMap.ext
      intro u
      exact hB.eq_iff.mpr (hv u u.property)
  let e : (V ⧸ U.toSubmodule) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) U.toSubmodule :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans
      (q.quotKerEquivOfSurjective (submodulePairing_surjective ρ B hnd U))
  have he (v : V) : e (U.toSubmodule.mkQ v) = q v := by
    simp [e]
  refine ⟨Representation.Equiv.mk e ?_, he⟩
  intro g
  apply LinearMap.ext
  intro z
  obtain ⟨v, rfl⟩ := U.toSubmodule.mkQ_surjective z
  change e (U.toSubmodule.mkQ (ρ g v)) = U.toRepresentation.dual g (e (U.toSubmodule.mkQ v))
  rw [he, he]
  exact submodulePairing_equivariant ρ B hinv U g v

end Representation.BinaryOffender
