module

public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.GeneralLinearCore
public import Theory.GroupTheory.PCoreSurjective

set_option linter.style.haveILetI false

/-!
# Binary five-space point stabilizers

The actual subgroup fixing a vector has a surjective action on the quotient by
its span. Its kernel is elementary abelian and remains normal in every overgroup
containing it. For a nonzero vector in dimension five the quotient action gives
an isomorphism from the stabilizer modulo its kernel to GL₄(2), with an explicit
coordinate-transport interface.

The elementary kernel is proved directly from displacements in the fixed line;
surjectivity is proved by lifting along a linear section of the quotient map.
The order-sixteen and two-core calculations are assembled in this umbrella.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.989 (PDF p.1006).
-/

namespace Theory.LinearAlgebra.BinaryFivePointStabilizer

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The binary point stabilizer has no two-core beyond its displacement kernel.

The quotient action is onto, and its kernel is elementary abelian.  The
quotient linear group is transported to `GL₄(2)`, whose two-core is trivial;
the p-core lifting theorem then identifies the stabilizer's two-core with the
actual action kernel.
-/
public theorem pCore_eq_kernel [FiniteDimensional (ZMod 2) E] (z : E) (hz : z ≠ 0)
    (hE : Module.finrank (ZMod 2) E = 5) :
    pCore 2 (stabilizer z) = kernel z := by
  letI : Finite E := Module.finite_of_finite (ZMod 2)
  letI : Finite (E → E) := inferInstance
  letI : Finite (E ≃ₗ[ZMod 2] E) := Finite.of_injective
    (fun g : E ≃ₗ[ZMod 2] E => g.toFun) (by
      intro a b h
      exact LinearEquiv.ext (fun x => congrFun h x))
  letI : Finite (stabilizer z) := Finite.of_injective
    (fun g : stabilizer z => g.val) (by
      intro a b h
      exact Subtype.ext h)
  letI : Finite (QuotientSpace z) := Finite.of_surjective
    (fun x : E => (line z).mkQ x) (LinearMap.range_eq_top.mp (Submodule.range_mkQ _))
  letI : Finite (QuotientSpace z → QuotientSpace z) := inferInstance
  letI : Finite (QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) := Finite.of_injective
    (fun g : QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z => g.toFun) (by
      intro a b h
      exact LinearEquiv.ext (fun x => congrFun h x))
  have hker : IsPGroup 2 (kernel z) :=
    IsElementaryAbelian.isPGroup 2 (kernel z)
  have hpre := MonoidHom.comap_pCore_of_ker_isPGroup (quotientAction z)
    (quotientAction_surjective z) hker
  let b := quotientCoordinates z hz hE
  let qgl : (QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) ≃*
      LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (QuotientSpace z)).symm.trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv b)
  have hGLlin : pCore 2 ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) = ⊥ := by
    apply pCore_eq_bot_finrank_four
    rw [Module.finrank_pi]
    decide
  let glEquiv := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 4 → ZMod 2)
  have hGLmap : (pCore 2 (LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2))).map
      glEquiv.toMonoidHom = ⊥ := by
    rw [pCore_map_iso, hGLlin]
  have hGL : pCore 2 (LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ glEquiv.injective).mp hGLmap
  have hqmap : (pCore 2 (QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z)).map
      qgl.toMonoidHom = ⊥ := by
    rw [pCore_map_iso, hGL]
  have htarget : pCore 2 (QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ qgl.injective).mp hqmap
  rw [← hpre, htarget]
  rfl

end Theory.LinearAlgebra.BinaryFivePointStabilizer
