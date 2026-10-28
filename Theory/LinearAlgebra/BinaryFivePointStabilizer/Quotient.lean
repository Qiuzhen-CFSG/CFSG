module

public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Lifting the quotient action of a binary point stabilizer

Choose a linear section `s` of the quotient map `q`. An automorphism `a` of the
quotient lifts to `x ↦ x - s(q(x)) + s(a(q(x)))`, fixing the line pointwise.
Thus the quotient action is onto, and the first isomorphism theorem identifies
the stabilizer modulo its kernel with the general linear group of the quotient.
An explicit basis transport identifies this group with GL₄(2) in dimension five.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.989 (PDF p.1006).
-/

@[expose] public section

namespace Theory.LinearAlgebra.BinaryFivePointStabilizer
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

private def liftMap (z : E) (s : QuotientSpace z →ₗ[ZMod 2] E)
    (a : QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) : E →ₗ[ZMod 2] E :=
  LinearMap.id - s.comp (line z).mkQ + s.comp (a.toLinearMap.comp (line z).mkQ)

private theorem liftMap_apply (z : E) (s : QuotientSpace z →ₗ[ZMod 2] E)
    (a : QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) (x : E) :
    liftMap z s a x = x - s ((line z).mkQ x) + s (a ((line z).mkQ x)) := rfl

private theorem mkQ_liftMap (z : E) (s : QuotientSpace z →ₗ[ZMod 2] E)
    (hs : ∀ x, (line z).mkQ (s x) = x)
    (a : QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) (x : E) :
    (line z).mkQ (liftMap z s a x) = a ((line z).mkQ x) := by
  simp only [liftMap_apply, map_add, map_sub, hs, sub_self, zero_add]

private theorem liftMap_inv (z : E) (s : QuotientSpace z →ₗ[ZMod 2] E)
    (hs : ∀ x, (line z).mkQ (s x) = x)
    (a : QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) (x : E) :
    liftMap z s a.symm (liftMap z s a x) = x := by
  rw [liftMap_apply, mkQ_liftMap z s hs, liftMap_apply, a.symm_apply_apply]
  abel

/-- The quotient action is onto: every quotient automorphism lifts while fixing the line. -/
theorem quotientAction_surjective (z : E) : Function.Surjective (quotientAction z) := by
  obtain ⟨s, hs⟩ := (line z).mkQ.exists_rightInverse_of_surjective (line z).range_mkQ
  have hs' (x : QuotientSpace z) : (line z).mkQ (s x) = x := LinearMap.congr_fun hs x
  intro a
  let g : E ≃ₗ[ZMod 2] E :=
    { liftMap z s a with
      invFun := liftMap z s a.symm
      left_inv := liftMap_inv z s hs' a
      right_inv := liftMap_inv z s hs' a.symm }
  have hz : (line z).mkQ z = 0 := by
    exact (Submodule.Quotient.mk_eq_zero (line z)).mpr (Submodule.subset_span (by simp))
  have hg : g ∈ stabilizer z := by
    change liftMap z s a z = z
    simp only [liftMap_apply, hz, map_zero, sub_zero, add_zero]
  refine ⟨⟨g, hg⟩, ?_⟩
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact mkQ_liftMap z s hs' a x

/-- The stabilizer modulo its actual action kernel is the full quotient linear group. -/
noncomputable def quotientEquiv (z : E) :
    (stabilizer z ⧸ kernel z) ≃* (QuotientSpace z ≃ₗ[ZMod 2] QuotientSpace z) :=
  QuotientGroup.quotientKerEquivOfSurjective (quotientAction z) (quotientAction_surjective z)

@[simp] theorem quotientEquiv_mk (z : E) (g : stabilizer z) :
    quotientEquiv z (QuotientGroup.mk' (kernel z) g) = quotientAction z g := rfl

/-- Explicit linear coordinates on the four-dimensional quotient. -/
noncomputable def quotientCoordinates [FiniteDimensional (ZMod 2) E]
    (z : E) (hz : z ≠ 0) (hE : Module.finrank (ZMod 2) E = 5) :
    QuotientSpace z ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_quotient z hz hE, Module.finrank_pi, Fintype.card_fin])

/-- Transport of the quotient isomorphism along any specified choice of coordinates. -/
noncomputable def quotientEquivGL4OfCoordinates (z : E)
    (b : QuotientSpace z ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :
    (stabilizer z ⧸ kernel z) ≃*
      LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2) :=
  (quotientEquiv z).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (QuotientSpace z)).symm.trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv b))

/-- In dimension five, the stabilizer quotient is GL₄(2). -/
noncomputable def quotientEquivGL4 [FiniteDimensional (ZMod 2) E]
    (z : E) (hz : z ≠ 0) (hE : Module.finrank (ZMod 2) E = 5) :
    (stabilizer z ⧸ kernel z) ≃*
      LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2) :=
  quotientEquivGL4OfCoordinates z (quotientCoordinates z hz hE)

end Theory.LinearAlgebra.BinaryFivePointStabilizer
