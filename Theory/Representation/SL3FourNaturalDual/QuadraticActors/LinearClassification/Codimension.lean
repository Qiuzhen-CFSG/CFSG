module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification.Parameters
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Exact fixed codimension of root-plane subgroups

The fixed-space quotient is explicitly identified with the dual of the
F₄-span of the parameters, together with one F₄ coordinate from the dual
summand. Restriction of functionals proves surjectivity of the quotient
projection. Restricting scalars then gives binary codimension four for a
nonzero field-line span, and six for the full parameter plane.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
open BinaryOffender

/-- Field span of the binary root parameters. -/
def parameterSpan (D : Submodule (ZMod 2) (F × F)) : Submodule F (F × F) :=
  Submodule.span F (D : Set (F × F))

/-- The natural displacement detects the dual of the parameter span; the
nontrivial dual displacement detects the first coordinate of the dual vector. -/
def fixedProjection (D : Submodule (ZMod 2) (F × F)) :
    V →ₗ[F] (Module.Dual F (parameterSpan D) × F) where
  toFun v := ((parameterSpan D).dualRestrict (pairDualEquiv (v.1 1, v.1 2)), v.2 0)
  map_add' v w := by
    apply Prod.ext
    · change (parameterSpan D).dualRestrict (pairDualEquiv ((v.1 1, v.1 2) +
        (w.1 1, w.1 2))) = _
      rw [map_add, map_add]
      rfl
    · rfl
  map_smul' a v := by
    apply Prod.ext
    · change (parameterSpan D).dualRestrict (pairDualEquiv (a • (v.1 1, v.1 2))) = _
      rw [map_smul, map_smul]
      rfl
    · rfl

lemma fixedProjection_surjective (D : Submodule (ZMod 2) (F × F)) :
    Function.Surjective (fixedProjection D) := by
  rintro ⟨f, a⟩
  obtain ⟨φ, hφ⟩ := Subspace.dualRestrict_surjective (W := parameterSpan D) f
  obtain ⟨p, hp⟩ := pairDualEquiv.surjective φ
  refine ⟨(![0, p.1, p.2], ![a, 0, 0]), ?_⟩
  change ((parameterSpan D).dualRestrict (pairDualEquiv p), a) = (f, a)
  rw [hp, hφ]

lemma fixedSpace_planeActor (D : Submodule (ZMod 2) (F × F)) (hD : D ≠ ⊥) :
    fixedSpace representation (planeActor D) =
      ((fixedProjection D).restrictScalars (ZMod 2)).ker := by
  obtain ⟨p, hp, hpn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  ext v
  constructor
  · intro hv
    have hd (q : F × F) (hq : q ∈ D) :
        (![q.1 * v.1 1 + q.2 * v.1 2, 0, 0],
          ![0, q.1 * v.2 0, q.2 * v.2 0]) = (0 : V) := by
      rw [← plane_displacement]
      exact sub_eq_zero.mpr (hv ⟨plane q, (mem_planeActor D q).mpr hq⟩)
    have hz : v.2 0 = 0 := by
      by_contra hn
      have h1 : p.1 = 0 := (mul_eq_zero.mp (congrArg (fun w : V => w.2 1)
        (hd p hp))).resolve_right hn
      have h2 : p.2 = 0 := (mul_eq_zero.mp (congrArg (fun w : V => w.2 2)
        (hd p hp))).resolve_right hn
      exact hpn (Prod.ext h1 h2)
    have hspan : parameterSpan D ≤ (pairDualEquiv (v.1 1, v.1 2)).ker := by
      apply Submodule.span_le.mpr
      intro q hq
      change pairDualEquiv (v.1 1, v.1 2) q = 0
      rw [pairDualEquiv_apply]
      have hs : q.1 * v.1 1 + q.2 * v.1 2 = 0 :=
        congrArg (fun w : V => w.1 0) (hd q hq)
      simpa only [mul_comm] using hs
    change fixedProjection D v = 0
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      exact hspan q.property
    · exact hz
  · intro hv g
    obtain ⟨g, p, hp, rfl⟩ := g
    change fixedProjection D v = 0 at hv
    have hz : v.2 0 = 0 := congrArg Prod.snd hv
    have hn : p.1 * v.1 1 + p.2 * v.1 2 = 0 := by
      have h := LinearMap.congr_fun (congrArg Prod.fst hv)
        ⟨p, Submodule.subset_span hp⟩
      change pairDualEquiv (v.1 1, v.1 2) p = 0 at h
      simpa only [pairDualEquiv_apply, mul_comm] using h
    change representation (plane p) v = v
    apply sub_eq_zero.mp
    rw [plane_displacement, hn, hz]
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp

/-- Exact fixed codimension: twice one plus the field dimension of the
parameter span. Thus a field line gives four and the full plane gives six. -/
theorem fixedCodim_planeActor (D : Submodule (ZMod 2) (F × F)) (hD : D ≠ ⊥) :
    fixedCodim representation (planeActor D) =
      2 * (Module.finrank F (parameterSpan D) + 1) := by
  unfold fixedCodim
  rw [fixedSpace_planeActor D hD]
  rw [((fixedProjection D).restrictScalars (ZMod 2)).quotKerEquivOfSurjective
    (fixedProjection_surjective D) |>.finrank_eq]
  rw [← Module.finrank_mul_finrank (ZMod 2) F, finrank_field,
    Module.finrank_prod, Module.finrank_self, Subspace.dual_finrank_eq]

end Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
