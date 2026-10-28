module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Alignment
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Scalars
/-!
# The larger-field scalar obstruction on the actual source point

The order-three scalar witness in the standard four-element-field
parabolic lifts through the proved residual image equality. The determinant-
one alignment transports its moved vector to the original marked point.
Consequently the genuine source hypothesis at n=2 implies that L₁ does
not centralize V₁. All ambient source hypotheses are retained.

This refutes a central-point restriction interface under those hypotheses;
it does not construct an instance of all of them, count chief factors, or
claim a counterexample to the complete printed theorem. A larger-field
chief calculation must account for the odd scalar constituent. The binary
point-centralization theorem remains applicable over F₂.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Hypothesis G.2.1 and G.2.5(8), printed pp.332,335–336. The scan has O²
in G.2.1; the nearby O^{2′} in G.1.12 and the proof of G.2.5(6) is a
different residual and does not justify changing the definition of L₁.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  (d : Hypothesis D F n g h)

include d in
/-- The scalar obstruction persists under the actual star map and the given
marked natural coordinates. It is not an artefact of the standard basis. -/
theorem four_element_local_point_noncentral (hF : Nat.card F = 4) :
    ¬ D.L₁ ≤ centralizer (D.V₁ : Set G) := by
  obtain ⟨a⟩ := exists_pointAlignment d
  obtain ⟨x, hx, _, hmove⟩ := four_element_scalar_obstruction F hF
  rw [← a.residual_image] at hx
  obtain ⟨l, hl, hlx⟩ := hx
  intro hcentral
  let v : Fin 3 → F := a.basis • ![1, 0, 0]
  have hv : v ∈ d.point := by
    change v ∈ (d.point : Set (Fin 3 → F))
    rw [a.point_eq]
    exact ⟨![1, 0, 0], by simp, rfl⟩
  let w := d.coordinates.symm (Multiplicative.ofAdd v)
  have hw : (w : G) ∈ D.V₁ := (d.point_mem w).mpr (by simpa [w] using hv)
  have hc := hcentral hl w hw
  change (w : G) * (l : G) = (l : G) * (w : G) at hc
  have he : (l : G) * w * (l : G)⁻¹ = w := by
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have he' : (⟨(l : G) * w * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) w).mp w.property⟩ :
      D.V) = w := Subtype.ext he
  have heq := d.equivariant l w
  rw [he'] at heq
  have hfix : modelProjection d l • v = v := by
    change (d.model (starProjection D l)).val *ᵥ v = v
    simpa [w] using heq.symm
  have hz := a.projection_natural l v
  rw [hfix] at hz
  have hb : a.basis⁻¹ • v = (![1, 0, 0] : Fin 3 → F) := inv_smul_smul _ _
  rw [hb, hlx] at hz
  exact hmove hz

/-- In the source exponent-two branch the actual local actor cannot
centralize its marked point. Any proposed restriction flag must retain
this scalar constituent. -/
theorem exponent_two_local_point_noncentral (d : Hypothesis D F 2 g h) :
    ¬ D.L₁ ≤ centralizer (D.V₁ : Set G) :=
  four_element_local_point_noncentral d (by simpa using d.field_card)
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
