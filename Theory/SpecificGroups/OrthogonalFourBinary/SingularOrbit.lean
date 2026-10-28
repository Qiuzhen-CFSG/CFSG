module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Singular vectors in the binary orthogonal four-space

Use the orthogonal sum of two anisotropic binary planes, each with form
`x² + xy + y²`. Its nonzero singular vectors have two nonzero components.
The order-three rotation of each plane transports any nonzero vector to
any other, so the full isometry group is transitive on nonzero singular
vectors. All finite calculations below are checked by the Lean kernel.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), pp.1121–1122 and 1140–1141;
the orbit calculation is used in Lemma 15.3.62, p.1151.
-/

@[expose] public section
namespace OrthogonalFourBinary

abbrev F := ZMod 2
abbrev Plane := F × F
abbrev Space := Plane × Plane

def planeForm : QuadraticForm F Plane :=
  QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.fst F F F) +
  QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F) +
  QuadraticMap.linMulLin (LinearMap.snd F F F) (LinearMap.snd F F F)

def form : QuadraticForm F Space :=
  planeForm.comp (LinearMap.fst F Plane Plane) +
  planeForm.comp (LinearMap.snd F Plane Plane)

private def rotate : Plane ≃ₗ[F] Plane where
  toFun x := (x.2, x.1 + x.2)
  invFun x := (x.1 + x.2, x.1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

theorem planeForm_indicator (x : Plane) : planeForm x = if x = 0 then 0 else 1 := by
  have h : ∀ x : Plane, planeForm x = if x = 0 then 0 else 1 := by decide +kernel
  exact h x

theorem planeForm_preserved (e : Plane ≃ₗ[F] Plane) (x : Plane) :
    planeForm (e x) = planeForm x := by
  have h : e x = 0 ↔ x = 0 :=
    ⟨fun hx => e.injective (hx.trans (map_zero e).symm), fun hx => by simp [hx]⟩
  simp only [planeForm_indicator, h]

theorem singular_components (v : Space) (hv : v ≠ 0) (hs : form v = 0) :
    v.1 ≠ 0 ∧ v.2 ≠ 0 := by
  have h : ∀ v : Space, v ≠ 0 → form v = 0 → v.1 ≠ 0 ∧ v.2 ≠ 0 := by decide +kernel
  exact h v hv hs

private theorem plane_transport (x y : Plane) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : Plane ≃ₗ[F] Plane, e x = y := by
  have h : ∀ x y : Plane, x ≠ 0 → y ≠ 0 →
      ∃ k : Fin 3, (rotate ^ (k : ℕ)) x = y := by decide +kernel
  obtain ⟨k, hk⟩ := h x y hx hy
  exact ⟨rotate ^ (k : ℕ), hk⟩

theorem exists_isometry_of_singular (v w : Space) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvs : form v = 0) (hws : form w = 0) :
    ∃ e : form.IsometryEquiv form, e v = w := by
  obtain ⟨hv1, hv2⟩ := singular_components v hv hvs
  obtain ⟨hw1, hw2⟩ := singular_components w hw hws
  obtain ⟨e, he⟩ := plane_transport v.1 w.1 hv1 hw1
  obtain ⟨f, hf⟩ := plane_transport v.2 w.2 hv2 hw2
  refine ⟨⟨e.prodCongr f, ?_⟩, ?_⟩
  · intro x
    change planeForm (e x.1) + planeForm (f x.2) = planeForm x.1 + planeForm x.2
    rw [planeForm_preserved, planeForm_preserved]
  · exact Prod.ext he hf

end OrthogonalFourBinary
