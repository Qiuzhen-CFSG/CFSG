module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.RootModel

/-!
# Diagonal and unitriangular factors of the highest-root centralizer

The (0,0) entry defines a surjective homomorphism from the actual special
linear centralizer to the field units. Dividing by its diagonal section leaves
three unitriangular coordinates. Projective centralizer fullness then gives a
factorization of every projective centralizer element, without discarding the
cube-root scalar kernel of the torus.

Source: the linear inner-involution calculation of Aschbacher–Smith 16.4.8,
combined manuscript of 1 March 2004, printed p.1188.
-/

@[expose] public section
noncomputable section

open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.EvenInnerCentralizers
variable (F : Type*) [Field F]

theorem centralizerSL_diagonal_product (g : centralizerSL F) :
    g.val.val 0 0 * g.val.val 1 1 * g.val.val 0 0 = 1 := by
  obtain ⟨h10,h20,h21,hd⟩ := (mem_centralizerSL_iff F g.val).mp g.property
  have h := g.val.property
  rw [Matrix.det_fin_three, h10,h20,h21, ← hd] at h
  simpa only [zero_mul, mul_zero, add_zero, sub_zero] using h

theorem centralizerSL_diagonal_ne_zero (g : centralizerSL F) : g.val.val 0 0 ≠ 0 := by
  intro h
  have hd := centralizerSL_diagonal_product F g
  simp [h] at hd

def diagonalHom : centralizerSL F →* Fˣ where
  toFun g := Units.mk0 (g.val.val 0 0) (centralizerSL_diagonal_ne_zero F g)
  map_one' := Units.ext rfl
  map_mul' g h := by
    apply Units.ext
    change (g.val.val * h.val.val) 0 0 = g.val.val 0 0 * h.val.val 0 0
    obtain ⟨h10,h20,_,_⟩ := (mem_centralizerSL_iff F h.val).mp h.property
    simp [Matrix.mul_apply, Fin.sum_univ_three, h10,h20]

@[simp] theorem diagonalHom_val (g : centralizerSL F) :
    (diagonalHom F g : F) = g.val.val 0 0 := rfl

def torusInCentralizerSL : Fˣ →* centralizerSL F :=
  (torusSL F).codRestrict (centralizerSL F) (torusSL_mem_centralizerSL F)

@[simp] theorem diagonalHom_torus (a : Fˣ) :
    diagonalHom F (torusInCentralizerSL F a) = a := by
  apply Units.ext
  rfl

theorem diagonalHom_surjective : Function.Surjective (diagonalHom F) :=
  fun a => ⟨torusInCentralizerSL F a, diagonalHom_torus F a⟩

/-- The three upper coordinates after dividing out the diagonal torus. -/
def unipotentPart (g : centralizerSL F) : U F :=
  ⟨(g.val.val 0 0)⁻¹ * g.val.val 0 1,
    (g.val.val 0 0)^2 * g.val.val 1 2,
    (g.val.val 0 0)⁻¹ * g.val.val 0 2⟩

theorem centralizerSL_factorization (g : centralizerSL F) :
    g.val = torusSL F (diagonalHom F g) * specialLinear F (unipotentPart F g) := by
  obtain ⟨h10,h20,h21,hd⟩ := (mem_centralizerSL_iff F g.val).mp g.property
  have hn := centralizerSL_diagonal_ne_zero F g
  have h11 : g.val.val 1 1 = (g.val.val 0 0)⁻¹^2 := by
    apply mul_left_cancel₀ hn
    apply mul_right_cancel₀ hn
    calc
      g.val.val 0 0 * g.val.val 1 1 * g.val.val 0 0 = 1 :=
        centralizerSL_diagonal_product F g
      _ = g.val.val 0 0 * (g.val.val 0 0)⁻¹^2 * g.val.val 0 0 := by field_simp
  apply Subtype.ext
  change g.val.val = Matrix.diagonal _ * matrix F (unipotentPart F g)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.diagonal_mul, unipotentPart, diagonalHom,
      h10,h20,h21,h11, ← hd, hn]

theorem centralizer_factorization [CharP F 2] (g : centralizer F) :
    ∃ a : Fˣ, ∃ u : U F, g = torus F a * unipotentInCentralizer F u := by
  have hg := (centralizer_map F).ge g.property
  obtain ⟨s,hs,he⟩ := hg
  let t : centralizerSL F := ⟨s,hs⟩
  refine ⟨diagonalHom F t, unipotentPart F t, ?_⟩
  apply Subtype.ext
  change g.val = projection F _ * projective F _
  calc
    g.val = projection F t.val := he.symm
    _ = _ := by rw [centralizerSL_factorization F t, map_mul]; rfl

end Matrix.PSL3.EvenInnerCentralizers
