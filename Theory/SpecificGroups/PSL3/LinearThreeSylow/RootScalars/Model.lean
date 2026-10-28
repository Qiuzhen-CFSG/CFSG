module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars.TorusEquations

/-!
# Highest-root scalar coordinates for the concrete Borel in PSL₃

The highest-root embedding sends `x` to the projective class of `1 + x E₁₃`.
Conjugation by the point torus `diag(a,a⁻¹,1)` multiplies this coordinate by
`a`. The independently proved centralizer–torus factorization of the Borel
then supplies the scalar for every Borel element. Its value on coordinate one
proves uniqueness and multiplicativity, and the torus proves surjectivity.

This is the intrinsic matrix calculation used in Aschbacher–Smith, combined
manuscript (1 March 2004), E.6.8, printed pp.247–248 (PDF pp.258–259).
No Chapter E complement result is used.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree.RootScalars
variable (F : Type*) [Field F]

def root : Multiplicative F →* PSL(3,F) := (projective F).comp (central F)

theorem root_apply (x : F) :
    root F (Multiplicative.ofAdd x) = projection F (specialLinear F ⟨0,0,x⟩) := by rfl

theorem root_injective : Function.Injective (root F) :=
  (projective_injective F).comp (central_injective F)

theorem root_range : (root F).range = projectiveCenter F :=
  MonoidHom.range_comp _ _

theorem torus_conjugation (a : Fˣ) (x : F) :
    complementTorus F a * root F (Multiplicative.ofAdd x) * (complementTorus F a)⁻¹ =
      root F (Multiplicative.ofAdd ((a : F) * x)) := by
  rw [mul_inv_eq_iff_eq_mul]
  have h : pointTorus F a * specialLinear F ⟨0,0,x⟩ =
      specialLinear F ⟨0,0,(a : F)*x⟩ * pointTorus F a := by
    apply Subtype.ext
    change diagonal _ * matrix F ⟨0,0,x⟩ = matrix F ⟨0,0,(a : F)*x⟩ * diagonal _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simpa only [complementTorus_apply, root_apply, map_mul] using congrArg (projection F) h

/-- A scalar is determined by the conjugate of root coordinate one. -/
private theorem scalar_unique (g : PSL(3,F)) (a b : Fˣ)
    (ha : ∀ x : F, g * root F (Multiplicative.ofAdd x) * g⁻¹ =
      root F (Multiplicative.ofAdd ((a : F) * x)))
    (hb : ∀ x : F, g * root F (Multiplicative.ofAdd x) * g⁻¹ =
      root F (Multiplicative.ofAdd ((b : F) * x))) : a = b := by
  apply Units.ext
  have h := root_injective F ((ha 1).symm.trans (hb 1))
  simpa using congrArg Multiplicative.toAdd h

variable [Finite F] [CharP F 2]

private theorem exists_scalar (b : borel F) : ∃ a : Fˣ, ∀ x : F,
    (b : PSL(3,F)) * root F (Multiplicative.ofAdd x) * (b : PSL(3,F))⁻¹ =
      root F (Multiplicative.ofAdd ((a : F) * x)) := by
  obtain ⟨g,hg,hgb⟩ := b.property
  obtain ⟨c,hc,a,ha⟩ := root_centralizer_factorization F g hg
  refine ⟨a, ?_⟩
  intro x
  have hb : (b : PSL(3,F)) = c * complementTorus F a := hgb.symm.trans ha
  have hcomm := mem_centralizer_iff.mp hc (root F (Multiplicative.ofAdd ((a : F)*x)))
    (root_range F ▸ ⟨_, rfl⟩)
  rw [hb]
  calc
    (c * complementTorus F a) * root F (Multiplicative.ofAdd x) *
        (c * complementTorus F a)⁻¹ =
        c * (complementTorus F a * root F (Multiplicative.ofAdd x) *
          (complementTorus F a)⁻¹) * c⁻¹ := by group
    _ = c * root F (Multiplicative.ofAdd ((a : F)*x)) * c⁻¹ := by rw [torus_conjugation]
    _ = root F (Multiplicative.ofAdd ((a : F)*x)) := by rw [← hcomm, mul_inv_cancel_right]

noncomputable def borelCharacter : borel F →* Fˣ where
  toFun b := (exists_scalar F b).choose
  map_one' := by
    apply scalar_unique F (1 : PSL(3,F))
    · exact (exists_scalar F 1).choose_spec
    · intro x; simp
  map_mul' b c := by
    apply scalar_unique F ((b*c : borel F) : PSL(3,F))
    · exact (exists_scalar F (b*c)).choose_spec
    · intro x
      change (b : PSL(3,F)) * c * root F (Multiplicative.ofAdd x) *
        ((b : PSL(3,F)) * c)⁻¹ = _
      calc
        (b : PSL(3,F)) * c * root F (Multiplicative.ofAdd x) *
            ((b : PSL(3,F)) * c)⁻¹ =
            b * ((c : PSL(3,F)) * root F (Multiplicative.ofAdd x) * (c : PSL(3,F))⁻¹) *
              (b : PSL(3,F))⁻¹ := by group
        _ = root F (Multiplicative.ofAdd
            (((exists_scalar F b).choose : F) * (((exists_scalar F c).choose : F) * x))) := by
          rw [(exists_scalar F c).choose_spec, (exists_scalar F b).choose_spec]
        _ = _ := by simp only [Units.val_mul, mul_assoc]

theorem borel_conjugation (b : borel F) (x : F) :
    (b : PSL(3,F)) * root F (Multiplicative.ofAdd x) * (b : PSL(3,F))⁻¹ =
      root F (Multiplicative.ofAdd ((borelCharacter F b : F) * x)) :=
  (exists_scalar F b).choose_spec x

theorem borelCharacter_surjective : Function.Surjective (borelCharacter F) := by
  intro a
  let b : borel F := ⟨complementTorus F a,
    by rw [complementTorus_apply]; exact mem_map_of_mem _ (pointTorus_mem_borel F a)⟩
  refine ⟨b, scalar_unique F b _ a (borel_conjugation F b) ?_⟩
  exact torus_conjugation F a

end Matrix.PSL3.LinearThree.RootScalars
