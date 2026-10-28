module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModel
public import GorensteinWalter.PGL2DeterminantSquare

/-!
# Concrete nine-field coordinates for the third J₃ local pair

General-linear representatives act on the cubic kernel by their determinant
square class. Passing to projective classes gives the literal canonical
`3 : PGL₂(9)` model. The two matrices retain the saved marked-generator
coordinates; their relations and generation are established separately.
The saved discovery data are untrusted; every arithmetic assertion below is
checked by the kernel in the existing quadratic nine-element field.
-/

@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Matrix Subgroup
abbrev F := Atlas.Comparisons.Exceptional.Nine.F
abbrev GL9 := Matrix.GeneralLinearGroup (Fin 2) F
abbrev Z := SourceRecognition.CubicNormalizerModel.Z
abbrev P := SourceRecognition.CubicNormalizerModel.P
abbrev Canonical := SourceRecognition.CubicNormalizerModel.Model

/-- A root of the Conway polynomial X²-X-1 over the prime field. -/
def z : F := ⟨2,1⟩
theorem z_polynomial : z ^ 2 = z + 1 := by decide +kernel

private theorem square_iff (x : F) : IsSquare x ↔ x = 0 ∨ x ^ 4 = 1 := by
  have h : ∀ x : F, (∃ y : F, x = y * y) ↔ x = 0 ∨ x ^ 4 = 1 := by decide +kernel
  exact h x

private theorem projective_derived (g : GL9) :
    Matrix.ProjGenLinGroup.mk g ∈ SourceRecognition.CubicNormalizerModel.derived ↔ (g.det : F) ^ 4 = 1 := by
  rw [SourceRecognition.CubicNormalizerModel.derived,GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three
    F (by rw [Atlas.Comparisons.Exceptional.Nine.card]; exact ⟨3,2,by decide,by decide,by decide,by decide⟩)
      (by rw [Atlas.Comparisons.Exceptional.Nine.card]; decide)]
  rw [GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare,square_iff]
  exact or_iff_right (Units.ne_zero _)

private theorem action_formula (g : GL9) :
    (if (g.det : F) ^ 4 = 1 then 1 else SourceRecognition.CubicNormalizerModel.inversion) =
      SourceRecognition.CubicNormalizerModel.action (Matrix.ProjGenLinGroup.mk g) := by
  rw [SourceRecognition.CubicNormalizerModel.action_apply,projective_derived]
  split_ifs <;> rfl

/-- The computable determinant-square action before projectivization. -/
def action : GL9 →* MulAut Z where
  toFun g := if (g.det : F) ^ 4 = 1 then 1 else SourceRecognition.CubicNormalizerModel.inversion
  map_one' := by simp
  map_mul' g h := by rw [action_formula,action_formula,action_formula,map_mul,map_mul]

private theorem action_compatible (g : GL9) :
    action g = SourceRecognition.CubicNormalizerModel.action (Matrix.ProjGenLinGroup.mk g) :=
  action_formula g

abbrev ComputableModel := Z ⋊[action] GL9

/-- Projectivization keeps the complete cubic coordinate. -/
noncomputable def toCanonical : ComputableModel →* Canonical :=
  SemidirectProduct.map (φ₁ := action) (φ₂ := SourceRecognition.CubicNormalizerModel.action)
    (MonoidHom.id Z) (Matrix.ProjGenLinGroup.mk : GL9 →* P) (by
    intro g
    rw [MonoidHom.id_comp,MonoidHom.comp_id,action_compatible])

@[simp] theorem toCanonical_left (g : ComputableModel) :
    (toCanonical g).left = g.left := rfl
@[simp] theorem toCanonical_right (g : ComputableModel) :
    (toCanonical g).right = Matrix.ProjGenLinGroup.mk g.right := rfl

theorem toCanonical_surjective : Function.Surjective toCanonical := by
  rintro ⟨a,p⟩
  obtain ⟨g,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective p
  exact ⟨⟨a,g⟩,rfl⟩

def firstMatrix : GL9 := Matrix.GeneralLinearGroup.mkOfDetNeZero
  !![z ^ 3,z ^ 4;z ^ 3,1] (by decide +kernel)
def secondMatrix : GL9 := Matrix.GeneralLinearGroup.mkOfDetNeZero
  !![z,0;z ^ 7,z ^ 6] (by decide +kernel)
def first : ComputableModel := ⟨1,firstMatrix⟩
def second : ComputableModel := ⟨Multiplicative.ofAdd 1,secondMatrix⟩
noncomputable def canonicalFirst : Canonical := toCanonical first
noncomputable def canonicalSecond : Canonical := toCanonical second

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
