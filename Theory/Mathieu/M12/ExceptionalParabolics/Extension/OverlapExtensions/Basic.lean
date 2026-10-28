module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coordinates
public import Theory.GroupTheory.Amalgam.TwistTransport

/-!
# Shared generator images for the outer M₁₂ extension calculation

The central mark is the square of the first actual quaternion generator. The
four binary changes affect only the second and third generators. This module
fixes those literal conventions for the independent coverage and endpoint
calculations. Extensionality connects their generator equations to the actual
left inclusion of the verified amalgam.

Source context: Aschbacher--Smith F.1.12(I)(13), p.263, using the corrected
nonsplit degree-24 endpoint from `Extension.Amalgam`.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
open Theory.GroupTheory.RankTwoAmalgam

/-- The actual marked central involution, as a word in the overlap generators. -/
def marked : overlap := Overlap.generator 0 ^ 2

theorem marked_coe : (marked : Carrier) = z := by decide +kernel

/-- The two binary changes of the second and third generators. The first
quaternion generator is fixed. -/
def centralImage (p q : Bool) (j : Fin 3) : overlap :=
  (if (j = 1 ∧ p = true) ∨ (j = 2 ∧ q = true) then marked else 1) *
    Overlap.generator j

/-- The predicted overlap generator images, with their literal inner actor. -/
def generatorImage (u : overlap) (p q : Bool) (j : Fin 3) : overlap :=
  u * centralImage p q j * u⁻¹

/-- Equality on the three certified generators suffices for the actual
commuting square of the inclusion amalgam. -/
theorem extendsAcross_of_generator_images (d : MulAut overlap)
    (a : MulAut firstParabolic)
    (h : ∀ j, a (VerifiedPair.amalgam.left (Overlap.generator j)) =
      VerifiedPair.amalgam.left (d (Overlap.generator j))) :
    ExtendsAcross VerifiedPair.amalgam.left d := by
  refine ⟨a, ?_⟩
  have he := Overlap.hom_ext
    (a.toMonoidHom.comp VerifiedPair.amalgam.left)
    (VerifiedPair.amalgam.left.comp d.toMonoidHom) h
  exact fun b => DFunLike.congr_fun he b

end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
