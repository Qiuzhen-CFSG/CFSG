module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.Collection
import Mathlib.Tactic.Group

/-!
# Compatibility of the short separator with the second Weyl relations

Conjugating the separator images by root 7 leaves only two changed radical
words: rootOne*root8*root9 and root1*root8. The original reflection equations
carry these to the separator images of the corresponding reflected roots.
Twenty small coordinate checks certify these corrections inside the existing
Sylow model. The square and cubic complement relations follow by commuting
root 7 past the reflection. Thus no second matrix-certificate family is needed.

Source coordinates: Shinoda (1975), pp.81–83; Weyl marking: Parrott (1972),
p.683. This is a conditional compatibility theorem, not a certificate of the
original literal reflection equations.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.SecondExtension
open ReeTwo Theory.GroupTheory

private def twistedWord (i : Fin 10) : List (Fin 10) :=
  ![[0, 8, 9], [1, 8], [2], [3], [4], [5], [6], [7], [8], [9]] i

private theorem twisted_generator (i : Fin 10) :
    SylowModel.root 7 * SecondSeparator.separator (radicalGenerator i) *
      (SylowModel.root 7)⁻¹ = evalWord radicalGenerator (twistedWord i) := by
  fin_cases i <;> decide +kernel

private theorem twisted_image (i : Fin 10) :
    evalWord weylImage (twistedWord i) = SecondSeparator.separator (weylImage i) := by
  fin_cases i <;> decide +kernel

/-- The separator and corrected reflection preserve the Weyl relations.
Only the original literal Weyl equations are inputs; all added root corrections
are checked in the already verified coordinate Sylow group. -/
theorem WeylRelations.separator {G : Type*} [Group G] {f : SylowModel →* G} {r : G}
    (h : WeylRelations f r) :
    WeylRelations (f.comp SecondSeparator.separator.toMonoidHom)
      (r * f (SylowModel.root 7)) := by
  let z := SylowModel.root 7
  have hz : f z * f z = 1 := by
    rw [← map_mul]
    exact (congrArg f (by decide +kernel : SylowModel.root 7 * SylowModel.root 7 = 1)).trans
      (map_one f)
  have hc : Commute r (f z) := by
    exact mul_inv_eq_iff_eq_mul.mp (h.conjugate 7)
  constructor
  · rw [hc.mul_pow, h.square, pow_two, hz, one_mul]
  · have he : (f.comp SecondSeparator.separator.toMonoidHom) (SylowModel.root 0) *
        (r * f z) = f (SylowModel.root 0) * r := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        SecondSeparator.separator_root_zero, map_mul]
      change f (SylowModel.root 0) * f z * (r * f z) = _
      calc
        _ = f (SylowModel.root 0) * (f z * r) * f z := by group
        _ = f (SylowModel.root 0) * (r * f z) * f z := by rw [hc.eq]
        _ = f (SylowModel.root 0) * r := by simp only [mul_assoc, hz, mul_one]
    rw [he, h.cube]
  · intro i
    have hw (w : List (Fin 10)) :
        r * f (evalWord radicalGenerator w) * r⁻¹ = f (evalWord weylImage w) := by
      induction w with
      | nil => simp [evalWord]
      | cons j w ih =>
        simp only [evalWord, map_mul]
        calc
          _ = (r * f (radicalGenerator j) * r⁻¹) *
              (r * f (evalWord radicalGenerator w) * r⁻¹) := by group
          _ = _ := by rw [h.conjugate, ih]
    change (r * f z) * f (SecondSeparator.separator (radicalGenerator i)) *
      (r * f z)⁻¹ = f (SecondSeparator.separator (weylImage i))
    calc
      _ = r * f (z * SecondSeparator.separator (radicalGenerator i) * z⁻¹) * r⁻¹ := by
        simp only [map_mul, map_inv]
        group
      _ = r * f (evalWord radicalGenerator (twistedWord i)) * r⁻¹ := by
        rw [twisted_generator]
      _ = f (evalWord weylImage (twistedWord i)) := hw _
      _ = _ := by rw [twisted_image]

end Tits.AmalgamRigidity.FullRee.SecondExtension
