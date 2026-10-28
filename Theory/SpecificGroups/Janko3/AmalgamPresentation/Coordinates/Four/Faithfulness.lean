module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Basic
import Mathlib.Tactic.FinCases

/-!
# A single surviving translation makes the affine marking faithful

The special linear subgroup is transitive on nonzero translations. Thus a
homomorphism killing any nonzero translation kills all translations. If its
restriction to translations is injective, its kernel centralizes translations;
faithfulness of the natural linear action then makes the whole map injective.
For the concrete first generator, its cube is a nonzero translation.
-/

noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates
open Subgroup Matrix
open Representation.SL2FourNatural hiding Plane
open Representation.CentralCubicNaturalFour

private def markedTranslation : Plane := Multiplicative.ofAdd ![0,⟨0,1⟩]

private theorem first_cube : first ^ 3 = SemidirectProduct.inl markedTranslation := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> decide +kernel
  · apply Units.ext
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel

private theorem markedTranslation_ne : markedTranslation ≠ 1 := by decide +kernel

private theorem conjugate_translation (x : Affine) (v : Plane) :
    x * SemidirectProduct.inl v * x⁻¹ = SemidirectProduct.inl (naturalAction x.right v) := by
  have he : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
    (SemidirectProduct.inl_left_mul_inr_right x).symm
  calc
    _ = SemidirectProduct.inl x.left *
        (SemidirectProduct.inr x.right * SemidirectProduct.inl v *
          SemidirectProduct.inr x.right⁻¹) * (SemidirectProduct.inl x.left)⁻¹ := by
      conv_lhs => rw [he]
      rw [map_inv]
      group
    _ = _ := by
      rw [←SemidirectProduct.inl_aut,←map_inv,←map_mul,←map_mul]
      congr 1
      rw [mul_comm x.left,mul_assoc,mul_inv_cancel,mul_one]

/-- A homomorphism preserving the nontrivial cube of the first marked element
is faithful on the entire natural affine group. -/
public theorem injective_of_first_cube_ne_one {G : Type*} [Group G]
    (f : Affine →* G) (h : (f first) ^ 3 ≠ 1) : Function.Injective f := by
  have ht : f (SemidirectProduct.inl markedTranslation) ≠ 1 := by
    rwa [←first_cube,map_pow]
  have hr : Function.Injective (f.comp (SemidirectProduct.inl : Plane →* Affine)) := by
    apply (injective_iff_map_eq_one _).mpr
    intro v hv
    by_contra hn
    have hv0 : v.toAdd ≠ 0 := hn
    have ht0 : markedTranslation.toAdd ≠ 0 := markedTranslation_ne
    obtain ⟨g,hg⟩ := transitive_nonzero v.toAdd markedTranslation.toAdd hv0 ht0
    have hg' : naturalAction (SpecialLinearGroup.toGL g) v = markedTranslation :=
      congrArg Multiplicative.ofAdd hg
    apply ht
    rw [←hg',SemidirectProduct.inl_aut,map_mul,map_mul,map_inv]
    change f (SemidirectProduct.inl v) = 1 at hv
    simp only [hv,mul_one,map_inv,mul_inv_cancel]
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have ha (v : Plane) : naturalAction x.right v = v := by
    apply hr
    change f (SemidirectProduct.inl (naturalAction x.right v)) = f (SemidirectProduct.inl v)
    rw [←conjugate_translation,map_mul,map_mul,map_inv,hx,one_mul,inv_one,mul_one]
  have hright : x.right = 1 := by
    apply SemilinearNormalizer.linear_injective
    apply LinearEquiv.ext
    intro v
    rw [map_one]
    exact congrArg Multiplicative.toAdd (ha (Multiplicative.ofAdd v))
  have hx' : x = SemidirectProduct.inl x.left := SemidirectProduct.ext rfl hright
  have hleft : x.left = 1 := hr (by
    change f (SemidirectProduct.inl x.left) = f (SemidirectProduct.inl 1)
    rw [←hx',hx,map_one,map_one])
  exact SemidirectProduct.ext hleft hright

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates
