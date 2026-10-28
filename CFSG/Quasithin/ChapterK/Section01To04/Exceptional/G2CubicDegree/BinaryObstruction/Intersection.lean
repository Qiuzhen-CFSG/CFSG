module
public import Theory.Representation.BinaryOffender.NormalizerConjugateBound
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# An involution supplement forces large displacement

If an actor A together with one involution generates a group with zero fixed
space, their fixed spaces have zero intersection. The dimension formula and
the characteristic-two involution bound give dim V ≤ 2 codim C_V(A).
This treats the common-fixed-space equality argument in GM Part I, 4.3.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
open Subgroup Representation Representation.BinaryOffender

/-- An involution supplement bounds the degree by twice the actor displacement. -/
theorem finrank_le_twice_fixedCodim_of_involution_supplement
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (A L : Subgroup G) (hfixed : fixedSpace ρ L = ⊥)
    (t : G) (ht : t ^ 2 = 1) (hgen : L ≤ A ⊔ zpowers t) :
    Module.finrank (ZMod 2) V ≤ 2 * fixedCodim ρ A := by
  have hzero : fixedSpace ρ (A ⊔ zpowers t) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfixed]
    exact ρ.invariants_comp_subtype_antitone hgen
  have hi : fixedSpace ρ A ⊓ fixedSpace ρ (zpowers t) = ⊥ := by
    change invariants (ρ.comp A.subtype) ⊓
      invariants (ρ.comp (zpowers t).subtype) = ⊥
    rw [← ρ.invariants_comp_sup]
    exact hzero
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace ρ A) (fixedSpace ρ (zpowers t))
  rw [hi, finrank_bot, add_zero] at hd
  have hsum := Submodule.finrank_le (fixedSpace ρ A ⊔ fixedSpace ρ (zpowers t))
  have hle : LinearMap.range (ρ t - LinearMap.id) ≤ fixedSpace ρ (zpowers t) := by
    rintro _ ⟨v, rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    exact involution_fixes_displacement ρ (by simpa only [pow_two] using ht) v
  have hr := Submodule.finrank_mono hle
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hr
  have hA := fixedCodim_add_finrank ρ A
  have ht := fixedCodim_add_finrank ρ (zpowers t)
  omega

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
