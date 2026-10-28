module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.MathieuTwelve.Placement
public import Theory.Mathieu.M12.SmallParabolicPair.ThreeResidualFixer
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The M₁₂ centralizer calculation in the sporadic rank-one branch

The source normal four determines a marking of the M₁₂ component in which
M ∩ K is the second parabolic. Its three-residual lies inside the transported
Y. The pointwise fixer of that residual in the full automorphism group is
trivial, so faithful conjugation on K makes C_G(Y) trivial. In particular,
the required Sylow centralizer S ∩ C_G(Y) is trivial.

The only model input is an actual equivalence K ≃ M₁₂. The argument applies
to every ambient group allowed by LocalConfiguration, including outer
extensions, and assumes no parabolic placement or centralizer conclusion.
The parent transfers this quotient calculation through the retained central
cover to C_S(Y₊) = C_S(L).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the sporadic paragraph of 15.3.43, printed p.1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] [Finite G] {K S M Y V : Subgroup G}

/-- For an actual M₁₂ component, the source residual has trivial centralizer in the whole faithful ambient group. -/
theorem LocalConfiguration.mathieu_twelve_full_centralizer
    (c : LocalConfiguration K S M Y V) (e : K ≃* Sporadic.Mathieu.M12) :
    centralizer (Y : Set G) = ⊥ := by
  let : K.Normal := c.normal
  obtain ⟨f, _, _, hM⟩ := MathieuTwelve.exists_local_marking c e
  have hR := MathieuTwelve.marked_residual_le c f hM
  apply eq_bot_iff.mpr
  intro x hx
  let a : MulAut Sporadic.Mathieu.M12 := MulAut.congr f (MulAut.conjNormal x)
  have hfix : ∀ y ∈ (Y.subgroupOf K).map f.toMonoidHom, a y = y := by
    rintro _ ⟨y, hy, rfl⟩
    change f (MulAut.conjNormal x (f.symm (f y))) = f y
    rw [f.symm_apply_apply]
    apply congrArg f
    apply Subtype.ext
    change x * (y : G) * x⁻¹ = (y : G)
    rw [← hx y hy, mul_inv_cancel_right]
  have ha : a = 1 := Sporadic.Mathieu.M12SmallPair.eq_one_of_fixes_second_threeResidual
    a (fun y hy => hfix y (hR hy))
  have hb : (MulAut.conjNormal x : MulAut K) = 1 :=
    (MulAut.congr f).injective (ha.trans (map_one (MulAut.congr f)).symm)
  exact MulAut.conjNormal_injective_of_centralizer_eq_bot K c.faithful
    (hb.trans (map_one (MulAut.conjNormal : G →* MulAut K)).symm)

/-- The quotient Sylow centralizer calculation required in the M₁₂ branch of 15.3.43. -/
theorem LocalConfiguration.mathieu_twelve_centralizer
    (c : LocalConfiguration K S M Y V) (e : K ≃* Sporadic.Mathieu.M12) :
    S ⊓ centralizer (Y : Set G) = ⊥ := by
  rw [c.mathieu_twelve_full_centralizer e, inf_bot_eq]

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
