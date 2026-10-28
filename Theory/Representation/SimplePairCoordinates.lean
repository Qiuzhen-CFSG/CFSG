module
public import Theory.GroupTheory.SimplePairSurjectivity
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# Direct-sum coordinates for two simple quotient actions

A faithful normal-subgroup action on complementary conjugate summands is
determined by its two quotient actions. The nontrivial constituent kernel
makes their joint image the full direct product. The resulting equivalences
retain both the original group embedding and the entire vector action.
Source: Aschbacher–Smith G.10.15 and G.11.2(12), pp.362–364.
-/
public noncomputable section
open Subgroup
namespace Representation
/-- Separating conjugate simple quotient actions on complementary summands
identify the normal subgroup and its entire action with the direct product. -/
theorem simple_pair_coordinates {D A V W : Type*} [Group D] [Group A]
    [IsSimpleGroup A] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (hfaith : Function.Injective ρ)
    (H : Subgroup D) [H.Normal] (R : Subrepresentation (ρ.comp H.subtype))
    (τ : Representation (ZMod 2) A W)
    (p : H →* A) (hp : Function.Surjective p) (hpker : p.ker ≠ ⊥)
    (c : R.toSubmodule ≃ₗ[ZMod 2] W)
    (hc : ∀ a u, c (R.toRepresentation a u) = τ (p a) (c u))
    (x : D) (hdis : Disjoint R.toSubmodule (R.toSubmodule.map (ρ x)))
    (hsup : R.toSubmodule ⊔ R.toSubmodule.map (ρ x) = ⊤) :
    ∃ e : H ≃* (A × A), ∃ C : V ≃ₗ[ZMod 2] (W × W),
      ∀ (a : H) u, C (ρ a u) = (τ (e a).1 (C u).1,τ (e a).2 (C u).2) := by
  let I := R.toSubmodule
  let α : MulAut H := MulAut.conjNormal x⁻¹
  have hcross (a : H) (w : I) :
      ρ a (ρ x w) = ρ x (ρ (α a) w) := by
    change ρ (a : D) (ρ x w) = ρ x (ρ (x⁻¹ * a * (x⁻¹)⁻¹) w)
    simp only [inv_inv,← Module.End.mul_apply,← map_mul]
    congr 2
    group
  let k := p.prod (p.comp α.toMonoidHom)
  have hk : Function.Injective k := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    have hpa : p a = 1 := congrArg Prod.fst ha
    have hpb : p (α a) = 1 := congrArg Prod.snd ha
    have hfix (b : H) (hb : p b = 1) (w : I) : ρ b w = w := by
      have hh := hc b w
      rw [hb,map_one,Module.End.one_apply] at hh
      exact congrArg Subtype.val (c.injective hh)
    apply Subtype.ext
    apply hfaith
    apply LinearMap.ext
    intro u
    have hu : u ∈ I ⊔ I.map (ρ x) := hsup.symm ▸ Submodule.mem_top
    obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨z,hz,rfl⟩ := hz
    simp only [Subgroup.coe_one,map_one,Module.End.one_apply]
    change ρ a (w + ρ x z) = w + ρ x z
    rw [map_add,hfix a hpa ⟨w,hw⟩,hcross a ⟨z,hz⟩,hfix (α a) hpb ⟨z,hz⟩]
  have hks : Function.Surjective k := Theory.GroupTheory.surjective_simple_pair p
    (p.comp α.toMonoidHom) hp (hp.comp α.surjective) hk hpker
  let e : H ≃* (A × A) := MulEquiv.ofBijective k ⟨hk,hks⟩
  let t := Submodule.equivMapOfInjective (ρ x)
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom x)).injective I
  let j : (I × I) ≃ₗ[ZMod 2] V :=
    ((LinearEquiv.refl (ZMod 2) I).prodCongr t).trans
      (Submodule.prodEquivOfIsCompl I _ ⟨hdis,codisjoint_iff.mpr hsup⟩)
  have hj (w : I × I) : j w = (w.1 : V) + ρ x w.2 := rfl
  let C := j.symm.trans (c.prodCongr c)
  refine ⟨e,C,?_⟩
  intro a u
  obtain ⟨w,rfl⟩ := j.surjective u
  have ha : ρ a (j w) = j (R.toRepresentation a w.1,R.toRepresentation (α a) w.2) := by
    rw [hj,map_add,hcross a w.2,hj]
    rfl
  rw [ha]
  change (c.prodCongr c) (j.symm (j _)) = (_, _)
  rw [j.symm_apply_apply]
  change (c (R.toRepresentation a w.1),c (R.toRepresentation (α a) w.2)) =
    (τ (p a) ((c.prodCongr c) (j.symm (j w))).1,
     τ (p (α a)) ((c.prodCongr c) (j.symm (j w))).2)
  rw [j.symm_apply_apply]
  exact Prod.ext (hc a w.1) (hc (α a) w.2)
end Representation

