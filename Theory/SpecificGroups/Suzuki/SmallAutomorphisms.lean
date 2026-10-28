module
public import Theory.GroupTheory.SpecificGroups.FiveFourComplement
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerSuzuki
public import Theory.GroupTheory.SolvableOuterQuotient
/-!
# Automorphisms of the small Suzuki group

In the faithful C₅:C₄ coordinates, the images of the two generators are
simultaneously conjugate to the generators whenever they satisfy the
presentation and the five-element is nontrivial. This finite calculation
and the normal-form theorem show that every automorphism is inner.
The coordinate model is centerless and has trivial two-core; order-twenty
recognition identifies it with the actual Suzuki matrix group Sz(2).
Transport therefore proves innerness and centerlessness for that model.

This supplies exactly the small Suzuki case of DGS, *Groups and Graphs*
(1985), 6.1, pp.118--119, without an outer-action assumption.
-/

public section
open Subgroup
namespace FiveFour
private theorem generator_images_conjugate (x y : Group)
    (hx : x ^ 5 = 1) (hxn : x ≠ 1) (hy : y ^ 4 = 1)
    (hconj : y * x * y⁻¹ = x ^ 2) :
    ∃ g : Group, g * c * g⁻¹ = x ∧ g * a * g⁻¹ = y := by
  exact (by decide +kernel : ∀ x y : Group,
    x ^ 5 = 1 → x ≠ 1 → y ^ 4 = 1 → y * x * y⁻¹ = x ^ 2 →
      ∃ g : Group, g * c * g⁻¹ = x ∧ g * a * g⁻¹ = y) x y hx hxn hy hconj

/-- Every automorphism of the faithful five-by-four group is inner. -/
theorem automorphism_inner (α : MulAut Group) : ∃ g : Group, α = MulAut.conj g := by
  obtain ⟨g,hc,ha⟩ := generator_images_conjugate (α c) (α a)
    (by rw [←map_pow,c_five,map_one]) (α.map_ne_one_iff.mpr (by decide))
    (by rw [←map_pow,a_four,map_one])
    (by rw [←map_inv,←map_mul,←map_mul,a_conj_c,map_pow])
  refine ⟨g,MulEquiv.ext fun x => ?_⟩
  exact DFunLike.congr_fun (hom_ext (f := α.toMonoidHom)
    (g := (MulAut.conj g).toMonoidHom) hc.symm ha.symm) x

/-- The faithful coordinate group is centerless. -/
theorem center_eq_bot : center Group = ⊥ := by
  apply bot_unique
  intro x hx
  exact (show ∀ x : Group, (∀ y, y*x=x*y) → x=1 by decide +kernel) x
    (mem_center_iff.mp hx)

/-- The faithful coordinate group has trivial two-core. -/
theorem twoCore_eq_bot : pCore 2 Group = ⊥ := by
  have hh := disjoint_range_of_normal_two_subgroup (MonoidHom.id Group) Function.injective_id
    (pCore 2 Group) pCore_isPGroup
  rw [MonoidHom.range_eq_top.mpr Function.surjective_id] at hh
  exact bot_unique (fun x hx => hh.le_bot ⟨mem_top x,hx⟩)

/-- Actual isomorphism from the faithful coordinates to the small Suzuki matrix group. -/
noncomputable def suzukiZeroEquiv : Group ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  Classical.choice
    (Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.equiv_suzuki_of_card_twenty
      card twoCore_eq_bot)
end FiveFour
namespace BenderSuzuki.MatrixGroups

/-- Every automorphism of the concrete Sz(2) model is inner. -/
theorem suzukiZero_automorphism_inner (α : MulAut (SuzukiMatrixGroup 0)) :
    ∃ g : SuzukiMatrixGroup 0, α = MulAut.conj g := by
  let e := FiveFour.suzukiZeroEquiv
  obtain ⟨g,hg⟩ := FiveFour.automorphism_inner (MulAut.congr e.symm α)
  refine ⟨e g,?_⟩
  apply (MulAut.congr e.symm).injective
  rw [hg,MulAut.congr_conj,e.symm_apply_apply]

/-- The concrete small Suzuki model is centerless. -/
theorem suzukiZero_center_eq_bot : center (SuzukiMatrixGroup 0) = ⊥ := by
  apply bot_unique
  intro x hx
  let e := FiveFour.suzukiZeroEquiv
  have he : e.symm x ∈ center FiveFour.Group := (centerCongr e.symm ⟨x,hx⟩).property
  rw [FiveFour.center_eq_bot,mem_bot] at he
  exact mem_bot.mpr (e.symm.injective (he.trans (map_one e.symm).symm))
end BenderSuzuki.MatrixGroups
