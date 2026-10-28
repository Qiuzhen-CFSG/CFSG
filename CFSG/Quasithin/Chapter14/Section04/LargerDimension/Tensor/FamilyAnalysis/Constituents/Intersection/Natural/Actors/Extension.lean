module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Actors.RootGroup
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# The action of a pure outer actor

Conjugate the actual extending representation by the supplied vector marking.
Normality of A₅ and the marked natural action give semilinearity over F₄.
An actor fixing the first vector and commuting with the marked upper-1 root
has matrix part upper triangular unipotent. Every F₄ automorphism is identity
or Frobenius. Faithfulness on A₅ and its trivial centralizer in S₅ make the
entire extending action faithful, so an outer actor cannot have a field-linear
upper-root action. Thus its action is an upper root followed by Frobenius,
with precisely the original actor and vector markings.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 14.4.10,
first proof paragraph, printed p.1010; natural tensor alternative 14.4.2(5),
p.1006. The semilinearity calculation is the natural-module normalizer argument
used in B.4.2(1), printed p.86.
-/

public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
open Representation.SL2FourNatural
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module Bit V] {σ : Representation Bit D V}

private def PointRootCoordinates.markedAction (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) : Representation Bit D Vector :=
  p.vector.conjRingEquiv.toMonoidHom.comp σ

private theorem PointRootCoordinates.markedAction_apply (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) (a : D) (v : Vector) :
    p.markedAction d a v = p.vector (σ a (p.vector.symm v)) := rfl

private theorem PointRootCoordinates.markedAction_component (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) (a : AltFive) (v : Vector) :
    p.markedAction d (inclusion hAD a) v = action (p.group a) v := by
  rw [p.markedAction_apply, p.equivariant, p.vector.apply_symm_apply]

private theorem PointRootCoordinates.markedAction_semilinear (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) (a : D) :
    ∃ φ : Field ≃+* Field, ∀ (c : Field) (v : Vector),
      p.markedAction d a (c • v) = φ c • p.markedAction d a v := by
  apply Representation.SL2NaturalOffenders.normalizer_semilinear (AltFive.subgroupOf D)
    ((subgroupOfEquivOfLe hAD).trans p.group)
  intro g v
  exact p.markedAction_component d ((subgroupOfEquivOfLe hAD) g) v

private theorem PointRootCoordinates.markedAction_faithful (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) : Function.Injective (p.markedAction d) := by
  let ρ := p.markedAction d
  have hf : Function.Injective (fun a : AltFive => ρ (inclusion hAD a)) := by
    intro a b hab
    apply p.group.injective
    apply action_faithful
    apply LinearEquiv.ext
    intro v
    exact (p.markedAction_component d a v).symm.trans
      ((LinearMap.congr_fun hab v).trans (p.markedAction_component d b v))
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply le_antisymm _ bot_le
  intro a ha
  have hk : ρ a = 1 := ha
  have hcentral : a.val ∈ centralizer (AltFive : Set Five) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    let y : AltFive := ⟨a.val * x * a.val⁻¹,
      (inferInstance : AltFive.Normal).conj_mem x hx a.val⟩
    have he : inclusion hAD y = a * inclusion hAD ⟨x, hx⟩ * a⁻¹ := rfl
    have hy : y = ⟨x, hx⟩ := by
      apply hf
      change ρ (inclusion hAD y) = ρ (inclusion hAD ⟨x, hx⟩)
      rw [he, map_mul, map_mul, hk, one_mul]
      have hki : ρ a⁻¹ = 1 := by
        have h := map_mul ρ a a⁻¹
        rw [mul_inv_cancel, map_one, hk, one_mul] at h
        exact h.symm
      rw [hki, mul_one]
    have hxy := congrArg Subtype.val hy
    change a.val * x * a.val⁻¹ = x at hxy
    have hh := congrArg (fun z : Five => z * a.val) hxy
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide)] at hcentral
  exact Subtype.ext hcentral

private theorem field_automorphism_cases (φ : Field ≃+* Field) :
    φ = RingEquiv.refl Field ∨ φ = fieldFrobenius := by
  let w : Field := QuadraticAlgebra.omega
  have hw0 : w ≠ 0 := by decide +kernel
  have hw1 : w ≠ 1 := by decide +kernel
  have hφ0 : φ w ≠ 0 := fun h => hw0 (φ.injective (h.trans (map_zero φ).symm))
  have hφ1 : φ w ≠ 1 := fun h => hw1 (φ.injective (h.trans (map_one φ).symm))
  have hc : ∀ z : Field, z ≠ 0 → z ≠ 1 → z = w ∨ z = fieldFrobenius w := by
    decide +kernel
  have ext_omega (ψ : Field ≃+* Field) (hw : φ w = ψ w) : φ = ψ := by
    apply RingEquiv.ext
    intro z
    have hz : z = 0 ∨ z = 1 ∨ z = w ∨ z = 1 + w := by
      revert z
      decide +kernel
    rcases hz with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact hw
    · simp [map_add, hw]
  rcases hc (φ w) hφ0 hφ1 with hw | hw
  · exact Or.inl (ext_omega (RingEquiv.refl Field) hw)
  · exact Or.inr (ext_omega fieldFrobenius hw)

private theorem semilinear_root_centralizer (f : Vector →ₗ[Bit] Vector)
    (φ : Field ≃+* Field) (hsemi : ∀ c v, f (c • v) = φ c • f v)
    (hpoint : f e1 = e1)
    (hroot : ∀ v, f (action (upper 1) v) = action (upper 1) (f v)) :
    ∃ b : Field, ∀ v : Vector, f v = ![φ (v 0) + b * φ (v 1), φ (v 1)] := by
  have he : action (upper 1) e2 = e1 + e2 := by
    rw [upper_action]
    funext i
    fin_cases i <;> simp [e1, e2]
  have hfe : f e2 1 = 1 := by
    have hh := congrFun (hroot e2) 0
    rw [he, map_add, hpoint, upper_action] at hh
    change 1 + f e2 0 = f e2 0 + 1 * f e2 1 at hh
    simpa only [one_mul, add_comm (1 : Field), add_right_inj] using hh.symm
  refine ⟨f e2 0, fun v => ?_⟩
  have hv : v = (v 0) • e1 + (v 1) • e2 := by
    funext i
    fin_cases i <;> simp [e1, e2]
  conv_lhs => rw [hv, map_add, hsemi, hsemi, hpoint]
  funext i
  fin_cases i <;> simp [e1, hfe, mul_comm]

/-- A pure actor outside the alternating component has the required Frobenius action
in the supplied frame. No particular extension representation is assumed. -/
theorem PointRootCoordinates.outer_action (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) {a : D} (ha : (1, a) ∈ d.actor)
    (houter : a.val ∉ AltFive) :
    ∃ b : Field, ∀ v : V,
      p.vector (σ a v) = action (upper b) (frobeniusLinear (p.vector v)) := by
  let ρ := p.markedAction d
  obtain ⟨φ, hφ⟩ := p.markedAction_semilinear d a
  have hp : ρ a e1 = e1 := p.pure_fixed d ha
  have hr : ∀ v, ρ a (action (upper 1) v) = action (upper 1) (ρ a v) := by
    intro v
    have hc := congrArg (fun z : Three × D => z.2) (actor_commute d ha p.root_mem)
    change a * (componentActor hAD p.group (upper 1)).2 =
      (componentActor hAD p.group (upper 1)).2 * a at hc
    have hh := LinearMap.congr_fun (congrArg ρ hc) v
    have he (w : Vector) : ρ (componentActor hAD p.group (upper 1)).2 w =
        action (upper 1) w := by
      change p.markedAction d (inclusion hAD (p.group.symm (upper 1))) w = _
      rw [p.markedAction_component, p.group.apply_symm_apply]
    simpa only [map_mul, Module.End.mul_apply, he] using hh
  obtain ⟨b, hb⟩ := semilinear_root_centralizer (ρ a) φ hφ hp hr
  rcases field_automorphism_cases φ with hφid | hφfrob
  · have he : a = inclusion hAD (p.group.symm (upper b)) := by
      apply p.markedAction_faithful d
      apply LinearMap.ext
      intro v
      rw [p.markedAction_component, p.group.apply_symm_apply, upper_action]
      simpa only [hφid, RingEquiv.refl_apply] using hb v
    exact (houter (he ▸ (p.group.symm (upper b)).property)).elim
  · refine ⟨b, fun v => ?_⟩
    have hh := hb (p.vector v)
    simpa only [ρ, p.markedAction_apply, p.vector.symm_apply_apply, hφfrob,
      upper_action, frobeniusLinear_apply, fieldFrobenius_apply] using hh
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
