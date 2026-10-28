module
public import Theory.Representation.PSL3Two.LowRankProfiles
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.DualBounds
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The binary natural–dual normalizer has no FF offender

Every automorphism of SL₃(2) has a unique implementing operator on the
natural–dual pair. This constructs its actual six-dimensional action.
An elementary actor has rank at most two. Outer operators move at least
three dimensions; inner actors have combined natural and dual fixed
codimension strictly greater than their rank. Thus no actor is an offender.
The same conclusion holds on the faithful image of any compatible action.

Source: Aschbacher–Smith 10.1.2(1) and 10.2.9, printed pp.742 and751,
using the natural–dual row of 10.1.1(5).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual

private theorem exists_operator (α : MulAut Group) :
    ∃ f : Space ≃ₗ[ZMod 2] Space, ∀ g x, f (action g x) = action (α g) (f x) := by
  by_cases hα : α ∈ MulAut.innerSubgroup Group
  · obtain ⟨g,rfl⟩ := hα
    exact ⟨innerOperator g,innerOperator_covariance g⟩
  · obtain ⟨g,hg⟩ := AutomorphismAction.outer_eq_inner_graph α hα
    refine ⟨graphSwap.trans (innerOperator g),?_⟩
    intro k x
    change innerOperator g (graphSwap (action k x)) = _
    rw [graphSwap_covariance,innerOperator_covariance,hg]
    rfl

private noncomputable def autOperator (α : MulAut Group) : Space ≃ₗ[ZMod 2] Space :=
  Classical.choose (exists_operator α)

private theorem autOperator_covariance (α : MulAut Group) (g : Group) (x : Space) :
    autOperator α (action g x) = action (α g) (autOperator α x) :=
  Classical.choose_spec (exists_operator α) g x

/-- The unique natural–dual implementation of every binary-three automorphism. -/
noncomputable def autAction : Representation (ZMod 2) (MulAut Group) Space where
  toFun α := (autOperator α).toLinearMap
  map_one' := by
    have h := implementing_unique 1 (autOperator 1) (LinearEquiv.refl _ _)
      (autOperator_covariance 1) (fun _ _ => rfl)
    exact congrArg LinearEquiv.toLinearMap h
  map_mul' α β := by
    have h := implementing_unique (α*β) (autOperator (α*β))
      ((autOperator β).trans (autOperator α)) (autOperator_covariance (α*β)) (by
        intro g x
        change autOperator α (autOperator β (action g x)) = _
        rw [autOperator_covariance,autOperator_covariance]
        rfl)
    exact congrArg LinearEquiv.toLinearMap h

/-- Restriction along the literal inner-automorphism map is the original pair action. -/
theorem autAction_inner (g : Group) : autAction (MulAut.conj g) = action g := by
  exact congrArg LinearEquiv.toLinearMap (implementing_unique _ _ _
    (autOperator_covariance (MulAut.conj g)) (innerOperator_covariance g))

/-- Neither inner nor outer elementary actors satisfy the offender inequality. -/
theorem not_isFFModule_autAction : ¬ IsFFModule autAction := by
  rintro ⟨A,hA⟩
  have hr : rank A ≤ 2 := by
    rcases LowRankProfiles.rank_one_or_two A hA.1 with h | h <;> omega
  have hAI : A ≤ MulAut.innerSubgroup Group := by
    intro α hα
    by_contra ho
    have hl := LowRankProfiles.outer_displacement_bound autAction autAction_inner α ho
    rw [←fixedCodim_zpowers_eq_displacement_rank] at hl
    have hf : fixedSpace autAction A ≤ fixedSpace autAction (zpowers α) := by
      intro v hv b
      exact hv ⟨b,(zpowers_le.mpr hα) b.property⟩
    have hdim := Submodule.finrank_mono hf
    have hsum := fixedCodim_add_finrank autAction A
    have hsum' := fixedCodim_add_finrank autAction (zpowers α)
    have hu := hA.2
    omega
  let j : Group →* MulAut Group := MulAut.conj
  have hj : Function.Injective j :=
    MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  let B := A.comap j
  have hB : B.map j = A := by
    exact map_comap_eq_self (show A ≤ j.range from hAI)
  let : IsElementaryAbelian 2 A := hA.1.2
  have he : IsElementaryAbelian 2 B := {
    toIsMulCommutative := A.comap_injective_isMulCommutative hj
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      apply hj
      change j ((x : Group)^2) = j 1
      rw [map_pow,map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (j x) x.property }
  have hBn : B ≠ ⊥ := by
    intro hb
    exact hA.1.1 (by rw [←hB,hb,Subgroup.map_bot])
  have hl := ResidualFFForms.ConstituentBudget.rank_lt_natural_add_dual_fixedCodim B ⟨hBn,he⟩
  have hc := fixedCodim_map_equivariant action autAction j (LinearEquiv.refl _ _)
    (fun g x => by change action g x = autAction (j g) x; rw [autAction_inner]) B
  rw [hB] at hc
  change fixedCodim (W.prod W.dual) B = _ at hc
  rw [fixedCodim_prod] at hc
  have hrr := rank_map_injective j hj B
  rw [hB] at hrr
  have hb := hA.2
  omega
end BinaryLinearThree.NaturalDual

namespace BinaryLinearThree.NaturalDual

/-- The implementing action of the full automorphism group is faithful. -/
theorem autAction_injective : Function.Injective autAction := by
  intro α β h
  apply MulEquiv.ext
  intro g
  have hf : Function.Injective action := by
    intro x y he
    apply natural_injective
    apply LinearMap.ext
    intro v
    exact congrArg Prod.fst (LinearMap.congr_fun he (v,0))
  apply hf
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (autOperator α).surjective x
  have he : autOperator α = autOperator β := LinearEquiv.toLinearMap_injective h
  rw [←autOperator_covariance,he,autOperator_covariance]

/-- Any compatible extension has a non-FF faithful image on the same vectors. -/
theorem not_isFFModule_image_of_covariance
    {P : Type*} [_root_.Group P]
    (η : Representation (ZMod 2) P Space) (a : P →* MulAut Group)
    (ha : ∀ p g x, η p (action g x) = action (a p g) (η p x)) :
    ¬ IsFFModule (imageRepresentation η) := by
  have he (p : P) : η p = autAction (a p) :=
    congrArg LinearEquiv.toLinearMap (implementing_unique (a p)
      (LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom p))
      (autOperator (a p)) (ha p) (autOperator_covariance (a p)))
  have hi : Function.Injective autAction.asGroupHom := fun _ _ h =>
    autAction_injective (congrArg Units.val h)
  let e : MulAut Group ≃* actionImage autAction := MonoidHom.ofInjective hi
  have hle : actionImage η ≤ actionImage autAction := by
    rintro _ ⟨p,rfl⟩
    exact ⟨a p,Units.ext (he p).symm⟩
  let j := e.symm.toMonoidHom.comp (inclusion hle)
  have hj : Function.Injective j := e.symm.injective.comp (inclusion_injective hle)
  intro hFF
  apply not_isFFModule_autAction
  apply hFF.map_equivariant (imageRepresentation η) autAction j hj (LinearEquiv.refl _ _)
  intro p x
  have hp := congrArg (fun z : actionImage autAction => z.val.val x)
    (e.apply_symm_apply (inclusion hle p))
  exact hp.symm
end BinaryLinearThree.NaturalDual
