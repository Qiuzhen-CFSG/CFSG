module
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.FieldLifts
public import Theory.Representation.SL2.AutomorphismNatural
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic

/-!
# Elementary automorphisms on Hermitian four-spaces

The coefficient automorphism of an involution of SL₂ over the quadratic field
is either the identity or its quadratic conjugation. Both fix the defining
half-field. Comparing an arbitrary additive intertwiner with the canonical
inner-field lift leaves a scalar by the Hermitian commutant calculation.
Consequently an elementary actor normalizing the actual Hermitian component
acts linearly over the half-field.

Source: the Hermitian row of Aschbacher--Smith G.11.7, printed p.367.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.ZD.Linear
open scoped MatrixGroups
namespace Representation.OrthogonalFourMinus.RankOne.AmbientActions
open Representation.OrthogonalFourMinus.FiniteModel
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

private theorem coefficient_involution (σ : Field s ≃+* Field s) (hσ : σ^2=1) :
    σ=1 ∨ σ=conjugation s := by
  classical
  let : IsCyclic (Field s ≃+* Field s) := SL2NaturalOffenders.binaryFieldAut_isCyclic
  let : Finite (Field s ≃+* Field s) := Finite.of_injective
    (fun e : Field s ≃+* Field s => (e : Field s → Field s)) DFunLike.coe_injective
  let := Fintype.ofFinite (Field s ≃+* Field s)
  have hconj2 : conjugation s ^ 2 = 1 := by
    ext x
    exact conjugation_involutive s x
  have hconjne : conjugation s ≠ 1 := by
    obtain ⟨x,hx⟩ := exists_conjugation_ne s
    exact fun he => hx (DFunLike.congr_fun he x)
  by_contra! hne
  have hle : ({1,σ,conjugation s} : Finset (Field s ≃+* Field s)) ⊆
      Finset.univ.filter (fun a => a^2=1) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [hσ,hconj2]
  have hc : ({1,σ,conjugation s} : Finset (Field s ≃+* Field s)).card = 3 := by
    simp [hne.2,Ne.symm hne.1,Ne.symm hconjne]
  have hb := IsCyclic.card_pow_eq_one_le (α := Field s ≃+* Field s) (n := 2) (by decide)
  have hh := Finset.card_le_card hle
  rw [hc] at hh
  omega

/-- An additive lift of an involutory Hermitian component automorphism is
linear over the defining fixed field. -/
theorem involution_intertwiner_linear
    (α : MulAut SL(2,Field s)) (hα2 : α^2=1)
    (E : Space s ≃ₗ[ZMod 2] Space s)
    (hE : ∀ g w, E (SL2.BinarySmall.hermitian s g w) =
      SL2.BinarySmall.hermitian s (α g) (E w)) :
    ∀ (c : fixedField s) w, E (c • w) = c • E w := by
  let p := SL2AutomorphismNatural.parameterEquiv.symm α
  let g := p.left
  let σ := p.right
  have hα : α = MulAut.conj g * sl2FieldAut σ :=
    (SL2AutomorphismNatural.parameterEquiv.apply_symm_apply α).symm
  have hσ2 : σ^2=1 := by
    change SL2AutomorphismNatural.fieldAction α ^ 2 = 1
    rw [←map_pow,hα2,map_one]
  let e₀ : Space s ≃+ Space s := (fieldLift s σ).trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv ((action s).asGroupHom g)).toAddEquiv
  have he₀ (b : SL(2,Field s)) (w : Space s) :
      e₀ (action s b w) = action s (α b) (e₀ w) := by
    change action s g (fieldLift s σ (action s b w)) =
      action s (α b) (action s g (fieldLift s σ w))
    rw [hα]
    change action s g (fieldLift s σ (action s b w)) =
      action s (g * sl2FieldAut σ b * g⁻¹) (action s g (fieldLift s σ w))
    rw [fieldLift_action]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  let f : Space s →+ Space s := e₀.symm.toAddMonoidHom.comp E.toAddMonoidHom
  obtain ⟨c,hc⟩ := commuting_addHom_eq_scalar s f (by
    intro b w
    apply e₀.injective
    change e₀ (e₀.symm (E (action s b w))) = e₀ (action s b (e₀.symm (E w)))
    rw [e₀.apply_symm_apply,he₀,e₀.apply_symm_apply]
    exact hE b w)
  have hform (w : Space s) : E w = e₀ (c • w) := by
    have hh := congrArg e₀ (hc w)
    change e₀ (e₀.symm (E w)) = _ at hh
    rwa [e₀.apply_symm_apply] at hh
  have hσfix (d : fixedField s) : fieldRestriction s σ d = d := by
    rcases coefficient_involution s σ hσ2 with h | h
    · rw [h]
      rfl
    · rw [h]
      apply Subtype.ext
      exact d.property
  intro d w
  rw [hform,hform]
  change action s g (fieldLift s σ (c • d • w)) = d • action s g (fieldLift s σ (c • w))
  rw [smul_comm c d,fieldLift_smul,hσfix,map_smul]

/-- An elementary actor normalizing the actual Hermitian component acts
linearly over its defining half-field. -/
theorem elementary_normal_component_linear
    {D : Type*} [_root_.Group D]
    (ρ : Representation (ZMod 2) D (Space s))
    (L : Subgroup D) [L.Normal] (e : L ≃* SL(2,Field s))
    (hcoord : ∀ (l : L) w, ρ l w = SL2.BinarySmall.hermitian s (e l) w)
    (A : Subgroup D) [IsElementaryAbelian 2 A] :
    ∀ (a : A) (c : fixedField s) w, ρ a (c • w) = c • ρ a w := by
  let φ : D →* MulAut SL(2,Field s) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : D →* MulAut L)
  intro a
  have ha2 : (a : D)^2 = 1 := congrArg Subtype.val
    ((Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)) a)
  apply involution_intertwiner_linear s (φ a) (by rw [←map_pow,ha2,map_one])
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a))
  intro b w
  have he (l : L) (u : Space s) : SL2.BinarySmall.hermitian s (e l) u = ρ l u :=
    (hcoord l u).symm
  rw [←e.apply_symm_apply b,he]
  rw [←e.apply_symm_apply (φ a (e (e.symm b))),he]
  have hp : e.symm (φ a (e (e.symm b))) = MulAut.conjNormal (a : D) (e.symm b) := by
    change e.symm (e (MulAut.conjNormal (a : D) (e.symm (e (e.symm b))))) = _
    simp only [e.symm_apply_apply]
  rw [hp]
  change ρ a (ρ (e.symm b) w) = ρ ((a : D) * (e.symm b : D) * (a : D)⁻¹) (ρ a w)
  simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
end Representation.OrthogonalFourMinus.RankOne.AmbientActions
