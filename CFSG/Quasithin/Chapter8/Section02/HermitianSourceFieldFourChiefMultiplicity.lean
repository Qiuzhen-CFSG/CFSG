module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChiefMovement
public import Theory.Representation.ScalarMultiplicity.NaturalPlaneDisplacement
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# Scalar multiplicity on the original natural Hermitian chief section

The scalar commutant of the natural SL₂(4) module constructs a multiplicity
action for each subgroup whose image commutes with the original local
residual. The pure-tensor equation and entire action kernel are preserved.
The displacement formula below identifies a marked involution moving four
binary dimensions with a transvection over the original four-element field.

Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
The literal chosen-module application is in the companion Chapter12 module.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree
open scoped IsMulCommutative commutatorElement MatrixGroups Matrix
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] {J R A : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) J W}
set_option backward.isDefEq.respectTransparency false

/-- Natural homogeneous coordinates construct the scalar multiplicity action,
with precisely the original action kernel. -/
theorem natural_coordinates_multiplicity
    (hRJ : R ≤ J) (hAJ : A ≤ J)
    (m : ℕ) (eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1))
    (e : W ≃ₗ[ZMod 2] (Fin m → (Fin 2 → E 1)))
    (he : ∀ r w, e (ρ (inclusion hRJ r) w) =
      fun i => (eR (QuotientGroup.mk' (pCore 2 R) r)).val *ᵥ (e w i))
    (hc : ∀ (a : A) (r : R), Commute (ρ (inclusion hAJ a)) (ρ (inclusion hRJ r))) :
    ∃ μ : Representation (E 1) A (Fin m → E 1),
      (∀ a c v, e (ρ (inclusion hAJ a) (e.symm (fun i => c i • v))) =
        fun i => μ a c i • v) ∧
      μ.asGroupHom.ker = (ρ.asGroupHom.comp (inclusion hAJ)).ker := by
  let τ : Representation (ZMod 2) A (Fin m → (Fin 2 → E 1)) :=
    (e.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp (ρ.comp (inclusion hAJ))
  have hτ (a : A) (x) : τ a x = e (ρ (inclusion hAJ a) (e.symm x)) := rfl
  let σ : Representation (ZMod 2) SL(2,E 1) (Fin 2 → E 1) := {
    toFun g := (specialLinearNatural 2 g).toAddMonoidHom.toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (map_one (specialLinearNatural 2)) v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (map_mul (specialLinearNatural 2) g h) v }
  have hdiag (a : A) (g : SL(2,E 1)) (x : Fin m → (Fin 2 → E 1)) :
      τ a (fun i => σ g (x i)) = fun i => σ g (τ a x i) := by
    obtain ⟨r,hr⟩ := (eR.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 R))) g
    change eR (QuotientGroup.mk' (pCore 2 R) r) = g at hr
    have hd (w : W) : e (ρ (inclusion hRJ r) w) = fun i => σ g (e w i) := by
      rw [he,hr]
      rfl
    have hi : e.symm (fun i => σ g (x i)) = ρ (inclusion hRJ r) (e.symm x) := by
      apply e.injective
      rw [e.apply_symm_apply,hd,e.apply_symm_apply]
    have hcomm : ρ (inclusion hAJ a) (ρ (inclusion hRJ r) (e.symm x)) =
        ρ (inclusion hRJ r) (ρ (inclusion hAJ a) (e.symm x)) :=
      LinearMap.congr_fun (hc a r).eq (e.symm x)
    rw [hτ,hi,hcomm,hd]
    rfl
  obtain ⟨μ,hμ,hker⟩ := ScalarMultiplicity.exists_multiplicity_kernel σ
    (fun l hl => SL2NaturalOffenders.centralizer_scalar l.toAddMonoidHom hl) τ hdiag
  refine ⟨μ,hμ,hker.trans ?_⟩
  ext a
  change τ.asGroupHom a = 1 ↔ ρ.asGroupHom (inclusion hAJ a) = 1
  constructor
  · intro ha
    apply Units.ext
    apply LinearMap.ext
    intro w
    change ρ (inclusion hAJ a) w = w
    apply e.injective
    have hh : τ a (e w) = e w := LinearMap.congr_fun (congrArg Units.val ha) (e w)
    simpa only [hτ,e.symm_apply_apply] using hh
  · intro ha
    apply Units.ext
    apply LinearMap.ext
    intro x
    change τ a x = x
    rw [hτ]
    have hh : ρ (inclusion hAJ a) = 1 := congrArg Units.val ha
    rw [hh,Module.End.one_apply,e.apply_symm_apply]

variable [FiniteDimensional (ZMod 2) W]

/-- The exact binary displacement of the original actor is four times its
scalar multiplicity displacement. -/
theorem natural_multiplicity_displacement
    (hAJ : A ≤ J) (m : ℕ)
    (e : W ≃ₗ[ZMod 2] (Fin m → (Fin 2 → E 1)))
    (μ : Representation (E 1) A (Fin m → E 1))
    (he : ∀ a c v, e (ρ (inclusion hAJ a) (e.symm (fun i => c i • v))) =
      fun i => μ a c i • v) (a : A) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (inclusion hAJ a) - 1)) =
      4 * Module.finrank (E 1) (LinearMap.range (μ a - 1)) := by
  let τ : Representation (ZMod 2) A (Fin m → (Fin 2 → E 1)) :=
    (e.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp (ρ.comp (inclusion hAJ))
  have hτ (a : A) (x) : τ a x = e (ρ (inclusion hAJ a) (e.symm x)) := rfl
  have hd := ScalarMultiplicity.natural_plane_displacement τ μ he a
  have hE : Module.finrank (ZMod 2) (E 1) = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E 1)
    rw [card_E,Nat.card_zmod] at hh
    exact hh.symm
  have ht := NaturalTensor.operatorFixedCodim_eq_of_equiv
    (ρ (inclusion hAJ a)) (τ a) e (by intro w; rw [hτ,e.symm_apply_apply])
  change Module.finrank (ZMod 2) (LinearMap.range (ρ (inclusion hAJ a)-1)) =
    Module.finrank (ZMod 2) (LinearMap.range (τ a-1)) at ht
  rw [ht,hd,hE]

/-- The original marked involution becomes a genuine scalar transvection. -/
theorem natural_multiplicity_transvection
    (hAJ : A ≤ J) (m : ℕ)
    (e : W ≃ₗ[ZMod 2] (Fin m → (Fin 2 → E 1)))
    (μ : Representation (E 1) A (Fin m → E 1))
    (he : ∀ a c v, e (ρ (inclusion hAJ a) (e.symm (fun i => c i • v))) =
      fun i => μ a c i • v) (a : A) (ha : a^2=1)
    (hd : Module.finrank (ZMod 2) (LinearMap.range (ρ (inclusion hAJ a)-1))=4) :
    μ a * μ a = 1 ∧ Module.finrank (E 1) (LinearMap.range (μ a-1))=1 := by
  refine ⟨?_,?_⟩
  · rw [←map_mul,←pow_two,ha,map_one]
  · have hh := natural_multiplicity_displacement hAJ m e μ he a
    rw [hd] at hh
    omega
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
