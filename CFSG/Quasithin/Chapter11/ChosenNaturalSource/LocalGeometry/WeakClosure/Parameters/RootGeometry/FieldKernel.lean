module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.Linear
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Coefficients

/-!
# Removing field actors through an original central cover

The coefficient kernel of an elementary two-group has index at most two.
The A₂ condition identifies its fixed space with that of the whole actor.
Exact lifting of inner fixed vectors carries this equality to the natural
quotient, where a nonzero fixed field line forces trivial coefficient action.
This argument retains nonsplit central attachments. The symplectic and G₂
source applications discharge the field-linear inner-actor premise.

Source: Aschbacher--Smith, I.2.3, B.4.6(9), and 11.2.2(4), printed p.768.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootActors
open SymplecticConjugatePair.Ambient.SemilinearCoefficients

variable {H F W X : Type*} [Group H] [Field F] [Finite F]
  [AddCommGroup W] [Module F W] [Module (ZMod 2) W] [Nontrivial W]
  [FiniteDimensional (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]

/-- The A₂ condition on a central cover removes the coefficient action whenever
field-linear elementary actors are inner and inner fixed vectors lift. -/
theorem two_family_inner_of_fixed_lifting
    (K : Subgroup H) (σ : Representation (ZMod 2) H X)
    (ρ : Representation (ZMod 2) H W) (q : X →ₗ[ZMod 2] W)
    (hq : Function.Surjective q) (he : ∀ a v, q (σ a v) = ρ a (q v))
    (π : H →* (F ≃+* F))
    (hsemi : ∀ a c v, ρ a (c • v) = π a c • ρ a v)
    (hinner : ∀ a : H, a ^ 2 = 1 → π a = 1 → a ∈ K)
    (hlift : ∀ a ∈ K, ∀ v, ρ a (q v) = q v → σ a v = v)
    {A : Subgroup H} (hA : A ∈ fixedSpaceFamily σ 2) : A ≤ K := by
  let := hA.2.1.2
  let B := A ⊓ π.ker
  have hBK : B ≤ K := fun b hb => hinner b
    (elemPow_eq_one_of_isElementaryAbelian b hb.1) hb.2
  have hcor : Nat.log 2 (B.relIndex A) < 2 := by
    have hh := Nat.log_mono_right (kernel_relativeIndex_le_two π
      (inferInstance : IsElementaryAbelian 2 A)) (b := 2)
    norm_num at hh
    change Nat.log 2 ((A ⊓ π.ker).relIndex A) < 2
    omega
  have hfix := hA.2.2 B inf_le_left hcor
  have hBfix : fixedSpace σ B = (fixedSpace ρ B).comap q := by
    ext v
    constructor
    · intro hv b
      exact (he b v).symm.trans (congrArg q (hv b))
    · intro hv b
      exact hlift b (hBK b.property) v (hv b)
  have hquot : fixedSpace ρ A = fixedSpace ρ B := by
    apply le_antisymm
    · intro v hv b
      exact hv ⟨b, b.property.1⟩
    · intro v hv
      obtain ⟨w,rfl⟩ := hq v
      have hw : w ∈ fixedSpace σ B := hBfix.symm ▸ hv
      have hwA : w ∈ fixedSpace σ A := hfix.symm ▸ hw
      intro a
      exact (he a w).symm.trans (congrArg q (hwA a))
  have hker : A ≤ π.ker := le_kernel_of_fixedSpace_eq ρ π hsemi
    ((IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left) inf_le_right hquot
  exact fun a ha => hinner a (elemPow_eq_one_of_isElementaryAbelian a ha) (hker ha)

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Exact lifting for every actor in the literal component image, including
nonsplit symplectic and G₂ central attachments. -/
theorem original_layer_fixed_lifts (c : Coordinates D S.field)
    (ρ : Representation (ZMod 2) (Automizer V) c.Space)
    (hres : ∀ (a : inducedAutomizer V L) v,
      ρ (a : Automizer V) v = c.modelAction (layerEquiv D S c a) v) :
    letI := D.elementary
    ∀ a ∈ inducedAutomizer V L, ∀ v,
      ρ a (projectionLinear D S c v) = projectionLinear D S c v →
        automizerRepresentation V a v = v := by
  let := D.elementary
  intro a ha v hv
  obtain ⟨l,hl⟩ := layerAction_surjective D ⟨a,ha⟩
  have he : (layerAction D l : Automizer V) = a := congrArg Subtype.val hl
  have hv' : c.modelAction (c.quotientMap l) (c.projection v.toMul).toAdd =
      (c.projection v.toMul).toAdd := by
    rw [← layerEquiv_apply D S c, ← hres, he]
    exact hv
  have hc := (NaturalFixedSpaces.centralizes_vector_iff D S c l v.toMul).mpr hv'
  rw [← he]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mpr hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootActors
