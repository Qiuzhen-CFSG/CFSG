module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.BinaryConjugationSection.Relabel
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# Full linear coordinates from a faithful binary section

A faithful action on a binary n-space fills GL(n,2) when the two finite
groups have the same order. Transport the action through specified linear
coordinates and identify the resulting faithful image by equality of orders.
The relabelled section keeps the original actor projection and subgroup
kernel, and its coordinate formula retains the chosen linear equivalence.

The source application constructs the natural marking in Aschbacher--Smith
13.8.29 from F.9.2 and the orders in 13.8.27, printed pp.963--964.
-/

public noncomputable section
open Subgroup Representation BinaryLinear.OuterCyclic
namespace Representation.BinaryConjugationSection
variable {G J W : Type*} [Group G] [Group J]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H A B : Subgroup G} {σ : Representation (ZMod 2) J W}

/-- Identify the actual faithful action with the full linear group in specified coordinates. -/
theorem full_linear_coordinates
    (q : H →* J) (c : BinaryConjugationSection H A B (σ.comp q))
    (hf : Function.Injective σ) {n : ℕ}
    (E : W ≃ₗ[ZMod 2] Space n)
    (hcard : Nat.card J = Nat.card (LinearGroup n)) :
    ∃ (e : J ≃* LinearGroup n)
      (d : BinaryConjugationSection H A B
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (e.toMonoidHom.comp q))),
      ∀ x : A, (d.coordinates x).toAdd = E (c.coordinates x).toAdd := by
  let C : (W →ₗ[ZMod 2] W)ˣ ≃* LinearGroup n :=
    (Units.mapEquiv E.conjRingEquiv.toMulEquiv).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space n))
  let f := C.toMonoidHom.comp σ.asGroupHom
  have hi : Function.Injective f := C.injective.comp
    (fun x y h => hf (congrArg Units.val h))
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  let e : J ≃* LinearGroup n := MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hcard⟩)
  let ρ : Representation (ZMod 2) J (Space n) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom
  let R : σ.Equiv ρ := Representation.Equiv.mk E (by
    intro g
    apply LinearMap.ext
    intro w
    change E (σ g w) = E (σ g (E.symm (E w)))
    rw [E.symm_apply_apply])
  exact ⟨e,c.relabel q R,fun _ => rfl⟩


end Representation.BinaryConjugationSection
