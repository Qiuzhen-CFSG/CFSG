module

public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.GroupTheory.CoveringMultiplierAction
public import Theory.GroupAction.CardFourCubic
public import Theory.SpecificGroups.Suzuki.FieldAutomorphism

/-!
# Normalizer actions on Rudvalis component multipliers

For an actual subgroup I of the degree-4060 Rudvalis model, restrict
conjugation by N_Ru(I) to I, lift it uniquely to a universal cover, and
restrict that lift to the covering kernel. These are the literal maps
needed for I.2.2(7a), rather than an independently chosen four-group action.

A moved kernel element and the order-four multiplier calculation suffice
to prove irreducibility for an order-three normalizer element. The concrete
Sz(8) layer, normalizer element and moved element still have to be supplied.
This module does not assert their existence or the splitting conclusion.
Source: Aschbacher--Smith, I.2.2(7), printed pp.410,412--413.
-/

namespace Rudvalis.CoveringIncidence

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups

variable {I : Subgroup Model} [IsQuasisimple I]
variable {U : Type} [Group U] [Finite U] [IsQuasisimple U]

/-- The canonical action of the actual normalizer on a chosen universal kernel. -/
@[expose] public noncomputable def normalizerMultiplierAction
    (f : Covering U I) (hf : Covering.IsUniversal.{0,0,0} f) :
    normalizer (I : Set Model) →* MulAut f.toMonoidHom.ker :=
  (Covering.multiplierAction f hf).comp I.normalizerMonoidHom

/-- Evaluation is by the unique lift of actual left conjugation on I. -/
@[simp] public theorem normalizerMultiplierAction_apply
    (f : Covering U I) (hf : Covering.IsUniversal.{0,0,0} f)
    (y : normalizer (I : Set Model)) (x : f.toMonoidHom.ker) :
    (normalizerMultiplierAction f hf y x : U) =
      hf.liftMulAut (I.normalizerMonoidHom y) x := rfl

/-- An order-three normalizer element induces an action whose cube is one. -/
public theorem normalizerMultiplierAction_cube
    (f : Covering U I) (hf : Covering.IsUniversal.{0,0,0} f)
    (y : normalizer (I : Set Model)) (hy : (y : Model) ^ 3 = 1) :
    normalizerMultiplierAction f hf y ^ 3 = 1 := by
  rw [← map_pow, show y ^ 3 = 1 from Subtype.ext hy, map_one]

/-- Nontriviality is witnessed on the literal covering kernel. -/
public theorem normalizerMultiplierAction_ne_one
    (f : Covering U I) (hf : Covering.IsUniversal.{0,0,0} f)
    (y : normalizer (I : Set Model))
    (hmoved : ∃ x : f.toMonoidHom.ker,
      hf.liftMulAut (I.normalizerMonoidHom y) x ≠ (x : U)) :
    normalizerMultiplierAction f hf y ≠ 1 := by
  intro he
  obtain ⟨x, hx⟩ := hmoved
  exact hx (congrArg (fun a : MulAut f.toMonoidHom.ker => (a x : U)) he)

/-- On the actual multiplier of order four, the cubic normalizer action has
no proper nontrivial invariant subgroup. For E₄ this is F₂-irreducibility. -/
public theorem multiplier_invariant_subgroup
    (f : Covering U I) (hf : Covering.IsUniversal.{0,0,0} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (y : normalizer (I : Set Model)) (hy : (y : Model) ^ 3 = 1)
    (hmoved : ∃ x : f.toMonoidHom.ker,
      hf.liftMulAut (I.normalizerMonoidHom y) x ≠ (x : U))
    (H : Subgroup f.toMonoidHom.ker)
    (hH : ∀ x ∈ H, normalizerMultiplierAction f hf y x ∈ H) :
    H = ⊥ ∨ H = ⊤ :=
  Theory.GroupAction.CardFourCubic.invariant_subgroup hfour
    (normalizerMultiplierAction f hf y)
    (normalizerMultiplierAction_cube f hf y hy)
    (normalizerMultiplierAction_ne_one f hf y hmoved) H hH

/-- The same literal action has no nontrivial invariant map to a central
group of order at most two. This is the multiplier obstruction used in (7a). -/
public theorem invariant_multiplier_hom_eq_one
    (f : Covering U I) (hf : Covering.IsUniversal.{0,0,0} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (y : normalizer (I : Set Model)) (hy : (y : Model) ^ 3 = 1)
    (hmoved : ∃ x : f.toMonoidHom.ker,
      hf.liftMulAut (I.normalizerMonoidHom y) x ≠ (x : U))
    {Z : Type*} [Group Z] [Finite Z] (hZ : Nat.card Z ≤ 2)
    (g : f.toMonoidHom.ker →* Z)
    (hg : ∀ x, g (normalizerMultiplierAction f hf y x) = g x) : g = 1 :=
  Theory.GroupAction.CardFourCubic.invariant_hom_eq_one hfour hZ
    (normalizerMultiplierAction f hf y)
    (normalizerMultiplierAction_cube f hf y hy)
    (normalizerMultiplierAction_ne_one f hf y hmoved) g hg

/-- A literal comparison with the matrix Sz(8) field automorphism converts
its moved universal-kernel element to the Rudvalis normalizer witness. -/
public theorem multiplier_invariant_subgroup_of_field
    (f : Covering U I) (hf : Covering.IsUniversal.{0,0,0} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (e : I ≃* SuzukiMatrixGroup 1)
    (y : normalizer (I : Set Model)) (hy : (y : Model) ^ 3 = 1)
    (hfield : I.normalizerMonoidHom y =
      MulAut.congr e.symm (suzukiFieldAutomorphism 1))
    (hmoved : ∃ x : f.toMonoidHom.ker,
      hf.liftMulAut (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) x ≠ (x : U))
    (H : Subgroup f.toMonoidHom.ker)
    (hH : ∀ x ∈ H, normalizerMultiplierAction f hf y x ∈ H) :
    H = ⊥ ∨ H = ⊤ := by
  apply multiplier_invariant_subgroup f hf hfour y hy _ H hH
  rwa [hfield]

end Rudvalis.CoveringIncidence
