module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.BlockExtensions
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Reductions for the binary SL₃(4) extension calculation

Changing the section by the central cross block makes that block zero whenever
it satisfies the central quadratic equation. The remaining cross blocks then
intertwine the two central operators, hence respect their canonical F₄ scalars.
This reduction does not confuse the ordinary scalar structures of the natural
and dual modules. Inverse transpose exchanges both constituent labels and
transports actual representation equivalences, reducing the four ordered cases
to one homogeneous case and one mixed case.

Elementary transvections form a proved finite generating family. Their cross
blocks determine a cocycle, and a coboundary identity on them gives an actual
module equivalence. No vanishing or completeness assertion is made here.

Source context: James (1973), Lemma 8.3, cited in Aschbacher–Smith H.12.1,
printed pp.393–394; p.394 describes the point restriction as an extension.
The proofs here are the elementary block identities and Gaussian elimination.
-/

@[expose] public noncomputable section

namespace Representation.SL3FourLocalCatalogue.BlockCocycle
variable {a b : Constituent}

private lemma end_add_self (f : W →ₗ[ZMod 2] W) : f + f = 0 := by
  rw [← two_smul (ZMod 2) f, show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- The cocycle obtained by changing a binary linear section. -/
def shift (c : BlockCocycle a b) (f : W →ₗ[ZMod 2] W) : BlockCocycle a b where
  value g := c.value g + (constituent a g).comp f + f.comp (constituent b g)
  one := by
    simpa only [map_one, c.one, Module.End.one_eq_id, LinearMap.id_comp,
      LinearMap.comp_id, zero_add] using end_add_self f
  mul g h := by
    simp only [c.mul, map_mul, Module.End.mul_eq_comp, LinearMap.comp_add,
      LinearMap.add_comp, LinearMap.comp_assoc]
    have hz := end_add_self ((constituent a g).comp (f.comp (constituent b h)))
    linear_combination (norm := abel) -hz

/-- The actual intertwining equivalence for a change of section. -/
def shiftEquiv (c : BlockCocycle a b) (f : W →ₗ[ZMod 2] W) :
    c.representation.Equiv (shift c f).representation := by
  apply equivOfCoboundary c (shift c f) f
  intro g
  change c.value g + f.comp (constituent b g) =
    (constituent a g).comp f + (c.value g + (constituent a g).comp f + f.comp (constituent b g))
  have hz : (constituent a g).comp f + (constituent a g).comp f = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
  linear_combination (norm := abel) -hz

/-- Change the section by the central cross block itself. -/
def normalize (c : BlockCocycle a b) : BlockCocycle a b := shift c (c.value z)

/-- The central quadratic equation makes the normalized central block vanish. -/
lemma normalize_value_z (c : BlockCocycle a b) (hc : c.IsCentral) :
    (normalize c).value z = 0 := by
  change c.value z + (constituent a z).comp (c.value z) +
    (c.value z).comp (constituent b z) = 0
  change (constituent a z).comp (c.value z) +
    (c.value z).comp (constituent b z) + c.value z = 0 at hc
  linear_combination (norm := abel) hc

/-- Normalized cross blocks intertwine the two central operators. -/
lemma normalized_intertwines (c : BlockCocycle a b) (hc : c.value z = 0) (g : SL) :
    (constituent a z).comp (c.value g) = (c.value g).comp (constituent b z) := by
  have h := congrArg c.value (SL3FourNaturalDual.centralScalar_commute g)
  simpa only [c.mul, hc, LinearMap.zero_comp, LinearMap.comp_zero, zero_add, add_zero] using h

/-- A zero central block satisfies the central polynomial. -/
lemma isCentral_of_value_z_eq_zero (c : BlockCocycle a b) (hc : c.value z = 0) :
    c.IsCentral := by
  simp only [IsCentral, hc, LinearMap.comp_zero, LinearMap.zero_comp, add_zero]

/-- Normalization preserves the central quadratic condition. -/
lemma normalize_isCentral (c : BlockCocycle a b) (hc : c.IsCentral) :
    (normalize c).IsCentral :=
  isCentral_of_value_z_eq_zero _ (normalize_value_z c hc)

/-- Normalized blocks respect the canonical central-field scalars on their endpoints. -/
lemma normalized_field_smul (c : BlockCocycle a b) (hc : c.value z = 0)
    (g : SL) (r : F) (v : W) :
    c.value g (r.re • v + r.im • (constituent b z) v) =
      r.re • c.value g v + r.im • (constituent a z) (c.value g v) := by
  rw [map_add, map_smul, map_smul]
  congr 1
  exact congrArg (r.im • ·) (LinearMap.congr_fun (normalized_intertwines c hc g).symm v)

/-- Between normalized blocks, the permitted section changes intertwine the central operators. -/
lemma shift_value_z (c : BlockCocycle a b) (hc : c.value z = 0)
    (f : W →ₗ[ZMod 2] W) :
    (shift c f).value z = 0 ↔ (constituent a z).comp f = f.comp (constituent b z) := by
  change c.value z + (constituent a z).comp f + f.comp (constituent b z) = 0 ↔ _
  rw [hc, zero_add]
  constructor
  · intro h
    have hz := end_add_self (f.comp (constituent b z))
    linear_combination (norm := abel) h - hz
  · intro h
    rw [h]
    exact end_add_self _

end Representation.SL3FourLocalCatalogue.BlockCocycle

namespace Representation.SL3FourLocalCatalogue

/-- Exchange the natural and inverse-transpose constituent labels. -/
def Constituent.flip : Constituent → Constituent
  | .natural => .dual
  | .dual => .natural

/-- Exchanging the two labels twice is the identity. -/
lemma Constituent.flip_flip (a : Constituent) : a.flip.flip = a := by cases a <;> rfl

/-- Exchanging a label is precomposition with the actual inverse-transpose automorphism. -/
lemma constituent_flip (a : Constituent) (g : SL) :
    constituent a.flip g = constituent a (Matrix.SpecialLinearGroup.inverseTranspose g) := by
  cases a with
  | natural => rfl
  | dual =>
    change SL3FourNaturalDual.natural g =
      SL3FourNaturalDual.natural (Matrix.SpecialLinearGroup.inverseTranspose
        (Matrix.SpecialLinearGroup.inverseTranspose g))
    rw [SL3FourNaturalDual.inverseTranspose_involutive]

/-- The finite parameter set for all elementary transvections. -/
abbrev RootIndex := {p : Fin 3 × Fin 3 // p.1 ≠ p.2} × F

/-- The actual elementary matrix specified by its two indices and field parameter. -/
def rootGenerator (r : RootIndex) : SL :=
  Matrix.SpecialLinearGroup.transvection r.1.property r.2

/-- The displayed finite family generates the entire special linear group. -/
lemma rootGenerators_generate : Subgroup.closure (Set.range rootGenerator) = ⊤ := by
  apply top_unique
  intro g _
  apply OneCohomology.SLHigherNatural.transvection_induction
    (fun g => g ∈ Subgroup.closure (Set.range rootGenerator)) ?_ ?_ g
  · intro i j hij t
    exact Subgroup.subset_closure ⟨(⟨(i, j), hij⟩, t), rfl⟩
  · exact fun _ _ => Subgroup.mul_mem _

namespace BlockCocycle
variable {a b : Constituent}

/-- Precompose every block with inverse transpose, exchanging both diagonal actions. -/
def graphTwist (c : BlockCocycle a b) : BlockCocycle a.flip b.flip where
  value g := c.value (Matrix.SpecialLinearGroup.inverseTranspose g)
  one := by rw [map_one, c.one]
  mul g h := by rw [map_mul, c.mul, constituent_flip, constituent_flip]

/-- The twisted representation is the original action precomposed with inverse transpose. -/
lemma graphTwist_apply (c : BlockCocycle a b) (g : SL) (v : W × W) :
    c.graphTwist.representation g v =
      c.representation (Matrix.SpecialLinearGroup.inverseTranspose g) v := by
  simp only [representation_apply, constituent_flip, graphTwist]

/-- Inverse transpose preserves vanishing of the central cross block. -/
lemma graphTwist_normalized (c : BlockCocycle a b) (hc : c.value z = 0) :
    c.graphTwist.value z = 0 := by
  change c.value (Matrix.SpecialLinearGroup.inverseTranspose z) = 0
  rw [central_inverseTranspose, pow_two, c.mul, hc]
  simp

/-- Precomposition transports an actual intertwining equivalence. -/
def graphTwistEquiv {c d : BlockCocycle a b} (e : c.representation.Equiv d.representation) :
    c.graphTwist.representation.Equiv d.graphTwist.representation := by
  refine .mk e.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  change e (c.graphTwist.representation g v) = d.graphTwist.representation g (e v)
  rw [graphTwist_apply, graphTwist_apply]
  exact LinearMap.congr_fun (e.isIntertwining' _) v

/-- Twisting twice returns to the original representation on the same carrier. -/
def graphTwistTwiceEquiv (c : BlockCocycle a b) :
    c.graphTwist.graphTwist.representation.Equiv c.representation := by
  refine .mk (LinearEquiv.refl (ZMod 2) (W × W)) ?_
  intro g
  apply LinearMap.ext
  intro v
  change c.graphTwist.graphTwist.representation g v = c.representation g v
  rw [graphTwist_apply, graphTwist_apply, SL3FourNaturalDual.inverseTranspose_involutive]

/-- Cocycle values on all elementary transvections determine the cocycle. -/
lemma ext_transvections (c d : BlockCocycle a b)
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (t : F),
      c.value (Matrix.SpecialLinearGroup.transvection hij t) =
      d.value (Matrix.SpecialLinearGroup.transvection hij t)) : c = d := by
  suffices hv : c.value = d.value by cases c; cases d; cases hv; rfl
  funext g
  apply OneCohomology.SLHigherNatural.transvection_induction (fun g => c.value g = d.value g) h ?_ g
  intro g h hg hh
  rw [c.mul, d.mul, hg, hh]

/-- A coboundary comparison on the proved generating family gives a module equivalence. -/
def equivOfTransvectionCoboundary (c d : BlockCocycle a b) (f : W →ₗ[ZMod 2] W)
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (t : F),
      c.value (Matrix.SpecialLinearGroup.transvection hij t) +
        f.comp (constituent b (Matrix.SpecialLinearGroup.transvection hij t)) =
      (constituent a (Matrix.SpecialLinearGroup.transvection hij t)).comp f +
        d.value (Matrix.SpecialLinearGroup.transvection hij t)) :
    c.representation.Equiv d.representation := by
  have he : shift c f = d := by
    apply ext_transvections
    intro i j hij t
    have hh := h i j hij t
    have hz :
        (constituent a (Matrix.SpecialLinearGroup.transvection hij t)).comp f +
          (constituent a (Matrix.SpecialLinearGroup.transvection hij t)).comp f = 0 := by
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
    change c.value _ + (constituent a _).comp f + f.comp (constituent b _) = _
    linear_combination (norm := abel) hh + hz
  exact he ▸ shiftEquiv c f

end BlockCocycle
end Representation.SL3FourLocalCatalogue
