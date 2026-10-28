module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.CenterAction
public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.Lifting
public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.RootCoverage

/-!
# Involution classes of the perfect four-cover in the source geometry

The field involution inverts the selected three-subgroup, which has no
common fixed point in Z(L). Its nontrivial action on the center allows the
projective field-coset calculation to lift, retaining an L-conjugator.
The source root plane together with Z(L) covers all involutions in L.

No fusion between distinct central elements under L is asserted. Fusion of
representatives in the source V under the larger ambient group belongs to
the chapter adapter.
Source: Aschbacher--Smith, proof of 15.3.38, printed pp.1136--1137,
combined manuscript of 1 March 2004.
-/

public section
namespace Matrix.PSL3Four.InvolutionClasses
open Subgroup ExtendedCentralizer
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- In the source three-subgroup geometry, the field coset has one L-class. -/
theorem field_coset_conjugate_of_three_geometry (d : Overgroup L)
    (X : Subgroup I) (hX : IsPGroup 3 X) (f : I) (hf : f ^ 2 = 1)
    (hfield : IsConj pslFrobenius (projectiveAction L d.cover f))
    (hinv : ∀ x : X, f * (x : I) * f⁻¹ = (x : I)⁻¹)
    (hfree : ((center L).map L.subtype) ⊓ centralizer (X : Set I) = ⊥)
    (x : I) (hx : x ^ 2 = 1) (hxL : x * f⁻¹ ∈ L) :
    ∃ b : L, (b : I) * f * (b : I)⁻¹ = x := by
  exact field_coset_conjugate d f hf hfield
    (field_moves_center_of_three_geometry d.cover X hX f hinv hfree) x hx hxL

/-- Specialization to the marked graph/field normalizer on the actual cover. -/
theorem normalizer_field_coset_conjugate {d : Overgroup L} (n : NormalizerGeometry d)
    (hfree : ((center L).map L.subtype) ⊓
      centralizer (((n.X : Subgroup n.YS).map n.YS.subtype) : Set I) = ⊥)
    (x : I) (hx : x ^ 2 = 1) (hxL : x * n.fieldI⁻¹ ∈ L) :
    ∃ b : L, (b : I) * n.fieldI * (b : I)⁻¹ = x := by
  exact field_coset_conjugate d n.fieldI n.field_sq n.field_frobenius.symm
    (normalizer_field_moves_center_of_fixed_free n hfree) x hx hxL

/-- The compatible lifts use the supplied quotient, without changing coordinates. -/
theorem field_coset_conjugate_of_coverActions (d : Overgroup L)
    (a : CoverActions L d.cover) (X : Subgroup I) (hX : IsPGroup 3 X)
    (f : I) (hf : f ^ 2 = 1) (ha : MulAut.conjNormal f = a.field)
    (hinv : ∀ x : X, f * (x : I) * f⁻¹ = (x : I)⁻¹)
    (hfree : ((center L).map L.subtype) ⊓ centralizer (X : Set I) = ⊥)
    (x : I) (hx : x ^ 2 = 1) (hxL : x * f⁻¹ ∈ L) :
    ∃ b : L, (b : I) * f * (b : I)⁻¹ = x := by
  have he : projectiveAction L d.cover f = pslFrobenius := by
    change d.cover.toCover.autMap d.cover.ker_eq_center (MulAut.conjNormal f) = _
    rw [ha, a.field_descends]
  exact field_coset_conjugate_of_three_geometry d X hX f hf
    (he ▸ IsConj.refl _) hinv hfree x hx hxL

end Matrix.PSL3Four.InvolutionClasses
