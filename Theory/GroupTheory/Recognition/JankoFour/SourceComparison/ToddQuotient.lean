module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapAffine

/-!
# The original Todd twist is outer modulo Q A

The cubic-fixing odd-word correction descends through the literal Q A.
If its quotient action were inner, the parity affine map would supply an
inner conjugator fixing every translation. Faithfulness of the natural
six-part action forces that conjugator to be a translation itself. Its
conjugation formula would make the odd-word parity cocycle principal,
contrary to the proved parity criterion.

Consequently the actual point-group correction represents the nontrivial
class in the complete quotient automorphism calculation. Every automorphism
of I/(Q A) is inner, optionally followed by this correction, which already
lifts to the original M. No compatible comparison maps are supplied.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups
open Sporadic.Mathieu MathieuCode Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

private theorem affine_conjugator_right (w : Full) (x : OverlapAffine a)
    (hx : ∀ y : PlaneOverlap a, overlapAffineProjection a (planeOverlapToddTwist a w y) =
      x * overlapAffineProjection a y * x⁻¹) : x.right = 1 := by
  apply BinaryPermutation.naturalRepresentation_injective _
    (by rw [card_sextetPart]; decide)
  apply LinearMap.ext
  intro v
  obtain ⟨u,rfl⟩ := sextetCocodeParity_surjective a.sextet v
  have he := (hx (overlapToddVector a u)).symm
  rw [planeOverlapToddTwist_vector,overlapAffineProjection_vector] at he
  have hh := congrArg SemidirectProduct.left (mul_inv_eq_iff_eq_mul.mp he)
  change x.left * BinaryPermutation.naturalMulAction _ x.right
      (Multiplicative.ofAdd (sextetCocodeParity a.sextet u)) =
    Multiplicative.ofAdd (sextetCocodeParity a.sextet u) *
      BinaryPermutation.naturalMulAction _ 1 x.left at hh
  rw [map_one,MulAut.one_apply,mul_comm (Multiplicative.ofAdd _)] at hh
  rw [map_one]
  exact congrArg Multiplicative.toAdd (mul_left_cancel hh)

/-- The odd Todd displacement remains outer after killing the full Q A. -/
theorem cubicToddQuotientTwist_not_inner :
    ¬ ∃ x : OverlapCohomology.Original a.P, cubicToddQuotientTwist a = MulAut.conj x := by
  rintro ⟨x,hx⟩
  let b := cubicAffineProjection a x
  have hb (y : PlaneOverlap a) :
      overlapAffineProjection a (planeOverlapToddTwist a (cubicFixedWord a) y) =
        b * overlapAffineProjection a y * b⁻¹ := by
    have he := congrArg (cubicAffineProjection a) (MulEquiv.congr_fun hx (QuotientGroup.mk' _ y))
    rw [cubicToddQuotientTwist_mk,MulAut.conj_apply,map_mul,map_mul,map_inv,
      cubicAffineProjection_mk,cubicAffineProjection_mk] at he
    exact he
  have hr := affine_conjugator_right a _ b hb
  apply cubicFixedWord_odd a
  apply (toddCocycle_parity_principal_iff a.sextet (cubicFixedWord a)).mp
  refine ⟨b.left.toAdd,fun s => ?_⟩
  have he := hb (overlapToddComplement a s)
  have hl : (overlapAffineProjection a
      (planeOverlapToddTwist a (cubicFixedWord a) (overlapToddComplement a s))).left.toAdd =
        sextetCocodeParity a.sextet (toddCocycle (cubicFixedWord a) s.val) := by
    change sextetCocodeParity a.sextet (overlapToddCoordinates a
      (planeOverlapToddTwist a (cubicFixedWord a) (overlapToddComplement a s))).left.toAdd = _
    rw [overlapToddCoordinates_twist,overlapToddCoordinates_complement,toddTwist_apply]
    simp only [SemidirectProduct.left_inr,SemidirectProduct.right_inr,one_mul]
    rfl
  have hleft : (overlapAffineProjection a (overlapToddComplement a s)).left = 1 := by
    change Multiplicative.ofAdd (sextetCocodeParity a.sextet
      (overlapToddCoordinates a (overlapToddComplement a s)).left.toAdd) = 1
    rw [overlapToddCoordinates_complement]
    exact congrArg Multiplicative.ofAdd (map_zero _)
  have hright : (overlapAffineProjection a (overlapToddComplement a s)).right =
      sextetPartPerm a.sextet s := by
    change sextetPartPerm a.sextet (overlapSextetProjection a (overlapToddComplement a s)) = _
    congr 1
    exact Subtype.ext (congrArg SemidirectProduct.right (overlapToddCoordinates_complement a s))
  have hh := congrArg (fun t : OverlapAffine a => t.left.toAdd) he
  rw [hl] at hh
  simp only [SemidirectProduct.mul_left,SemidirectProduct.mul_right,SemidirectProduct.inv_left,
    hr,hleft,hright,map_one,MulAut.one_apply,mul_one,one_mul,inv_one] at hh
  change sextetCocodeParity a.sextet (toddCocycle (cubicFixedWord a) s.val) =
    b.left.toAdd + BinaryPermutation.naturalRepresentation _ (sextetPartPerm a.sextet s)
      (-b.left.toAdd) at hh
  rw [hh,map_neg,←sub_eq_add_neg]
  have hn (v : BinaryPermutation.natural (SextetPart a.sextet)) : -v=v := by
    rw [←neg_one_smul (ZMod 2) v,show (-1 : ZMod 2)=1 from rfl,one_smul]
  rw [sub_eq_add_neg,sub_eq_add_neg,hn,hn,add_comm]

/-- The correction coming from the original point group is the nontrivial
class in the independently computed automorphism group of I/(Q A). -/
theorem cubicToddQuotientTwist_outer_class :
    ∃ x : OverlapCohomology.Original a.P, cubicToddQuotientTwist a =
      MulAut.conj x * OverlapCohomology.originalQuadraticTwist h a.P := by
  obtain ⟨x,hx⟩ := OverlapCohomology.original_all_automorphisms h a.P (cubicToddQuotientTwist a)
  exact ⟨x,hx.resolve_left (fun he => cubicToddQuotientTwist_not_inner a ⟨x,he⟩)⟩

/-- Every quotient automorphism is inner, optionally followed by the actual
Todd correction. This identifies a representative which lifts to M. -/
theorem original_all_automorphisms_todd (f : MulAut (OverlapCohomology.Original a.P)) :
    ∃ x : OverlapCohomology.Original a.P, f = MulAut.conj x ∨
      f = MulAut.conj x * cubicToddQuotientTwist a := by
  obtain ⟨v,hv⟩ := cubicToddQuotientTwist_outer_class a
  obtain ⟨x,hx|hx⟩ := OverlapCohomology.original_all_automorphisms h a.P f
  · exact ⟨x,Or.inl hx⟩
  · refine ⟨x*v⁻¹,Or.inr ?_⟩
    rw [hx,hv,map_mul,map_inv,mul_assoc,inv_mul_cancel_left]
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
