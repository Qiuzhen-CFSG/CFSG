module
public import Theory.GroupAction.InnerCentralizerCardinality
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension

/-!
# Solvable radicals of centralizers in automorphism overgroups

For a centerless finite group, intersecting the centralizer of an automorphism
with the inner subgroup gives its literal fixed group. In any subgroup
containing all inner automorphisms, the quotient of that centralizer embeds
in the outer group. Thus two-group radicals in the fixed group, together
with a two-group outer quotient, give a two-group radical in the exact
centralizer. No equality with the full automorphism group is required.

Source application: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {B : Type*} [Group B] [Finite B]

/-- In an inner-containing automorphism group with two-group outer quotient,
the fixed-group radical controls the exact involution centralizer radical. -/
theorem centralizer_radical_isTwoGroup_of_fixed
    (hz : center B = ⊥) (ho : IsPGroup 2 (Outer B))
    (A : Subgroup (MulAut B)) (hA : innerSubgroup B ≤ A) (t : A)
    (hf : IsPGroup 2 (solvableRadical (t : MulAut B).fixedSubgroup)) :
    IsPGroup 2 (solvableRadical (centralizer ({t} : Set A))) := by
  let C := centralizer ({t} : Set A)
  let q : C →* Outer B :=
    (QuotientGroup.mk' (innerSubgroup B)).comp (A.subtype.comp C.subtype)
  have hi := conj_injective_of_center_eq_bot hz
  let f : (t : MulAut B).fixedSubgroup →* q.ker :=
    { toFun x := ⟨⟨⟨conj x.val,hA ⟨x.val,rfl⟩⟩, by
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        have hx := (mem_fixedSubgroup _ _).mp x.property
        have he : (t : MulAut B) * conj x.val * (t : MulAut B)⁻¹ = conj ((t : MulAut B) x.val) := by
          ext y
          simp
        rw [hx] at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm⟩,
        (QuotientGroup.eq_one_iff _).mpr ⟨x.val,rfl⟩⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_one conj
      map_mul' x y := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_mul conj x.val y.val }
  have hfbij : Function.Bijective f := by
    constructor
    · intro x y he
      exact Subtype.ext (hi (congrArg (fun k : q.ker => k.val.val.val) he))
    · intro k
      obtain ⟨x,hx⟩ := (QuotientGroup.eq_one_iff _).mp k.property
      have hcomm := congrArg Subtype.val (mem_centralizer_singleton_iff.mp k.val.property)
      change k.val.val.val * (t : MulAut B) = (t : MulAut B) * k.val.val.val at hcomm
      change conj x = k.val.val.val at hx
      have hfixed : (t : MulAut B) x = x := by
        apply hi
        have he : (t : MulAut B) * conj x * (t : MulAut B)⁻¹ = conj ((t : MulAut B) x) := by
          ext y
          simp
        rw [←he,hx,←hcomm,mul_inv_cancel_right]
      exact ⟨⟨x,(mem_fixedSubgroup _ _).mpr hfixed⟩,
        Subtype.ext (Subtype.ext (Subtype.ext hx))⟩
  let e := MulEquiv.ofBijective f hfbij
  let eR := (e.subgroupMap (solvableRadical (t : MulAut B).fixedSubgroup)).trans
    (MulEquiv.subgroupCongr (map_solvableRadical_equiv e))
  have hD : IsPGroup 2 (solvableRadical q.ker) := hf.of_equiv eR
  have hq : IsPGroup 2 (C ⧸ q.ker) :=
    (ho.to_subgroup q.range).of_equiv (QuotientGroup.quotientKerEquivRange q).symm
  exact radical_isTwoGroup_of_normal_two_quotient q.ker hD hq
end MulAut
