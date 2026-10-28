module

public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.PairCandidates
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondNormalizer.Characteristic
/-!
# Intrinsic restrictions on the two Sylow generator images

The unique nonidentity central element is fixed by every automorphism.
The centralizer of the intrinsic second center is characteristic, contains
all normal forms with index below 1024, and excludes `s8`. Consequently
no image of `s8` can have such an index.

Source: Parrott (1972), §5, p.683, using the certified Atlas marking and
the existing identification of the second center. This is the structural
part of the finite generator-pair exhaustion.
-/

@[expose] public section
namespace Tits.SharpOuterBound.LocalImageBound.SylowPairExhaustion.Intrinsic
open Subgroup ExceptionalParabolics RelativeParabolicNormalizers
open OuterOddSubgroups.OverlapCentralizers

def perm : S →* Equiv.Perm (Fin 1600) where
  toFun x := x.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem perm_injective : Function.Injective perm := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

theorem gen_perm (i : Fin 8) :
    perm (sylowGenerator i) = Packed.generator (⟨i.val + 2, by omega⟩ : Fin 10) := by
  change (atlas1600ParrottAssignment _).val = _
  fin_cases i <;> simp [atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation, Packed.generator]

theorem nf_perm (n : Fin 2048) :
    perm (atlas1600SylowTwoEquiv n) = Atlas1600SylowTwoCertificate.normalForm n := by
  change (atlas1600SylowTwoEquiv n).val.val = _
  rw [atlas1600SylowTwoEquiv_apply, atlas1600SylowTwoNormalForm_val]
  rfl

def z : S := ⟨atlas1600R5, atlas1600R5_mem_sylowTwo⟩

theorem z_perm : perm z = SecondCenterCertificate.x := by
  change atlas1600R5.val = _
  rw [atlas1600R5_eq]
  change (atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .s5).val ^ 2 = _
  simp only [atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation,
    SecondCenterCertificate.x]

theorem fixes_z (f : MulAut S) : f z = z := by
  have hm : f z ∈ center S :=
    (characteristic_iff_le_comap.mp inferInstance f) atlas1600R5_mem_center_sylowTwo
  rcases (atlas1600SylowTwo_mem_center_iff _).mp hm with h | h
  · have hf : f z = 1 := Subtype.ext h
    have hz : z = 1 := f.map_eq_one_iff.mp hf
    exact (atlas1600R5_ne_one (congrArg Subtype.val hz)).elim
  · exact Subtype.ext h

local notation "Z₂" => secondCenter.subgroupOf S
local instance : (Z₂).Characteristic := secondCenter_characteristic

private def C : Subgroup S := centralizer (Z₂ : Set S)
private instance : C.Characteristic := inferInstanceAs (centralizer (Z₂ : Set S)).Characteristic

private theorem mate_perm : secondCenterMate.val = SecondCenterCertificate.y := by
  change (atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .s2).val *
    (atlas1600ParrottAssignment .s3).val ^ 2 = _
  simp only [atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation,
    SecondCenterCertificate.y]

private theorem gen_perm' (i : Fin 8) :
    perm (sylowGenerator i) = Atlas1600SylowTwoCenterCertificate.generator i := by
  rw [gen_perm]
  fin_cases i <;> rfl

private theorem gen_commutes_mate (i : Fin 8) (hi : i ≠ 7) :
    (sylowGenerator i).val * secondCenterMate =
      secondCenterMate * (sylowGenerator i).val := by
  have hc : (sylowGenerator i).val * secondCenterMate * ((sylowGenerator i).val)⁻¹ =
      secondCenterMate := by
    apply Subtype.ext
    change perm (sylowGenerator i) * secondCenterMate.val *
      (perm (sylowGenerator i))⁻¹ = secondCenterMate.val
    simpa only [gen_perm', mate_perm, if_neg hi] using SecondCenterCertificate.sylow_y i
  exact (mul_inv_eq_iff_eq_mul).mp hc

private theorem gen_mem_C (i : Fin 8) (hi : i ≠ 7) : sylowGenerator i ∈ C := by
  have hx : (sylowGenerator i).val * atlas1600R5 = atlas1600R5 * (sylowGenerator i).val :=
    congrArg Subtype.val (mem_center_iff.mp atlas1600R5_mem_center_sylowTwo (sylowGenerator i))
  intro w hw
  change w.val ∈ secondCenter at hw
  apply Subtype.ext
  change w.val * (sylowGenerator i).val = (sylowGenerator i).val * w.val
  rcases mem_secondCenter_iff.mp hw with he | he | he | he
  · simp only [he, one_mul, mul_one]
  · rw [he, gen_commutes_mate i hi]
  · rw [he, hx]
  · rw [he, mul_assoc, ← gen_commutes_mate i hi, ← mul_assoc, ← hx, mul_assoc]

private theorem last_not_mem_C : sylowGenerator 7 ∉ C := by
  intro h
  have hm : secondCenterMate ∈ secondCenter := mem_sup_right (mem_zpowers _)
  let y : S := ⟨secondCenterMate, secondCenter_le_sylow hm⟩
  have hh := congrArg Subtype.val (h y hm)
  change secondCenterMate * (sylowGenerator 7).val = (sylowGenerator 7).val * secondCenterMate at hh
  have hc : (sylowGenerator 7).val * secondCenterMate * ((sylowGenerator 7).val)⁻¹ =
      atlas1600R5 * secondCenterMate := by
    apply Subtype.ext
    change perm (sylowGenerator 7) * secondCenterMate.val * (perm (sylowGenerator 7))⁻¹ =
      atlas1600R5.val * secondCenterMate.val
    simpa only [gen_perm', mate_perm, show atlas1600R5.val = SecondCenterCertificate.x from z_perm, if_true] using SecondCenterCertificate.sylow_y 7
  have he : atlas1600R5 * secondCenterMate = secondCenterMate := by
    rw [← hc, ← hh, mul_assoc, mul_inv_cancel, mul_one]
  exact atlas1600R5_ne_one (mul_right_cancel (he.trans (one_mul _).symm))

private theorem low_mem_C (n : Fin 2048) (hn : n.val < 1024) : atlas1600SylowTwoEquiv n ∈ C := by
  have he : atlas1600SylowTwoEquiv n =
      sylowGenerator 0 ^ (n.val % 2) * sylowGenerator 1 ^ (n.val / 2 % 2) *
      sylowGenerator 2 ^ (n.val / 4 % 4) * sylowGenerator 3 ^ (n.val / 16 % 2) *
      sylowGenerator 4 ^ (n.val / 32 % 4) * sylowGenerator 5 ^ (n.val / 128 % 2) *
      sylowGenerator 6 ^ (n.val / 256 % 4) * sylowGenerator 7 ^ (n.val / 1024 % 2) := by
    apply Subtype.ext
    rw [atlas1600SylowTwoEquiv_apply]
    exact atlas1600SylowTwoNormalForm_eq n
  rw [he, Nat.div_eq_of_lt hn]
  simp only [Nat.zero_mod, pow_zero, mul_one]
  repeat' first | apply C.mul_mem | apply C.pow_mem | exact gen_mem_C _ (by decide)

theorem image_last_not_low (f : MulAut S) (n : Fin 2048)
    (hn : atlas1600SylowTwoEquiv n = f (sylowGenerator 7)) : ¬n.val < 1024 := by
  intro h
  have hm : f (sylowGenerator 7) ∈ C := hn ▸ low_mem_C n h
  have hm' := (characteristic_iff_le_comap.mp (inferInstance : C.Characteristic) f.symm) hm
  exact last_not_mem_C (by simpa using hm')
end Tits.SharpOuterBound.LocalImageBound.SylowPairExhaustion.Intrinsic

end
