module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.WeylVerification

/-!
# The second reflection on the binary Ree radical

The ordered radical word is evaluated on the verified Weyl images. The literal
endpoint inclusion identifies this computable map with conjugation by the
second reflection. Injectivity of that inclusion proves the group and
involution laws, without an additional finite action certificate.

Source: the radical and Weyl relations of `FullRee.SecondExtension`, following
Shinoda (1975), pp. 81–83 and Parrott (1972), p. 683.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo SecondExtension

def radicalWord (a : Fin 10 → SylowModel) (x : SylowModel) : SylowModel :=
  a 1 ^ x.left.b1.val * a 2 ^ x.left.b2.val * a 3 ^ x.left.b3.val *
  a 4 ^ x.left.b4.val * a 5 ^ x.left.b5.val * a 6 ^ x.left.b6.val *
  a 7 ^ x.left.b7.val * a 8 ^ x.left.b8.val * a 9 ^ x.left.b9.val *
  (a 0)⁻¹ ^ x.right.toAdd.val

theorem radicalWord_eq (x : radical) : radicalWord radicalGenerator x = x := by
  have he := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form x.val.left)
  have h0 : x.val.left.b0 = 0 := x.property
  have ht : (SemidirectProduct.inr x.val.right : SylowModel) =
      SylowModel.rootOne⁻¹ ^ x.val.right.toAdd.val := by
    rw [SylowModel.rootOne, ← map_inv, inv_inv, ← map_pow, FiveFour.generator_pow_val]
  have hx := SemidirectProduct.inl_left_mul_inr_right x.val
  rw [← he, ht] at hx
  change radicalWord radicalGenerator x = x.val
  dsimp only [radicalWord]
  simp only [map_mul, map_pow, h0, ZMod.val_zero, pow_zero, one_mul] at hx
  exact hx

def secondWeylWord (x : radical) : SylowModel := radicalWord weylImage x

theorem secondWeylWord_mem (x : radical) : secondWeylWord x ∈ radical := by
  unfold secondWeylWord radicalWord
  have hp (i : Fin 10) (n : Nat) : weylImage i ^ n ∈ radical :=
    radical.pow_mem (weylImage_mem i) n
  have hz : (weylImage 0)⁻¹ ^ x.val.right.toAdd.val ∈ radical :=
    radical.pow_mem (radical.inv_mem (weylImage_mem 0)) _
  exact radical.mul_mem (radical.mul_mem (radical.mul_mem (radical.mul_mem
    (radical.mul_mem (radical.mul_mem (radical.mul_mem (radical.mul_mem
    (radical.mul_mem (hp 1 _) (hp 2 _)) (hp 3 _)) (hp 4 _)) (hp 5 _)) (hp 6 _))
    (hp 7 _)) (hp 8 _)) (hp 9 _)) hz

theorem inclusion_secondWeylWord (x : radical) :
    inclusion (secondWeylWord x) = reflection * inclusion x * reflection⁻¹ := by
  let f := (MulAut.conj reflection).toMonoidHom.comp inclusion
  have hgen (i : Fin 10) : f (radicalGenerator i) = inclusion (weylImage i) :=
    weyl_relations.conjugate i
  change inclusion (secondWeylWord x) = f x
  conv_rhs => rw [← radicalWord_eq x]
  simp only [secondWeylWord, radicalWord, map_mul, map_pow, map_inv, hgen]

def secondWeyl : MulAut radical where
  toFun x := ⟨secondWeylWord x, secondWeylWord_mem x⟩
  invFun x := ⟨secondWeylWord x, secondWeylWord_mem x⟩
  left_inv x := by
    apply Subtype.ext
    apply inclusion_injective
    simp only [inclusion_secondWeylWord]
    have hh : reflection * reflection = 1 := by simpa only [pow_two] using weyl_relations.square
    calc
      _ = (reflection * reflection) * inclusion x * (reflection * reflection)⁻¹ := by group
      _ = _ := by rw [hh]; simp
  right_inv x := by
    apply Subtype.ext
    apply inclusion_injective
    simp only [inclusion_secondWeylWord]
    have hh : reflection * reflection = 1 := by simpa only [pow_two] using weyl_relations.square
    calc
      _ = (reflection * reflection) * inclusion x * (reflection * reflection)⁻¹ := by group
      _ = _ := by rw [hh]; simp
  map_mul' x y := by
    apply Subtype.ext
    apply inclusion_injective
    change inclusion (secondWeylWord (x*y)) = inclusion (secondWeylWord x * secondWeylWord y)
    rw [inclusion_secondWeylWord, map_mul, inclusion_secondWeylWord, inclusion_secondWeylWord]
    change reflection * inclusion (x.val * y.val) * reflection⁻¹ = _
    rw [map_mul]
    group

end Tits.AmalgamRigidity.FullRee.PointedPairs
