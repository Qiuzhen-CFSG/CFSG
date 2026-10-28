module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondModel

/-!
# The original Borel inside the second coordinate model

Splitting a Sylow element at its first root gives an explicit computable map
into the second semidirect-product model. Compatibility with the verified
endpoint inclusion proves it is a homomorphism and identifies its exact range.
Thus the finite reflection census uses the original common Borel embedding.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo SecondExtension

def secondSylowFun (x : SylowModel) : SecondModel :=
  let i := x.left.b0.val
  let k := x * (SylowModel.root 0 ^ i)⁻¹
  have hk : k ∈ radical := by
    change radicalCharacter k = 1
    dsimp [k]
    rw [map_mul, map_inv, map_pow]
    have he : radicalCharacter (SylowModel.root 0) ^ i = radicalCharacter x :=
      FiveFour.generator_pow_val (radicalCharacter x)
    rw [he, mul_inv_cancel]
  ⟨⟨k,hk⟩, (DihedralGroup.sr 2)^i⟩

theorem secondMap_secondSylowFun (x : SylowModel) :
    secondMap (secondSylowFun x) = inclusion x := by
  change radicalMap ⟨x*(SylowModel.root 0 ^ x.left.b0.val)⁻¹, _⟩ *
    secondSection (DihedralGroup.sr 2 ^ x.left.b0.val) = inclusion x
  rw [map_pow, secondSection_firstRoot, ← map_pow]
  change inclusion (x * (SylowModel.root 0 ^ x.left.b0.val)⁻¹) *
    inclusion (SylowModel.root 0 ^ x.left.b0.val) = inclusion x
  rw [← map_mul, inv_mul_cancel_right]

def secondSylow : SylowModel →* SecondModel where
  toFun := secondSylowFun
  map_one' := by
    apply secondMap_bijective.1
    rw [secondMap_secondSylowFun, map_one, map_one]
  map_mul' x y := by
    apply secondMap_bijective.1
    rw [secondMap_secondSylowFun, map_mul, map_mul,
      secondMap_secondSylowFun, secondMap_secondSylowFun]

@[simp] theorem secondMap_secondSylow (x : SylowModel) :
    secondMap (secondSylow x) = inclusion x := secondMap_secondSylowFun x

theorem secondSylow_injective : Function.Injective secondSylow := by
  intro x y h
  apply inclusion_injective
  simpa only [secondMap_secondSylow] using congrArg secondMap h

theorem secondSylow_radical (x : radical) : secondSylow x = SemidirectProduct.inl x := by
  apply secondMap_bijective.1
  rw [secondMap_secondSylow, secondMap_inl]
  rfl

theorem secondSylow_firstRoot : secondSylow (SylowModel.root 0) = SemidirectProduct.inr (DihedralGroup.sr 2) := by
  apply secondMap_bijective.1
  rw [secondMap_secondSylow, secondMap_inr, secondSection_firstRoot]

theorem mem_secondB_iff (x : SecondModel) : x ∈ secondSylow.range ↔
    x.right = 1 ∨ x.right = DihedralGroup.sr 2 := by
  constructor
  · rintro ⟨y,rfl⟩
    change (DihedralGroup.sr 2)^y.left.b0.val = 1 ∨
      (DihedralGroup.sr 2)^y.left.b0.val = DihedralGroup.sr 2
    exact (by decide +kernel : ∀ a : ZMod 2,
      (DihedralGroup.sr 2)^a.val = 1 ∨ (DihedralGroup.sr 2)^a.val = DihedralGroup.sr 2) y.left.b0
  · rintro (h | h)
    · refine ⟨x.left.val, ?_⟩
      rw [secondSylow_radical]
      apply SemidirectProduct.ext
      · rfl
      · exact h.symm
    · refine ⟨x.left.val * SylowModel.root 0, ?_⟩
      rw [map_mul, secondSylow_radical, secondSylow_firstRoot]
      rw [← h, SemidirectProduct.inl_left_mul_inr_right]

end Tits.AmalgamRigidity.FullRee.PointedPairs
