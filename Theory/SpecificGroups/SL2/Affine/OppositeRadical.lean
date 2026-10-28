module

public import Theory.SpecificGroups.SL2.Affine
public import Theory.Representation.SL2FourNaturalOrbits.BorelFactors

/-!
# The opposite elementary radical is forced by the actual affine action

An elementary sixteen whose actual linear image is the full upper root
has its translation coordinate on the upper fixed line. Squaring one lift
of upper(1) and commuting with it proves this directly, retaining the
original affine subgroup. Cardinality then gives equality with the literal
opposite radical, with no shear or splitting assumption on that subgroup.
-/

public noncomputable section
open Subgroup Matrix SemidirectProduct
open scoped IsMulCommutative
namespace Matrix.SL2
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors

/-- The original upper translations together with the upper root actors. -/
@[expose] def oppositeRootMap : Multiplicative (F×F) →* Affine F where
  toFun v := ⟨Multiplicative.ofAdd ![v.toAdd.1,0],upper v.toAdd.2⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      fin_cases i <;> rfl
    · apply Subtype.ext
      funext i j
      fin_cases i <;> fin_cases j <;> simp [upper]
  map_mul' v w := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change ![v.toAdd.1+w.toAdd.1,0] =
        ![v.toAdd.1,0]+(upper v.toAdd.2).val *ᵥ ![w.toAdd.1,0]
      funext i
      fin_cases i <;>
        simp [upper]
    · apply Subtype.ext
      funext i j
      change (upper (v.toAdd.2+w.toAdd.2)).val i j=
        ((upper v.toAdd.2).val*(upper w.toAdd.2).val) i j
      fin_cases i <;> fin_cases j <;>
        simp [upper,Matrix.mul_apply,Fin.sum_univ_two,add_comm]

/-- The literal elementary opposite radical inside the existing affine endpoint. -/
@[expose] def oppositeRoot : Subgroup (Affine F) := oppositeRootMap.range

theorem mem_oppositeRoot (a : Affine F) :
    a∈oppositeRoot ↔ a.left.toAdd 1=0 ∧ a.right∈U0 := by
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨rfl,(mem_U0 _).mpr ⟨v.toAdd.2,rfl⟩⟩
  · rintro ⟨hv,hg⟩
    obtain ⟨x,hx⟩ := (mem_U0 _).mp hg
    refine ⟨Multiplicative.ofAdd (a.left.toAdd 0,x),?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · rfl
      · exact hv.symm
    · exact hx

theorem oppositeRoot_card : Nat.card oppositeRoot=16 := by
  have hi : Function.Injective oppositeRootMap := by
    intro v w h
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · exact congrArg (fun a : Affine F => a.left.toAdd 0) h
    · exact congrArg (fun a : Affine F => a.right.val 0 1) h
  change Nat.card oppositeRootMap.range=16
  rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  change Nat.card (F×F)=16
  rw [Nat.card_prod,Nat.card_eq_fintype_card,card_field]

theorem elementary_oppositeRoot_of_image (C : Subgroup (Affine F))
    [IsElementaryAbelian 2 C] (hC : Nat.card C=16)
    (himage : C.map (rightHom : Affine F →* SL)=U0) : C=oppositeRoot := by
  have h1 : upper 1∈C.map (rightHom : Affine F →* SL) := by
    rw [himage]
    exact (mem_U0 _).mpr ⟨1,rfl⟩
  obtain ⟨c,hc,hcr⟩ := h1
  change c.right=upper 1 at hcr
  have hc2 : c^2=1 := elemPow_eq_one_of_isElementaryAbelian c hc
  have hc1 : c.left.toAdd 1=0 := by
    have hh := congrArg (fun a : Affine F => a.left.toAdd 0) hc2
    rw [pow_two] at hh
    change c.left.toAdd 0+(c.right.val *ᵥ c.left.toAdd) 0=0 at hh
    rw [hcr] at hh
    simpa [upper,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
      ←add_assoc,CharTwo.add_self_eq_zero] using hh
  have hle : C≤oppositeRoot := by
    intro b hb
    have hbr : b.right∈U0 := himage ▸ mem_map_of_mem rightHom hb
    obtain ⟨x,hx⟩ := (mem_U0 _).mp hbr
    apply (mem_oppositeRoot b).mpr
    refine ⟨?_,hbr⟩
    have he : c*b=b*c := congrArg Subtype.val
      (mul_comm (⟨c,hc⟩ : C) (⟨b,hb⟩ : C))
    have hh := congrArg (fun a : Affine F => a.left.toAdd 0) he
    change c.left.toAdd 0+(c.right.val *ᵥ b.left.toAdd) 0=
      b.left.toAdd 0+(b.right.val *ᵥ c.left.toAdd) 0 at hh
    rw [hcr,←hx] at hh
    have hh' : c.left.toAdd 0+b.left.toAdd 0+b.left.toAdd 1=
        b.left.toAdd 0+c.left.toAdd 0 := by
      simpa [upper,
        Matrix.mulVec,dotProduct,Fin.sum_univ_two,hc1,add_assoc] using hh
    have heq : (c.left.toAdd 0+b.left.toAdd 0)+b.left.toAdd 1=
        (c.left.toAdd 0+b.left.toAdd 0)+0 := by
      simpa only [add_zero,add_comm (b.left.toAdd 0)] using hh'
    exact add_left_cancel heq
  let : Finite oppositeRoot := Finite.of_surjective oppositeRootMap.rangeRestrict
    oppositeRootMap.rangeRestrict_surjective
  apply eq_of_le_of_card_ge hle
  rw [hC,oppositeRoot_card]

end Matrix.SL2
