module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SourceQuotientBridge.NonsplitOther

/-!
# The square functional on the marked other quotient

The literal other preimage modulo the original Z is the elementary eight-group
in the wreath quotient. Since the preimage is abelian, squaring is a
homomorphism into Z, and since Z has exponent two this homomorphism descends.
The nonsplit swap witnesses its nonzero value. Surjectivity and the orders of
the domain and codomain give a kernel of order four.

All maps retain representatives in the original degree-24 carrier.
Source: the corrected third-branch calculation for Aschbacher--Smith 14.2.21,
printed p.988, refs/quasithin.pdf.
-/

@[expose] public section

open Sporadic.Mathieu.M12ExceptionalExtension FirstParabolic
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M12ExceptionalExtension.SourceQuotientBridge.NonsplitOther
noncomputable section

def markedSubgroup (m : InnerModel) : Subgroup (otherPreimage m) :=
  (distinguished.subgroupOf outerCore).subgroupOf (otherPreimage m)

instance (m : InnerModel) : (markedSubgroup m).Normal := inferInstanceAs
  ((distinguished.subgroupOf outerCore).subgroupOf (otherPreimage m)).Normal

abbrev CentralQuotient (m : InnerModel) := otherPreimage m ⧸ markedSubgroup m

def toOther (m : InnerModel) : otherPreimage m →* FourWreathTwo.other :=
  ((wreathMap m).comp (otherPreimage m).subtype).codRestrict _ (fun x => x.property)

theorem toOther_surjective (m : InnerModel) : Function.Surjective (toOther m) := by
  intro w
  obtain ⟨x,hx⟩ := wreathMap_surjective m w.val
  exact ⟨⟨x,show wreathMap m x ∈ FourWreathTwo.other from hx ▸ w.property⟩,Subtype.ext hx⟩

theorem toOther_ker (m : InnerModel) : (toOther m).ker = markedSubgroup m := by
  ext x
  change (⟨wreathMap m x.val,x.property⟩ : FourWreathTwo.other) = 1 ↔ _
  rw [Subtype.ext_iff]
  change x.val ∈ (wreathMap m).ker ↔ x.val ∈ distinguished.subgroupOf outerCore
  rw [wreathMap_ker]

def centralQuotientEquiv (m : InnerModel) : CentralQuotient m ≃* FourWreathTwo.other :=
  (QuotientGroup.quotientMulEquivOfEq (toOther_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (toOther m) (toOther_surjective m))

theorem centralQuotientEquiv_mk (m : InnerModel) (x : otherPreimage m) :
    centralQuotientEquiv m (QuotientGroup.mk' (markedSubgroup m) x) = toOther m x := rfl

theorem centralQuotient_card (m : InnerModel) : Nat.card (CentralQuotient m) = 8 :=
  (Nat.card_congr (centralQuotientEquiv m).toEquiv).trans FourWreathTwo.card_other

instance centralQuotient_elementary (m : InnerModel) : IsElementaryAbelian 2 (CentralQuotient m) where
  is_comm := ⟨fun a b => by
    apply (centralQuotientEquiv m).injective
    let := FourWreathTwo.other_elementary
    simp only [map_mul, mul_comm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
    apply (centralQuotientEquiv m).injective
    rw [map_pow, map_one]
    exact FourWreathTwo.other_square _)

theorem square_mem (m : InnerModel) (x : otherPreimage m) : x.val.val ^ 2 ∈ distinguished := by
  have h : wreathMap m (x.val ^ 2) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val (FourWreathTwo.other_square (toOther m x))
  have hk : x.val ^ 2 ∈ (wreathMap m).ker := h
  rwa [wreathMap_ker] at hk

/-- Literal squaring, with values in the original marked subgroup of the carrier. -/
def squareToZ (m : InnerModel) : otherPreimage m →* distinguished where
  toFun x := ⟨x.val.val ^ 2, square_mem m x⟩
  map_one' := Subtype.ext (one_pow 2)
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg (fun a : otherPreimage m => a.val.val) (mul_pow x y 2)

theorem marked_le_square_ker (m : InnerModel) : markedSubgroup m ≤ (squareToZ m).ker := by
  intro x hx
  apply Subtype.ext
  change x.val.val ^ 2 = 1
  rcases (mem_distinguished x.val.val).mp hx with h | h
  · rw [h, one_pow]
  · rw [h, z_square]

/-- Squaring descends through the original Z, since it is central of exponent two. -/
def squareMap (m : InnerModel) : CentralQuotient m →* distinguished :=
  QuotientGroup.lift (markedSubgroup m) (squareToZ m) (marked_le_square_ker m)

theorem squareMap_mk (m : InnerModel) (x : otherPreimage m) :
    (squareMap m (QuotientGroup.mk' (markedSubgroup m) x)).val = x.val.val ^ 2 := rfl

def swapClass (m : InnerModel) : CentralQuotient m :=
  QuotientGroup.mk' (markedSubgroup m) ⟨outerSwap,outerSwap_mem_otherPreimage m⟩

theorem squareMap_swap (m : InnerModel) :
    squareMap m (swapClass m) = ⟨z,Subgroup.mem_zpowers z⟩ :=
  Subtype.ext nonsplitSwap_square

theorem squareMap_nonzero (m : InnerModel) : squareMap m ≠ 1 := by
  intro h
  have he := congrArg (fun f : CentralQuotient m →* distinguished => (f (swapClass m)).val) h
  rw [squareMap_swap] at he
  exact z_ne_one he

theorem squareMap_surjective (m : InnerModel) : Function.Surjective (squareMap m) := by
  intro x
  rcases (mem_distinguished x.val).mp x.property with h | h
  · refine ⟨1, ?_⟩
    rw [map_one]
    exact Subtype.ext h.symm
  · exact ⟨swapClass m, (squareMap_swap m).trans (Subtype.ext h.symm)⟩

theorem squareMap_ker_card (m : InnerModel) : Nat.card (squareMap m).ker = 4 := by
  have hc := (squareMap m).ker.card_mul_index
  have hi : (squareMap m).ker.index = 2 := by
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (squareMap_surjective m)).toEquiv,
      card_distinguished]
  rw [hi, centralQuotient_card] at hc
  omega

/-- The induced action of a homomorphism fixing the actual marked subgroup pointwise. -/
def quotientMapFixingZ (m : InnerModel) (a : otherPreimage m →* otherPreimage m)
    (ha : ∀ x ∈ markedSubgroup m, a x = x) : CentralQuotient m →* CentralQuotient m :=
  QuotientGroup.map _ _ a (fun x hx => by
    change a x ∈ markedSubgroup m
    rw [ha x hx]
    exact hx)

theorem squareMap_invariant (m : InnerModel) (a : otherPreimage m →* otherPreimage m)
    (ha : ∀ x ∈ markedSubgroup m, a x = x) (q : CentralQuotient m) :
    squareMap m (quotientMapFixingZ m a ha q) = squareMap m q := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (markedSubgroup m) q
  apply Subtype.ext
  change (a x).val.val ^ 2 = x.val.val ^ 2
  have hx : x ^ 2 ∈ markedSubgroup m := square_mem m x
  exact congrArg (fun y : otherPreimage m => y.val.val)
    ((a.map_pow x 2).symm.trans (ha (x ^ 2) hx))

end
end Sporadic.Mathieu.M12ExceptionalExtension.SourceQuotientBridge.NonsplitOther
