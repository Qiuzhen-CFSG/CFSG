module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiMixedCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations
/-!
# Four exterior coordinates of the opposite Suzuki commutator

The first Suzuki natural quotient reads two of the five interior root
factors. Conjugating by the supplied linear reflection exchanges the two
Suzuki arguments and inverts their right commutator. The same natural
readout then gives the other two exterior factors. Thus only the two central
Suzuki coordinates and the middle linear coordinate remain undetermined,
with no restriction on the field, including q=2.

Source: Fong--Seitz II (1974), (10.9) and (10.23), pp.223 and 227.
The formulas retain the native triangular correction in both whole roots.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition WeylPresentation SignedGeometry
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)
local notation "W" s:max => (sourceSimpleReflection Q split c s : X ⧸ Q.D)

private theorem batch_pair_reflection (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (W s) (L i a) = L (next false s i) a := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) false s (true,i)
    (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D)
    (synchronizedLinear_perpendicularReflection Q split c a)
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_pair_word,MulAut.conj_apply] using hh

private theorem batch_quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh


private def oppositeReadout : (V2Section Q split c).numerator →*
    Multiplicative (Representation.SuzukiNatural.W m) :=
  ((V2Coordinates Q split c).toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom).comp
    (QuotientGroup.mk' (V2Section Q split c).denominator)

private theorem oppositeReadout_T2 (v : (V2Section Q split c).numerator)
    (h : (v : X ⧸ Q.D) ∈ T2 Q split) : oppositeReadout Q split c v = 1 := by
  change Multiplicative.ofAdd (V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))) = 1
  have hv : (QuotientGroup.mk v : (V2Section Q split c).Carrier) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h
  rw [hv]
  exact congrArg Multiplicative.ofAdd ((V2Coordinates Q split c).toLinearEquiv.map_zero)

private theorem oppositeReadout_next (a : CoefficientField m) :
    oppositeReadout Q split (pinnedInput Q split c) (suzukiMixedRootPoint Q split c (.inl 2) (by decide) a) = 1 :=
  oppositeReadout_T2 Q split (pinnedInput Q split c) _
    ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left)
      (nextLinear_le_phi Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inl 2) a).property))

private theorem oppositeReadout_perpendicular (a : CoefficientField m) :
    oppositeReadout Q split (pinnedInput Q split c) (suzukiMixedRootPoint Q split c (.inl 3) (by decide) a) = 1 :=
  oppositeReadout_T2 Q split (pinnedInput Q split c) _
    ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left)
      (perpendicularLinear_le_phi Q split (pinnedInput Q split c)
        (synchronizedPositiveChart Q split c (.inl 3) a).property))

private theorem oppositeReadout_centralSuzuki (a b : CoefficientField m) :
    oppositeReadout Q split (pinnedInput Q split c) (suzukiMixedRootPoint Q split c (.inr 1) (by decide) (a,b)) = 1 :=
  oppositeReadout_T2 Q split (pinnedInput Q split c) _
    ((show perpendicularSuzuki Q split ≤ T2 Q split from le_sup_right)
      (synchronizedPositiveChart Q split c (.inr 1) (a,b)).property)

private theorem oppositeReadout_reflected (a : CoefficientField m) :
    oppositeReadout Q split (pinnedInput Q split c) (suzukiMixedRootPoint Q split c (.inl 1) (by decide) a) =
      Multiplicative.ofAdd ![a*pinnedLinearV2Label Q split c 1,0,0,0] :=
  congrArg Multiplicative.ofAdd (synchronized_reflected_coordinates Q split c a)

private theorem oppositeReadout_shifted (a b : CoefficientField m) :
    oppositeReadout Q split (pinnedInput Q split c) (suzukiMixedRootPoint Q split c (.inr 3) (by decide) (a,b)) =
      Multiplicative.ofAdd ![0,a*pinnedLinearV2Label Q split c 1,0,0] :=
  congrArg Multiplicative.ofAdd (synchronized_shifted_coordinates Q split c a b)

private theorem oppositeReadout_product (p v l w t r s : CoefficientField m)
    (k : (V2Section Q split (pinnedInput Q split c)).numerator)
    (hk : (k : X ⧸ Q.D) = L 1 p * S 3 v l * L 3 w * S 1 t r * L 2 s) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk k)) =
      ![p*pinnedLinearV2Label Q split c 1,v*pinnedLinearV2Label Q split c 1,0,0] := by
  have he : k = suzukiMixedRootPoint Q split c (.inl 1) (by decide) p *
      suzukiMixedRootPoint Q split c (.inr 3) (by decide) (v,l) *
      suzukiMixedRootPoint Q split c (.inl 3) (by decide) w *
      suzukiMixedRootPoint Q split c (.inr 1) (by decide) (t,r) *
      suzukiMixedRootPoint Q split c (.inl 2) (by decide) s := Subtype.ext hk
  have hh := congrArg (oppositeReadout Q split (pinnedInput Q split c)) he
  rw [map_mul,map_mul,map_mul,map_mul,oppositeReadout_next,oppositeReadout_centralSuzuki,
    oppositeReadout_perpendicular,oppositeReadout_shifted,oppositeReadout_reflected] at hh
  have hv := congrArg Multiplicative.toAdd hh
  change V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk k)) =
    ![p*pinnedLinearV2Label Q split c 1,0,0,0]+![0,v*pinnedLinearV2Label Q split c 1,0,0]+0+0+0 at hv
  exact hv.trans (by ext i; fin_cases i <;> simp)

private theorem simple_suzuki (a b : CoefficientField m) :
    S 0 a b = (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_quartet_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]

private theorem opposite_reflected_commutator (a b y z : CoefficientField m) :
    MulAut.conj (W false) (synchronizedSuzukiMixed Q split c a b y z : X ⧸ Q.D) =
      (synchronizedSuzukiMixed Q split c y z a b : X ⧸ Q.D)⁻¹ := by
  rw [synchronizedSuzukiMixed_val,←simple_suzuki,map_mul,map_mul,map_mul,map_inv,map_inv,
    batch_quartet_reflection Q split c false 2 (by decide),
    batch_quartet_reflection Q split c false 0 (by decide),
    synchronizedSuzukiMixed_val,←simple_suzuki]
  simp only [next,Matrix.cons_val,Fin.isValue]
  group

theorem synchronizedSuzukiMixed_four_coefficients (a b y z : CoefficientField m) :
    ∃ l w r : CoefficientField m,
      (synchronizedSuzukiMixed Q split c a b y z : X ⧸ Q.D) =
        L 2 (z*a) * S 1 (titsEnd m y*a) l * L 3 w *
          S 3 (titsEnd m a*y) r * L 1 (b*y) := by
  obtain ⟨p,v,l,w,t,r,s,hprod,hs,ht⟩ := synchronizedSuzukiMixed_outer_coefficients Q split c a b y z
  have hh := congrArg (MulAut.conj (W false)) hprod
  rw [opposite_reflected_commutator] at hh
  simp only [map_mul,batch_pair_reflection Q split c false 2 (by decide),
    batch_pair_reflection Q split c false 3 (by decide),
    batch_pair_reflection Q split c false 1 (by decide),
    batch_quartet_reflection Q split c false 1 (by decide),
    batch_quartet_reflection Q split c false 3 (by decide),
    next,Matrix.cons_val,Fin.isValue] at hh
  have hc := oppositeReadout_product Q split c p v l w t r s
    (synchronizedSuzukiMixed Q split c y z a b)⁻¹ hh
  have hinv : V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk ((synchronizedSuzukiMixed Q split c y z a b)⁻¹))) =
      ![(z*a)*pinnedLinearV2Label Q split c 1,
        (titsEnd m y*a)*pinnedLinearV2Label Q split c 1,0,0] := by
    rw [QuotientGroup.mk_inv]
    change (V2Coordinates Q split (pinnedInput Q split c)).toLinearEquiv
      (-Additive.ofMul (QuotientGroup.mk (synchronizedSuzukiMixed Q split c y z a b))) = _
    rw [map_neg]
    change -V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (synchronizedSuzukiMixed Q split c y z a b))) = _
    rw [synchronizedSuzukiMixed_coordinates]
    ext i
    fin_cases i <;> simp only [Pi.neg_apply,CharTwo.neg_eq]
  rw [hinv] at hc
  have hp : p = z*a := mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    (show p*pinnedLinearV2Label Q split c 1 = z*a*pinnedLinearV2Label Q split c 1 from (congrFun hc 0).symm)
  have hv : v = titsEnd m y*a := mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    (show v*pinnedLinearV2Label Q split c 1 = titsEnd m y*a*pinnedLinearV2Label Q split c 1 from (congrFun hc 1).symm)
  exact ⟨l,w,r,by simpa only [hp,hv,hs,ht] using hprod⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
