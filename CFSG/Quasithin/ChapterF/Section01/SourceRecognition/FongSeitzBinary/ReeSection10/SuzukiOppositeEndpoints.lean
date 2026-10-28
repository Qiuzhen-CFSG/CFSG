module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiOppositeMiddle

/-!
# Endpoint coordinates of the pure opposite Suzuki commutator

The middle-coordinate calculation leaves the two central Suzuki labels.  This
file records the binary reflection relation between those labels.  The
comparison is made in the native triangular chart, so the inverse of a pure
first-coordinate Suzuki point contributes its chart correction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4 BenderSuzuki.MatrixGroups
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

private theorem quartet_inv (i : Fin 4) (a b : CoefficientField m) :
    (S i a b)⁻¹ = S i a (b+titsEnd m a*a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  have he : b+(b+titsEnd m a*a)+titsEnd m a*a = 0 := by
    rw [←add_assoc b b,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  simp only [he,CharTwo.add_self_eq_zero,synchronizedPositivePoint_quartet_zero]

set_option maxHeartbeats 500000 in
private theorem chart_pair_zero (i : Fin 4) :
    synchronizedPositiveChart Q split c (.inl i) 0 = 1 := by
  apply Subtype.ext
  exact synchronizedPositivePoint_pair_zero Q split c i

private theorem chart_quartet_zero (i : Fin 4) :
    synchronizedPositiveChart Q split c (.inr i) (0,0) = 1 := by
  apply Subtype.ext
  exact synchronizedPositivePoint_quartet_zero Q split c i

private theorem triple_unique
    (v l w t r v' l' w' t' r' : CoefficientField m)
    (he : S 3 v l * L 3 w * S 1 t r =
      S 3 v' l' * L 3 w' * S 1 t' r') :
    v = v' ∧ l = l' ∧ w = w' ∧ t = t' ∧ r = r' := by
  have he' := congrArg (MulAut.conj (W true)) he
  simp only [map_mul,
    batch_quartet_reflection Q split c true 3 (by decide),
    batch_pair_reflection Q split c true 3 (by decide),
    batch_quartet_reflection Q split c true 1 (by decide),
    next,Matrix.cons_val,Fin.isValue] at he'
  have hh := linearProduct_injective Q split c
    (a₁ := (synchronizedPositiveChart Q split c (.inr 2) (v,l),
      synchronizedPositiveChart Q split c (.inl 2) w,
      synchronizedPositiveChart Q split c (.inr 1) (t,r),
      1,1,1,1,PUnit.unit))
    (a₂ := (synchronizedPositiveChart Q split c (.inr 2) (v',l'),
      synchronizedPositiveChart Q split c (.inl 2) w',
      synchronizedPositiveChart Q split c (.inr 1) (t',r'),
      1,1,1,1,PUnit.unit)) (by
        simp only [linearFactors,rootProduct,OneMemClass.coe_one,mul_one]
        change S 2 v l * (L 2 w * S 1 t r) = S 2 v' l' * (L 2 w' * S 1 t' r')
        simpa only [mul_assoc] using he')
  have hv := (synchronizedPositiveChart Q split c (.inr 2)).injective (congrArg Prod.fst hh)
  have hw := (synchronizedPositiveChart Q split c (.inl 2)).injective
    (congrArg (fun z => z.2.1) hh)
  have ht := (synchronizedPositiveChart Q split c (.inr 1)).injective
    (congrArg (fun z => z.2.2.1) hh)
  exact ⟨congrArg Prod.fst hv, congrArg Prod.snd hv, hw,
    congrArg Prod.fst ht, congrArg Prod.snd ht⟩

private theorem pair_inv (i : Fin 4) (a : CoefficientField m) :
    (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_pair_mul]
  simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]

/-- The reflected opposite-Omega action, in the opposite-first convention. -/
theorem synchronized_omegaOpposite_right (b y : CoefficientField m) :
    (S 2 y 0)⁻¹*(S 0 0 b)⁻¹*S 2 y 0*S 0 0 b =
      L 1 (y*b)*L 3 (y*titsEnd m y*b)*S 1 0 (y^2*titsEnd m y*b) := by
  have h := synchronized_oppositeOmega_right Q split c y 0 b
  simp only [zero_mul,mul_zero,map_zero,add_zero,zero_add,
    synchronizedPositivePoint_quartet_zero,one_mul] at h
  have hh := congrArg (MulAut.conj (W false)) h
  simp only [map_mul,map_inv,
    batch_quartet_reflection Q split c false 2 (by decide),
    batch_quartet_reflection Q split c false 0 (by decide),
    batch_quartet_reflection Q split c false 3 (by decide),
    batch_pair_reflection Q split c false 3 (by decide),
    batch_pair_reflection Q split c false 2 (by decide),
    next,Matrix.cons_val,Fin.isValue] at hh
  simpa only [mul_inv_rev,inv_inv,quartet_inv,pair_inv,map_zero,zero_mul,
    add_zero,zero_add,CharTwo.add_self_eq_zero,mul_assoc] using congrArg Inv.inv hh

/-- Reflection couples the two central labels of the unit seed. -/
theorem synchronizedSuzukiMixed_unit_seed :
    ∃ ε : CoefficientField m,
      (synchronizedSuzukiMixed Q split c 1 0 1 0 : X ⧸ Q.D) =
        S 1 1 (1+ε) * L 3 1 * S 3 1 ε := by
  obtain ⟨l,r,h⟩ := synchronizedSuzukiMixed_main_middle Q split c 1 1
  have hθ : titsEnd m (1 : CoefficientField m) = 1 := map_one _
  rw [hθ] at h
  simp only [mul_one] at h
  have hh := congrArg (MulAut.conj (sourceSimpleReflection Q split c false : X ⧸ Q.D)) h
  rw [opposite_reflected_commutator Q split c 1 0 1 0] at hh
  rw [h] at hh
  simp only [map_mul,
    batch_quartet_reflection Q split c false 1 (by decide),
    batch_pair_reflection Q split c false 3 (by decide),
    batch_quartet_reflection Q split c false 3 (by decide),
    next,Matrix.cons_val,Fin.isValue] at hh
  simp only [mul_inv_rev,pair_inv Q split c,quartet_inv Q split c,hθ,
    mul_one,mul_assoc] at hh
  have hu := triple_unique Q split c 1 l 1 1 r 1 (r+1) 1 1 (l+1) (by
    simpa only [mul_assoc] using hh.symm)
  have hlr : l = r+1 := hu.2.1
  refine ⟨r, ?_⟩
  simpa [hlr, add_comm] using h

/-- The binary seed has one undetermined central parameter. -/
theorem synchronizedSuzukiMixed_binary_seed
    (_hfield : m = 0) :
    ∃ ε : CoefficientField m,
      (synchronizedSuzukiMixed Q split c 1 0 1 0 : X ⧸ Q.D) =
        S 1 1 (1+ε) * L 3 1 * S 3 1 ε :=
  synchronizedSuzukiMixed_unit_seed Q split c

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
