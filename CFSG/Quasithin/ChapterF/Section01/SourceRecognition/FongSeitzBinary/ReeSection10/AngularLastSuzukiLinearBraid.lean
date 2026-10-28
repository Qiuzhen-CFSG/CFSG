module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastSuzukiLinear

/-!
# Linear rank-one symmetry of the last Suzuki commutator

The parameter-one linear root element and its supplied reflection satisfy
the rank-one braid relation. The opposite Suzuki root commutes with this
linear element. Hence the conjugated simple Suzuki point is fixed by the
linear reflection. This is a source equality in the original marked quotient,
used to compare the remaining Carter coordinates of the last angular row.

Source: Fong--Seitz II (1974), printed pp.228--229, (10.27)--(10.30).
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
private theorem batch_quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh
private theorem simple_linear (a : CoefficientField m) :
    L 0 a = (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_pair_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]
private theorem pair_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_pair_mul]
  simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]
private theorem linear_braid :
    W false * L 0 1 * W false = L 0 1 * W false * L 0 1 := by
  have hw : W false * W false = 1 := linearReflection_sq Q split c
  have hwi : (W false)⁻¹ = W false := inv_eq_of_mul_eq_one_right hw
  have hx : L 0 1 * L 0 1 = 1 := by
    rw [synchronizedPositivePoint_pair_mul]
    simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]
  have h := synchronizedLinear_gauss Q split c (1 : (CoefficientField m)ˣ)
  simp only [Units.val_one,inv_one,map_one,mul_one] at h
  rw [←simple_linear Q split c] at h
  change W false * (W false * L 0 1 * (W false)⁻¹) =
    (W false * L 0 1 * (W false)⁻¹) * L 0 1 at h
  rw [hwi] at h
  have hh : L 0 1 * W false = W false * L 0 1 * W false * L 0 1 := by
    simpa only [←mul_assoc,hw,one_mul] using h
  calc
    _ = (W false * L 0 1 * W false * L 0 1) * L 0 1 := by
      rw [mul_assoc (W false * L 0 1 * W false),hx,mul_one]
    _ = _ := by rw [←hh]
private theorem fixed_of_braid {G : Type*} [Group G] {w x y z : G}
    (hb : w*x*w = x*w*x) (hy : w*z*w⁻¹ = y) (hxz : x*z*x⁻¹ = z) :
    w*(x*y*x⁻¹)*w⁻¹ = x*y*x⁻¹ := by
  calc
    _ = (w*x*w)*z*(w*x*w)⁻¹ := by rw [←hy]; group
    _ = (x*w*x)*z*(x*w*x)⁻¹ := by rw [hb]
    _ = x*(w*(x*z*x⁻¹)*w⁻¹)*x⁻¹ := by group
    _ = _ := by rw [hxz,hy]

theorem synchronizedSuzukiLinear_linear_braid_fixed (a b : CoefficientField m) :
    MulAut.conj (W false) (L 0 1 * S 0 a b * L 0 1) =
      L 0 1 * S 0 a b * L 0 1 := by
  have hy : W false * S 2 a b * (W false)⁻¹ = S 0 a b := by
    simpa only [MulAut.conj_apply,next,Matrix.cons_val,Fin.isValue]
      using batch_quartet_reflection Q split c false 2 (by decide) a b
  have hc := (synchronized_adjacent_commute_family Q split c 1 a b).2.2.2.2.2.2
  have hxz : L 0 1 * S 2 a b * (L 0 1)⁻¹ = S 2 a b := by
    rw [hc.eq,mul_inv_cancel_right]
  simpa only [MulAut.conj_apply,pair_inv] using
    fixed_of_braid (linear_braid Q split c) hy hxz
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
