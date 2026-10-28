module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.RootConjugacy
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction.RankOne
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.CentralKernel
public import Mathlib.FieldTheory.Perfect

/-!
# Short-leading involutions in genuine binary triality

The central SL₂ action makes the second first-layer coordinate zero. The
square-one condition then puts the higher coordinate in a cubic trace kernel.
The identity F³=1 solves its Frobenius equation explicitly. A fixed-field
shift preserves this solution and changes the remaining quadratic trace by
its square times a nonzero norm; finite-field square surjectivity therefore
solves both higher coordinates. The published radical multiplication gives
an actual conjugating element to the specified pinned short root.

Every positive field exponent is retained, including q=2. This supplies the
short-leading input to the complete involution-class assembly; the independent
arms-radical reduction is separate.

Source: Aschbacher–Smith 16.1.4(1), printed p.1171, and GLS3 §§2.4–2.6.
-/

public section
noncomputable section
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace Triality.Standard.EvenInvolutionGeometry.ShortNormalization
variable (P : Parameters) (hp : P.prime = 2)

private theorem higher_scaled (a x : ExtensionField P) :
    higherCoefficient P a (a*x) = a * fieldFrobenius P a *
      (fieldFrobenius P x + x) := by
  simp only [higherCoefficient, map_mul]
  ring

private theorem pair_scaled (a y : ExtensionField P) :
    armsPairing P a (a * fieldFrobenius P a * y) =
      cubicNorm P a * cubicTrace P y := by
  apply Subtype.ext
  simp only [armsPairing_coe, cubicTrace_coe, cubicNorm, Subfield.coe_mul,
    map_mul, fieldFrobenius_three]
  ring

private theorem norm_ne_zero {a : ExtensionField P} (ha : a ≠ 0) : cubicNorm P a ≠ 0 := by
  intro h
  have hz := congrArg Subtype.val h
  exact mul_ne_zero (mul_ne_zero ha ((map_ne_zero _).mpr ha))
    ((map_ne_zero _).mpr ((map_ne_zero _).mpr ha)) hz

include hp

/-- The higher coefficient has exactly the trace-zero image needed by an involution. -/
theorem exists_higher_preimage {a d : ExtensionField P} (ha : a ≠ 0)
    (hd : armsPairing P a d = 0) :
    ∃ c : ExtensionField P, higherCoefficient P a c = d := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let y := d / (a * fieldFrobenius P a)
  have hbase : a * fieldFrobenius P a ≠ 0 := mul_ne_zero ha ((map_ne_zero _).mpr ha)
  have hy : a * fieldFrobenius P a * y = d := mul_div_cancel₀ d hbase
  have htr : cubicTrace P y = 0 := by
    have h := pair_scaled P a y
    rw [hy, hd] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (norm_ne_zero P ha)
  have hsum : fieldFrobenius P (fieldFrobenius P y) + fieldFrobenius P y = y := by
    have h := congrArg Subtype.val htr
    change y + fieldFrobenius P y + fieldFrobenius P (fieldFrobenius P y) = 0 at h
    have h' : (fieldFrobenius P (fieldFrobenius P y) + fieldFrobenius P y) + y = 0 := by
      simpa only [add_assoc, add_comm, add_left_comm] using h
    exact CharTwo.add_eq_zero.mp h'
  refine ⟨a * fieldFrobenius P y, ?_⟩
  rw [higher_scaled, hsum, hy]

/-- Fixed-field shifts preserve the higher coefficient. -/
theorem higher_shift (a c : ExtensionField P) (t : fixedField P) :
    higherCoefficient P a (c + t.val*a) = higherCoefficient P a c := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have ht : fieldFrobenius P t.val = t.val := t.property
  simp only [higherCoefficient, map_add, map_mul, ht]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

private theorem quadratic_shift (a c : ExtensionField P) (t : fixedField P) :
    cubicTrace P (a * fieldFrobenius P (c + t.val*a) *
      fieldFrobenius P (fieldFrobenius P (c + t.val*a))) =
      cubicTrace P (a * fieldFrobenius P c * fieldFrobenius P (fieldFrobenius P c)) +
        t^2 * cubicNorm P a := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have ht : fieldFrobenius P t.val = t.val := t.property
  apply Subtype.ext
  change (cubicTrace P (a * fieldFrobenius P (c + t.val*a) *
    fieldFrobenius P (fieldFrobenius P (c + t.val*a))) : ExtensionField P) =
    (cubicTrace P (a * fieldFrobenius P c * fieldFrobenius P (fieldFrobenius P c)) : ExtensionField P) +
      t.val^2 * (a * fieldFrobenius P a * fieldFrobenius P (fieldFrobenius P a))
  simp only [cubicTrace_coe, map_add, map_mul, fieldFrobenius_three, ht]
  have hthree : (3 : ExtensionField P) = 1 := by
    calc (3 : ExtensionField P) = 2+1 := by norm_num
         _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]
  ring_nf
  simp only [CharTwo.two_eq_zero, hthree, mul_zero, add_zero, zero_add, mul_one]

/-- Solve both nonlinear coordinates, retaining the same nonzero leading root parameter. -/
theorem exists_higher_quadratic_preimage {a d : ExtensionField P} (ha : a ≠ 0)
    (hd : armsPairing P a d = 0) (f : fixedField P) :
    ∃ c : ExtensionField P, higherCoefficient P a c = d ∧
      cubicTrace P (a * fieldFrobenius P c * fieldFrobenius P (fieldFrobenius P c)) = f := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let : CharP (fixedField P) 2 := inferInstance
  obtain ⟨c, hc⟩ := exists_higher_preimage P hp ha hd
  let Q := cubicTrace P (a * fieldFrobenius P c * fieldFrobenius P (fieldFrobenius P c))
  obtain ⟨t, ht⟩ := (Finite.surjective_of_injective (f := fun x : fixedField P => x^2)
    (fun x y h => by exact (frobenius_inj (fixedField P) 2) h))
      ((f + Q) / cubicNorm P a)
  change t^2 = (f+Q) / cubicNorm P a at ht
  refine ⟨c + t.val*a, (higher_shift P hp a c t).trans hc, ?_⟩
  rw [quadratic_shift P hp, ht, div_mul_cancel₀ _ (norm_ne_zero P ha)]
  change Q + (f + Q) = f
  simp [add_left_comm, CharTwo.add_self_eq_zero]
end Triality.Standard.EvenInvolutionGeometry.ShortNormalization

open Triality.Standard.RadicalCoordinates
open Triality.Standard.Parabolics
open Triality.Standard.Parabolics.CentralRootSquare
open Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
namespace Triality.Standard.EvenInvolutionGeometry.ShortNormalization
variable (P : Parameters) (hp : P.prime = 2)

include hp

private theorem pairing_higher (a c : ExtensionField P) :
    armsPairing P c (higherCoefficient P a c) = 0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply Subtype.ext
  change (armsPairing P c (higherCoefficient P a c) : ExtensionField P) = 0
  simp only [armsPairing_coe, higherCoefficient, map_add, map_mul, fieldFrobenius_three]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add]

private theorem coordinates_zero : coordinates P hp (0,0) = 1 := by
  apply Subtype.ext
  rw [coordinates_val, rootElement_factorization]
  simp [extendOrbit]

/-- Square one with zero second coordinate gives the exact trace-zero obstruction. -/
theorem pairing_of_square (v : RootOrbitParameters P .central)
    (hv : v.1 1 = 0) (hs : (coordinates P hp v)^2 = 1) :
    armsPairing P (v.1 0) (v.1 2) = 0 := by
  have he : multiply P v v = (0,0) := (coordinates P hp).injective
    ((coordinates_multiply P hp v v).trans ((pow_two _).symm.trans
      (hs.trans (coordinates_zero P hp).symm)))
  have h := congrArg (fun z : RootOrbitParameters P .central => z.2 0) he
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  simpa [multiply, hv, CharTwo.add_self_eq_zero, -fieldFrobenius_apply] using h

/-- Actual conjugation removes every higher coordinate once the second coordinate is zero. -/
theorem reduced_isConj_short (v : RootOrbitParameters P .central)
    (ha : v.1 0 ≠ 0) (hv : v.1 1 = 0) (hs : (coordinates P hp v)^2 = 1) :
    IsConj (short P hp 0 (v.1 0)) (coordinates P hp v).val := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  obtain ⟨c,hc,hq⟩ := exists_higher_quadratic_preimage P hp ha
    (pairing_of_square P hp v hv hs) (v.2 1)
  obtain ⟨k,hk⟩ := armsPairing_surjective_right P hp (v.1 0) ha
    (v.2 0 + cubicTrace P (c * fieldFrobenius P (v.1 0) *
      fieldFrobenius P (fieldFrobenius P (v.1 0))))
  let w : RootOrbitParameters P .central := (![0,c,k],0)
  let r : RootOrbitParameters P .central := (![v.1 0,0,0],0)
  have hcd : armsPairing P c (v.1 2) = 0 := hc ▸ pairing_higher P hp (v.1 0) c
  have hmul : multiply P w r = multiply P v w := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [multiply,w,r,hv,higherCoefficient, -fieldFrobenius_apply,add_comm]
      exact hc
    · funext i
      fin_cases i
      · simp [multiply,w,r,hv,hc,hk,CharTwo.add_self_eq_zero,
          -fieldFrobenius_apply,add_assoc]
      · simp [multiply,w,r,hv,hq,hcd,higherCoefficient,-fieldFrobenius_apply]
  have he : (coordinates P hp w).val * (coordinates P hp r).val =
      (coordinates P hp v).val * (coordinates P hp w).val := by
    exact congrArg Subtype.val ((coordinates_multiply P hp w r).symm.trans
      ((congrArg (coordinates P hp) hmul).trans (coordinates_multiply P hp v w)))
  have hr : (coordinates P hp r).val = short P hp 0 (v.1 0) := by
    rw [coordinates_val,rootElement_factorization]
    simp [r,extendOrbit]
  rw [hr] at he
  exact isConj_iff.mpr ⟨(coordinates P hp w).val, (mul_inv_eq_iff_eq_mul).mpr he⟩
end Triality.Standard.EvenInvolutionGeometry.ShortNormalization

namespace Triality.Standard.EvenInvolutionGeometry.ShortNormalization
open scoped MatrixGroups
open Matrix
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

/-- A genuine central rank-one actor removes the second first-layer coordinate. -/
theorem exists_firstLayer_normalization (Q : Parameters) (hp : Q.prime = 2) (u : radical Q .central)
    (ha : (firstLayer Q hp u).1 ≠ 0) (hs : u^2 = 1) :
    ∃ g : parabolic Q .central,
      firstLayer Q hp (conjugation Q g u) = ((firstLayer Q hp u).1,0) := by
  let : CharP (ExtensionField Q) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField Q) Q.prime)
  let v := (coordinates Q hp).symm u
  have hv : coordinates Q hp v = u := (coordinates Q hp).apply_symm_apply u
  have hsqv : (coordinates Q hp v)^2 = 1 := by rw [hv]; exact hs
  have hz : multiply Q v v = (0,0) := (coordinates Q hp).injective
    ((coordinates_multiply Q hp v v).trans ((pow_two _).symm.trans
      (hsqv.trans (coordinates_zero Q hp).symm)))
  have h0 : v.1 0 ≠ 0 := by
    intro hz
    apply ha
    rw [← hv, firstLayer_coordinates]
    exact hz
  have hh : higherCoefficient Q (v.1 0) (v.1 1) = 0 := by
    have he := congrArg (fun z : RootOrbitParameters Q .central => z.1 2) hz
    simpa [multiply, CharTwo.add_self_eq_zero] using he
  obtain ⟨t, ht⟩ := TwoRank.fixed_ratio_of_higherCoefficient_eq_zero Q hp h0 hh
  let b := (baseFieldEquivFixed Q).symm t
  have hb : baseFieldEmbedding Q b = t.val :=
    congrArg Subtype.val ((baseFieldEquivFixed Q).apply_symm_apply t)
  let A : SL(2,GaloisField Q.prime Q.exponent) :=
    SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) b
  refine ⟨centralActor Q hp A, ?_⟩
  rw [firstLayer_centralActor, centralLinear_apply, ← hv, firstLayer_coordinates]
  apply Prod.ext
  · simp [A, SpecialLinearGroup.transvection_coe]
  · simp [A, SpecialLinearGroup.transvection_coe,hb,ht,
      CharTwo.add_self_eq_zero]

/-- Every involution with nonzero first short coordinate belongs to the literal pinned short-root class. -/
theorem isShortRoot_of_first_ne_zero (u : radical P .central)
    (ha : (firstLayer P rfl u).1 ≠ 0) (hu : orderOf u.val = 2) :
    IsShortRootInvolution n hn u.val := by
  have hs : u^2 = 1 := Subtype.ext (hu ▸ pow_orderOf_eq_one u.val)
  obtain ⟨g,hg⟩ := exists_firstLayer_normalization P rfl u ha hs
  let v := (coordinates P rfl).symm (conjugation P g u)
  have hv : coordinates P rfl v = conjugation P g u :=
    (coordinates P rfl).apply_symm_apply _
  have hl : (v.1 0,v.1 1) = ((firstLayer P rfl u).1,0) :=
    (firstLayer_coordinates P rfl v).symm.trans ((congrArg (firstLayer P rfl) hv).trans hg)
  have he : v.1 0 = (firstLayer P rfl u).1 := congrArg Prod.fst hl
  have ha' : v.1 0 ≠ 0 := he ▸ ha
  have hz : v.1 1 = 0 := congrArg Prod.snd hl
  have hs' : (coordinates P rfl v)^2 = 1 := by rw [hv,← map_pow,hs,map_one]
  have hc := reduced_isConj_short P rfl v ha' hz hs'
  rw [foldedShort_zero_eq_shortRoot n hn, hv] at hc
  refine ⟨v.1 0,ha',hc.trans ?_⟩
  exact (isConj_iff.mpr ⟨g.val, (conjugation_val P g u).symm⟩).symm
end Triality.Standard.EvenInvolutionGeometry.ShortNormalization
