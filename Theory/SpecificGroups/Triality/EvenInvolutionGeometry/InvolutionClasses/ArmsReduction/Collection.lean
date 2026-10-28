module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ShortLeading
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Multiplication

/-!
# Actual folded-root shears in the binary triality arms radical

Collecting the twelve positive D₄ roots gives the conjugation formula for
short-root shears on the faithful arms coordinates. The trace, norm and
Frobenius terms are retained exactly, including the binary field.
This supplies the coordinate calculation in the involution-class reduction.

Source: Aschbacher–Smith 16.1.4(1), printed p.1171; GLS3 §§2.4–2.6.
-/

@[expose] public section
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace Triality.Standard.EvenInvolutionGeometry.ArmsNormalization

private theorem collect_sum {F G : Type*} [Mul F] [Group G]
    (x : Fin 12 → F → G)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a * b))
    (i j k : Fin 12) (h : (i,j,k) ∈ sumTriples) (a b : F) (g : G) :
    x i a * (x j b * g) = x j b * (x i a * (x k (a * b) * g)) := by
  rw [← mul_assoc, hs i j k h]
  simp only [mul_assoc]

private theorem collect_comm {F G : Type*} [Group G]
    (x : Fin 12 → F → G)
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b,
      Commute (x i a) (x j b))
    (i j : Fin 12) (hij : i ≠ j) (h : ∀ k, (i,j,k) ∉ sumTriples)
    (a b : F) (g : G) :
    x i a * (x j b * g) = x j b * (x i a * g) := by
  rw [← mul_assoc, (hc i j hij h a b).eq, mul_assoc]

private theorem collect_add {F G : Type*} [Add F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a+b) = x i a * x i b)
    (i : Fin 12) (a b : F) (g : G) :
    x i a * (x i b * g) = x i (a+b) * g := by
  rw [← mul_assoc, ← ha]

private theorem raw_collection {F G : Type*} [Add F] [Mul F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a+b) = x i a * x i b)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b,
      Commute (x i a) (x j b))
    (a A B b c C D d E Fv e f : F) :
    x 0 (a) * x 1 (A) * x 2 (B) * x 3 (b) * x 4 (c) * x 5 (C) * x 6 (D) * x 7 (d) * x 8 (E) * x 9 (Fv) * x 10 (e) * x 11 (f) * x 0 (a) * x 1 (A) * x 2 (B) =
      x 0 ((a+a)) * x 1 ((A+A)) * x 2 ((B+B)) * x 3 (b) * x 4 (((b*a)+c)) * x 5 (((b*A)+C)) * x 6 (((b*B)+D)) * x 7 (((((b*a)+c)*A)+((C*a)+d))) * x 8 (((((b*A)+C)*B)+((D*A)+E))) * x 9 (((((b*a)+c)*B)+((D*a)+Fv))) * x 10 (((((((b*a)+c)*A)+((C*a)+d))*B)+((((D*a)+Fv)*A)+((E*a)+e)))) * x 11 ((((((b*a)+c)*B)*((b*A)+C))+(((((b*a)+c)*A)*D)+(((C*a)*D)+f)))) := by
  suffices h : (x 0 (a) * x 1 (A) * x 2 (B) * x 3 (b) * x 4 (c) * x 5 (C) * x 6 (D) * x 7 (d) * x 8 (E) * x 9 (Fv) * x 10 (e) * x 11 (f) * x 0 (a) * x 1 (A) * x 2 (B)) * 1 =
      (x 0 ((a+a)) * x 1 ((A+A)) * x 2 ((B+B)) * x 3 (b) * x 4 (((b*a)+c)) * x 5 (((b*A)+C)) * x 6 (((b*B)+D)) * x 7 (((((b*a)+c)*A)+((C*a)+d))) * x 8 (((((b*A)+C)*B)+((D*A)+E))) * x 9 (((((b*a)+c)*B)+((D*a)+Fv))) * x 10 (((((((b*a)+c)*A)+((C*a)+d))*B)+((((D*a)+Fv)*A)+((E*a)+e)))) * x 11 ((((((b*a)+c)*B)*((b*A)+C))+(((((b*a)+c)*A)*D)+(((C*a)*D)+f))))) * 1 by simpa only [mul_one] using h
  simp only [mul_assoc]
  conv_lhs =>
    rw [collect_comm x hc 11 0 (by decide) (by decide) (f) (a)]
    rw [collect_comm x hc 10 0 (by decide) (by decide) (e) (a)]
    rw [collect_comm x hc 9 0 (by decide) (by decide) (Fv) (a)]
    rw [collect_sum x hs 8 0 10 (by decide) (E) (a)]
    rw [collect_comm x hc 7 0 (by decide) (by decide) (d) (a)]
    rw [collect_sum x hs 6 0 9 (by decide) (D) (a)]
    rw [collect_sum x hs 5 0 7 (by decide) (C) (a)]
    rw [collect_comm x hc 4 0 (by decide) (by decide) (c) (a)]
    rw [collect_sum x hs 3 0 4 (by decide) (b) (a)]
    rw [collect_comm x hc 2 0 (by decide) (by decide) (B) (a)]
    rw [collect_comm x hc 1 0 (by decide) (by decide) (A) (a)]
    rw [collect_add x ha 0 (a) (a)]
    rw [collect_add x ha 4 ((b*a)) (c)]
    rw [collect_sum x hs 7 6 11 (by decide) ((C*a)) (D)]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((C*a)*D)) ((D*a))]
    rw [collect_comm x hc 11 7 (by decide) (by decide) (((C*a)*D)) (d)]
    rw [collect_comm x hc 9 7 (by decide) (by decide) ((D*a)) (d)]
    rw [collect_add x ha 7 ((C*a)) (d)]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((C*a)*D)) (E)]
    rw [collect_comm x hc 9 8 (by decide) (by decide) ((D*a)) (E)]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((C*a)*D)) ((E*a))]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((C*a)*D)) (Fv)]
    rw [collect_comm x hc 10 9 (by decide) (by decide) ((E*a)) (Fv)]
    rw [collect_add x ha 9 ((D*a)) (Fv)]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((C*a)*D)) (e)]
    rw [collect_add x ha 10 ((E*a)) (e)]
    rw [collect_add x ha 11 (((C*a)*D)) (f)]
    rw [collect_comm x hc 11 1 (by decide) (by decide) ((((C*a)*D)+f)) (A)]
    rw [collect_comm x hc 10 1 (by decide) (by decide) (((E*a)+e)) (A)]
    rw [collect_sum x hs 9 1 10 (by decide) (((D*a)+Fv)) (A)]
    rw [collect_comm x hc 8 1 (by decide) (by decide) (E) (A)]
    rw [collect_comm x hc 7 1 (by decide) (by decide) (((C*a)+d)) (A)]
    rw [collect_sum x hs 6 1 8 (by decide) (D) (A)]
    rw [collect_comm x hc 5 1 (by decide) (by decide) (C) (A)]
    rw [collect_sum x hs 4 1 7 (by decide) (((b*a)+c)) (A)]
    rw [collect_sum x hs 3 1 5 (by decide) (b) (A)]
    rw [collect_comm x hc 2 1 (by decide) (by decide) (B) (A)]
    rw [collect_add x ha 1 (A) (A)]
    rw [collect_comm x hc 5 4 (by decide) (by decide) ((b*A)) (((b*a)+c))]
    rw [collect_comm x hc 7 5 (by decide) (by decide) ((((b*a)+c)*A)) (C)]
    rw [collect_add x ha 5 ((b*A)) (C)]
    rw [collect_sum x hs 7 6 11 (by decide) ((((b*a)+c)*A)) (D)]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((((b*a)+c)*A)*D)) ((D*A))]
    rw [collect_comm x hc 11 7 (by decide) (by decide) (((((b*a)+c)*A)*D)) (((C*a)+d))]
    rw [collect_comm x hc 8 7 (by decide) (by decide) ((D*A)) (((C*a)+d))]
    rw [collect_add x ha 7 ((((b*a)+c)*A)) (((C*a)+d))]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((((b*a)+c)*A)*D)) (E)]
    rw [collect_add x ha 8 ((D*A)) (E)]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((((b*a)+c)*A)*D)) (((D*a)+Fv))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((((b*a)+c)*A)*D)) ((((D*a)+Fv)*A))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((((b*a)+c)*A)*D)) (((E*a)+e))]
    rw [collect_add x ha 10 ((((D*a)+Fv)*A)) (((E*a)+e))]
    rw [collect_add x ha 11 (((((b*a)+c)*A)*D)) ((((C*a)*D)+f))]
    rw [collect_comm x hc 11 2 (by decide) (by decide) ((((((b*a)+c)*A)*D)+(((C*a)*D)+f))) (B)]
    rw [collect_comm x hc 10 2 (by decide) (by decide) (((((D*a)+Fv)*A)+((E*a)+e))) (B)]
    rw [collect_comm x hc 9 2 (by decide) (by decide) (((D*a)+Fv)) (B)]
    rw [collect_comm x hc 8 2 (by decide) (by decide) (((D*A)+E)) (B)]
    rw [collect_sum x hs 7 2 10 (by decide) (((((b*a)+c)*A)+((C*a)+d))) (B)]
    rw [collect_comm x hc 6 2 (by decide) (by decide) (D) (B)]
    rw [collect_sum x hs 5 2 8 (by decide) (((b*A)+C)) (B)]
    rw [collect_sum x hs 4 2 9 (by decide) (((b*a)+c)) (B)]
    rw [collect_sum x hs 3 2 6 (by decide) (b) (B)]
    rw [collect_add x ha 2 (B) (B)]
    rw [collect_comm x hc 6 4 (by decide) (by decide) ((b*B)) (((b*a)+c))]
    rw [collect_sum x hs 9 5 11 (by decide) ((((b*a)+c)*B)) (((b*A)+C))]
    rw [collect_comm x hc 6 5 (by decide) (by decide) ((b*B)) (((b*A)+C))]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((((b*a)+c)*B)*((b*A)+C))) ((((b*A)+C)*B))]
    rw [collect_comm x hc 9 8 (by decide) (by decide) ((((b*a)+c)*B)) ((((b*A)+C)*B))]
    rw [collect_comm x hc 11 6 (by decide) (by decide) (((((b*a)+c)*B)*((b*A)+C))) (D)]
    rw [collect_comm x hc 9 6 (by decide) (by decide) ((((b*a)+c)*B)) (D)]
    rw [collect_comm x hc 8 6 (by decide) (by decide) ((((b*A)+C)*B)) (D)]
    rw [collect_add x ha 6 ((b*B)) (D)]
    rw [collect_comm x hc 11 7 (by decide) (by decide) (((((b*a)+c)*B)*((b*A)+C))) (((((b*a)+c)*A)+((C*a)+d)))]
    rw [collect_comm x hc 9 7 (by decide) (by decide) ((((b*a)+c)*B)) (((((b*a)+c)*A)+((C*a)+d)))]
    rw [collect_comm x hc 8 7 (by decide) (by decide) ((((b*A)+C)*B)) (((((b*a)+c)*A)+((C*a)+d)))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((((b*a)+c)*B)*((b*A)+C))) ((((((b*a)+c)*A)+((C*a)+d))*B))]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((((b*a)+c)*B)*((b*A)+C))) (((D*A)+E))]
    rw [collect_comm x hc 10 8 (by decide) (by decide) ((((((b*a)+c)*A)+((C*a)+d))*B)) (((D*A)+E))]
    rw [collect_comm x hc 9 8 (by decide) (by decide) ((((b*a)+c)*B)) (((D*A)+E))]
    rw [collect_add x ha 8 ((((b*A)+C)*B)) (((D*A)+E))]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((((b*a)+c)*B)*((b*A)+C))) (((D*a)+Fv))]
    rw [collect_comm x hc 10 9 (by decide) (by decide) ((((((b*a)+c)*A)+((C*a)+d))*B)) (((D*a)+Fv))]
    rw [collect_add x ha 9 ((((b*a)+c)*B)) (((D*a)+Fv))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((((b*a)+c)*B)*((b*A)+C))) (((((D*a)+Fv)*A)+((E*a)+e)))]
    rw [collect_add x ha 10 ((((((b*a)+c)*A)+((C*a)+d))*B)) (((((D*a)+Fv)*A)+((E*a)+e)))]
    rw [collect_add x ha 11 (((((b*a)+c)*B)*((b*A)+C))) ((((((b*a)+c)*A)*D)+(((C*a)*D)+f)))]


noncomputable section

/-- The actual central-coordinate shear induced by the first folded short root. -/
def shearParameters (P : Parameters) (a : ExtensionField P) (v : ArmsParameters P) :
    ArmsParameters P :=
  (![v.1 0 + v.2 0 * a,
      v.1 1 + higherCoefficient P a (v.1 0) + v.2 0 * a * fieldFrobenius P a],
    ![v.2 0,
      v.2 1 + armsPairing P a (v.1 1) +
        cubicTrace P (v.1 0 * fieldFrobenius P a * fieldFrobenius P (fieldFrobenius P a)) +
          v.2 0 * cubicNorm P a,
      v.2 2 + cubicTrace P (a * fieldFrobenius P (v.1 0) *
        fieldFrobenius P (fieldFrobenius P (v.1 0))) +
          v.2 0 * cubicTrace P (v.1 0 * fieldFrobenius P a *
            fieldFrobenius P (fieldFrobenius P a)) + (v.2 0)^2 * cubicNorm P a])


private def rawCoordinates (P : Parameters) (a : ExtensionField P) (v : ArmsParameters P) :
    Coordinates P := ![(a+a),
      ((fieldFrobenius P a)+(fieldFrobenius P a)),
      ((fieldFrobenius P (fieldFrobenius P a))+(fieldFrobenius P (fieldFrobenius P a))),
      ((v.2 0).val),
      ((((v.2 0).val)*a)+(v.1 0)),
      ((((v.2 0).val)*(fieldFrobenius P a))+(fieldFrobenius P (v.1 0))),
      ((((v.2 0).val)*(fieldFrobenius P (fieldFrobenius P a)))+(fieldFrobenius P (fieldFrobenius P (v.1 0)))),
      ((((((v.2 0).val)*a)+(v.1 0))*(fieldFrobenius P a))+(((fieldFrobenius P (v.1 0))*a)+(v.1 1))),
      ((((((v.2 0).val)*(fieldFrobenius P a))+(fieldFrobenius P (v.1 0)))*(fieldFrobenius P (fieldFrobenius P a)))+(((fieldFrobenius P (fieldFrobenius P (v.1 0)))*(fieldFrobenius P a))+(fieldFrobenius P (v.1 1)))),
      ((((((v.2 0).val)*a)+(v.1 0))*(fieldFrobenius P (fieldFrobenius P a)))+(((fieldFrobenius P (fieldFrobenius P (v.1 0)))*a)+(fieldFrobenius P (fieldFrobenius P (v.1 1))))),
      ((((((((v.2 0).val)*a)+(v.1 0))*(fieldFrobenius P a))+(((fieldFrobenius P (v.1 0))*a)+(v.1 1)))*(fieldFrobenius P (fieldFrobenius P a)))+(((((fieldFrobenius P (fieldFrobenius P (v.1 0)))*a)+(fieldFrobenius P (fieldFrobenius P (v.1 1))))*(fieldFrobenius P a))+(((fieldFrobenius P (v.1 1))*a)+((v.2 1).val)))),
      (((((((v.2 0).val)*a)+(v.1 0))*(fieldFrobenius P (fieldFrobenius P a)))*((((v.2 0).val)*(fieldFrobenius P a))+(fieldFrobenius P (v.1 0))))+(((((((v.2 0).val)*a)+(v.1 0))*(fieldFrobenius P a))*(fieldFrobenius P (fieldFrobenius P (v.1 0))))+((((fieldFrobenius P (v.1 0))*a)*(fieldFrobenius P (fieldFrobenius P (v.1 0))))+((v.2 2).val))))]

private theorem rawCoordinates_eq (P : Parameters) (hp : P.prime = 2)
    (a : ExtensionField P) (v : ArmsParameters P) :
    rawCoordinates P a v = expand P (extendOrbit P .arms (shearParameters P a v)) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hb : fieldFrobenius P (v.2 0).val = (v.2 0).val := (v.2 0).property
  funext i
  fin_cases i <;>
    simp [rawCoordinates, expand, extendOrbit, shearParameters, higherCoefficient,
      armsPairing_coe, cubicTrace_coe, cubicNorm, -fieldFrobenius_apply,
      map_add, map_mul, fieldFrobenius_three, hb, CharTwo.add_self_eq_zero] <;> ring

theorem shortSplit_shear (P : Parameters) (hp : P.prime = 2)
    (a : ExtensionField P) (v : ArmsParameters P) :
    shortSplit P 0 a * armsProduct P v * shortSplit P 0 a =
      armsProduct P (shearParameters P a v) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hs : SumExchange P := by
    obtain ⟨n,hn,rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact sumExchange_binary n hn
  have h := raw_collection (curve P) (curve_add P)
    (fun i j k h => hs i j k ((root_sum_iff i j k).mpr ((mem_sumTriples_iff i j k).mp h)))
    (fun i j hij h => nonsumCommute_parameters P i j hij (by
      rintro ⟨k,hk⟩
      exact h k ((mem_sumTriples_iff i j k).mpr ((root_sum_iff i j k).mp hk))))
    a (fieldFrobenius P a) (fieldFrobenius P (fieldFrobenius P a)) (v.2 0).val
    (v.1 0) (fieldFrobenius P (v.1 0)) (fieldFrobenius P (fieldFrobenius P (v.1 0)))
    (v.1 1) (fieldFrobenius P (v.1 1)) (fieldFrobenius P (fieldFrobenius P (v.1 1)))
    (v.2 1).val (v.2 2).val
  calc
    _ = orderedProduct P (rawCoordinates P a v) := by
      simpa [shortSplit, shortPosition, armsProduct, orderedProduct, expand, extendOrbit,
        rawCoordinates, List.ofFn_succ, -fieldFrobenius_apply, mul_assoc] using h
    _ = _ := by rw [rawCoordinates_eq P hp]; rfl

open Parabolics

/-- The faithful arms parameters on the literal parabolic radical. -/
def armsCoordinates (P : Parameters) (hp : P.prime = 2) :
    ArmsParameters P ≃ radical P .arms :=
  (armsEquiv P hp).trans (MulEquiv.subgroupCongr
    (radical_eq_descendedRootSubgroup P hp .arms).symm).toEquiv

theorem armsCoordinates_val (P : Parameters) (hp : P.prime = 2) (v : ArmsParameters P) :
    (armsCoordinates P hp v).val = toCarrier P (rootElement P hp .arms v) := rfl

theorem armsCoordinates_factorization (P : Parameters) (hp : P.prime = 2) (v : ArmsParameters P) :
    (armsCoordinates P hp v).val = long P hp 0 (v.2 0) * short P hp 1 (v.1 0) *
      short P hp 2 (v.1 1) * long P hp 1 (v.2 1) * long P hp 2 (v.2 2) := by
  rw [armsCoordinates_val,rootElement_factorization]
  simp [extendOrbit]

end
end Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
