module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FiveCenter
public import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The exceptional U₅ mixed coefficient from the actual rank-one torus

Subtract the expected norm coefficient from the unknown Hermitian correction.
Associativity makes this error additive in the A-parameter; multiplication in
the full nonabelian B-parameter group makes it additive in the first Hermitian
coordinate. Its central values vanish by the Hermitian commutator law.

At fixed-field order four, choose θ with θ⁴=θ+1 in the matrix field of order
sixteen. Such a θ is constructed using the factor X⁴+X+1 of X¹⁶−X. Its norm
has order three. Four applications of the actual h₁(θ) action, compared with
additivity and θ⁴=θ+1, force the entire error to vanish. This replaces the
five-equation calculation (8.35) without assuming any of its equations.

The B--D crossing also determines the torus action on C from its actions
on the two full Hermitian roots. Thus only the A, B and D actions remain
independent inputs. In the model these are the simple-coroot coordinates
(t,t⁻¹), whose middle diagonal correction is one. They agree with (8.20)
after changing the source's right conjugation to left conjugation.
The source charts and preceding crossings remain explicit inputs. The original quotient application is
UnitarySource/ExceptionalApplication. This is not source recognition.
Source: Fong--Seitz II (8.20), (8.24)--(8.30), pp.205--209, with an additive
weight argument in place of the printed exceptional linear system.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FiveMixedRigidity
variable {E Y : Type*} [Field E] [CharP E 2] [Group Y]
open Polynomial in
/-- The required source element exists in every field of sixteen elements. -/
theorem exists_exceptional_scalar (hcard : Nat.card E=16) :
    ∃ θ : E, θ^4=θ+1 := by
  let p : E[X] := X^4+X+1
  have hp : p ∣ X^16-X := by
    refine ⟨p^3+1,?_⟩
    dsimp only [p]
    ring_nf
    simp [CharTwo.ofNat_eq_mod,CharTwo.neg_eq]
  have hsplit : Splits (X^16-X : E[X]) := by
    simpa only [hcard] using (Polynomial.splits_X_pow_nat_card_sub_X (K := E))
  have hn : (X^16-X : E[X]) ≠ 0 := by
    intro he
    have hh := congrArg (fun f : E[X] => f.coeff 16) he
    norm_num [coeff_X] at hh
  have hd4 : degree p=4 := by
    dsimp only [p]
    compute_degree <;> norm_num
  have hd : degree p ≠ 0 := by rw [hd4]; norm_num
  obtain ⟨θ,hθ⟩ := (hsplit.of_dvd hn hp).exists_eval_eq_zero hd
  refine ⟨θ,?_⟩
  simp only [p,eval_add,eval_pow,eval_X,eval_one] at hθ
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hθ

variable (J : HermitianForm 5 E)

private def sectionParameter (κ : E) (hκ : κ+J.conj κ=1) (x : E) : FivePositive.Parameter J :=
  ⟨(x,κ*x*J.conj x),by
    change κ*x*J.conj x+J.conj (κ*x*J.conj x)+x*J.conj x=0
    simp only [map_mul, J.conj_involutive x]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) x*J.conj x*hκ⟩

variable (r : PositiveMaps Y (Multiplicative E) (FivePositive.Parameter J)
  (Multiplicative E) (FivePositive.Parameter J))
variable (T : FivePositive.Parameter J → E → FivePositive.Parameter J)
variable (hD : Function.Injective r.D)
variable (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1=a*p.val.1)
variable (hAD : ∀ a d, Commute (r.A a) (r.D d))
variable (hCD : ∀ c d, Commute (r.C c) (r.D d))
variable (hBC : ∀ p c, Commute (r.B p) (r.C c))
variable (hCA : ∀ a c, r.C (Multiplicative.ofAdd c)*r.A (Multiplicative.ofAdd a) =
  r.A (Multiplicative.ofAdd a)*r.D (FivePositive.traceParameter J a c)*r.C (Multiplicative.ofAdd c))
variable (hBD : ∀ p q, r.B p*r.D q = r.D q*
  r.C (Multiplicative.ofAdd (q.val.1*J.conj p.val.1))*r.B p)
variable (hBA : ∀ a p, r.B p*r.A (Multiplicative.ofAdd a) =
  r.A (Multiplicative.ofAdd a)*r.D (T p a)*
    r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p)

include hBD in
/-- The B--D crossing forces the C-root weight from the two Hermitian
root actions. No injectivity of the charts or correction formula is used. -/
theorem crossing_torus_action (κ : E) (hκ : κ+J.conj κ=1)
    (t : E) (ht : t≠0) (k : Y ≃* Y)
    (hB : ∀ p, k (r.B (FivePositive.normParameter J t p))=r.B p)
    (hDt : ∀ p, k (r.D p)=r.D (FivePositive.normParameter J t p))
    (c : E) : k (r.C (Multiplicative.ofAdd c))=
      r.C (Multiplicative.ofAdd (t/(J.conj t)*c)) := by
  let p := sectionParameter J κ hκ 1
  let q := sectionParameter J κ hκ (c/J.conj t)
  have hbart : J.conj t ≠ 0 := (map_ne_zero J.conj).mpr ht
  have hbefore : q.val.1*J.conj (FivePositive.normParameter J t p).val.1=c := by
    change (c/J.conj t)*J.conj (t*1)=c
    rw [mul_one, div_mul_cancel₀ _ hbart]
  have hafter : (FivePositive.normParameter J t q).val.1*J.conj p.val.1=
      t/J.conj t*c := by
    change (t*(c/J.conj t))*J.conj (1:E)=_
    rw [map_one,mul_one]
    ring
  have he := congrArg k (hBD (FivePositive.normParameter J t p) q)
  simp only [map_mul,hB,hDt,hbefore] at he
  rw [hBD,hafter] at he
  exact (mul_left_cancel (mul_right_cancel he)).symm

private def error (p : FivePositive.Parameter J) (a : E) : E :=
  (T p a).val.2-a*J.conj a*p.val.2

include hD hfst hCD hBC hBD hBA in
private theorem error_mul (p q : FivePositive.Parameter J) (a : E) :
    error J T (p*q) a=error J T p a+error J T q a := by
  have he := congrArg (fun u : FivePositive.Parameter J => u.val.2)
    (FiveCoefficients.correction_mul J r T hCD hBA hD hfst hBC hBD p q a)
  change (T (p*q) a).val.2 =
    (T p a).val.2+(T q a).val.2-(T p a).val.1*J.conj (T q a).val.1 at he
  simp only [hfst,map_mul] at he
  change (T (p*q) a).val.2-a*J.conj a*(p.val.2+q.val.2-p.val.1*J.conj q.val.1)=_
  dsimp only [error]
  linear_combination he

include hD hfst hAD hCD hCA hBA in
private theorem error_add (p : FivePositive.Parameter J) (a b : E) :
    error J T p (a+b)=error J T p a+error J T p b := by
  have he := FiveCoefficients.coefficient_add J r T hAD hCD hCA hBA hD hfst p a b
  dsimp only [error]
  rw [map_add]
  linear_combination he

include hD hfst hCD hBC hBD hBA in
private theorem error_center (κ : E) (hκ : κ+J.conj κ=1)
    (p : FivePositive.Parameter J) (hp : p.val.1=0) (a : E) : error J T p a=0 := by
  have he := FiveCenter.correction_on_center J r T κ hκ hD hfst hCD hBC hBD hBA p hp a
  rw [error,he]
  exact sub_self _

include hD hfst hCD hBC hBD hBA in
private theorem error_eq_of_first_eq (κ : E) (hκ : κ+J.conj κ=1)
    (p q : FivePositive.Parameter J) (hpq : p.val.1=q.val.1) (a : E) :
    error J T p a=error J T q a := by
  have hmul := error_mul J r T hD hfst hCD hBC hBD hBA p q⁻¹ a
  have hone := error_mul J r T hD hfst hCD hBC hBD hBA q q⁻¹ a
  have hc : (p*q⁻¹).val.1=0 := by
    change p.val.1 + -q.val.1=0
    rw [hpq,add_neg_cancel]
  rw [error_center J r T hD hfst hCD hBC hBD hBA κ hκ _ hc] at hmul
  rw [mul_inv_cancel, error_center J r T hD hfst hCD hBC hBD hBA κ hκ 1 rfl] at hone
  exact add_right_cancel (hmul.symm.trans hone)

private def reducedError (κ : E) (hκ : κ+J.conj κ=1) (x a : E) : E :=
  error J T (sectionParameter J κ hκ x) a

include hD hfst hCD hBC hBD hBA in
private theorem error_eq_reduced (κ : E) (hκ : κ+J.conj κ=1)
    (p : FivePositive.Parameter J) (a : E) :
    error J T p a=reducedError J T κ hκ p.val.1 a :=
  error_eq_of_first_eq J r T hD hfst hCD hBC hBD hBA κ hκ p (sectionParameter J κ hκ p.val.1) rfl a

include hD hfst hCD hBC hBD hBA in
private theorem reducedError_add_left (κ : E) (hκ : κ+J.conj κ=1) (x y a : E) :
    reducedError J T κ hκ (x+y) a=
      reducedError J T κ hκ x a+reducedError J T κ hκ y a := by
  have he := error_mul J r T hD hfst hCD hBC hBD hBA
    (sectionParameter J κ hκ x) (sectionParameter J κ hκ y) a
  rw [error_eq_reduced J r T hD hfst hCD hBC hBD hBA κ hκ] at he
  exact he

include hD hfst hAD hCD hCA hBA in
private theorem reducedError_add_right (κ : E) (hκ : κ+J.conj κ=1) (x a b : E) :
    reducedError J T κ hκ x (a+b)=
      reducedError J T κ hκ x a+reducedError J T κ hκ x b :=
  error_add J r T hD hfst hAD hCD hCA hBA _ a b

/-- The order-fifteen torus has no weight in the additive tensor error. -/
theorem additive_torus_rigidity (f : E → E → E) (θ c : E)
    (hθ : θ^4=θ+1) (hc : c^3=1) (hcne : c ≠ 1)
    (hleft : ∀ x y a, f (x+y) a=f x a+f y a)
    (hright : ∀ x a b, f x (a+b)=f x a+f x b)
    (hscale : ∀ x a, f (θ*x) a=c*f x (θ^2*a)) : ∀ x a, f x a=0 := by
  have hiter (n : ℕ) (x a : E) : f (θ^n*x) a=c^n*f x (θ^(2*n)*a) := by
    induction n generalizing x a with
    | zero => simp
    | succ n ih =>
      have hp : θ^(2*n)*(θ^2*a)=θ^(2*(n+1))*a := by
        rw [Nat.mul_succ,pow_add]
        ring
      calc
        _=c*(c^n*f x (θ^(2*n)*(θ^2*a))) := by
          rw [pow_succ',mul_assoc,hscale,ih]
        _=_ := by rw [hp,pow_succ']; ring
  have hθ8 : θ^8=θ^2+1 := by
    calc
      θ^8=(θ^4)^2 := by ring
      _=θ^2+1 := by rw [hθ]; ring_nf; simp [CharTwo.two_eq_zero]
  have hc4 : c^4=c := by rw [show c^4=c^3*c by ring,hc,one_mul]
  intro x a
  have he := hiter 4 x a
  norm_num only [Nat.reduceMul] at he
  rw [hθ,hθ8,hc4,add_mul,one_mul,hleft,add_mul,one_mul,hright,hscale] at he
  have he' : (c-1)*f x a=0 := by linear_combination -he
  exact (mul_eq_zero.mp he').resolve_left (sub_ne_zero.mpr hcne)

omit [CharP E 2] in
include hD hBA in
private theorem correction_torus (t : E) (ht : t ≠ 0) (k : Y ≃* Y)
    (hA : ∀ a, k (r.A (Multiplicative.ofAdd a))=r.A (Multiplicative.ofAdd (t^2*a)))
    (hB : ∀ p, k (r.B (FivePositive.normParameter J t p))=r.B p)
    (hC : ∀ c, k (r.C (Multiplicative.ofAdd c))=r.C (Multiplicative.ofAdd (t/(J.conj t)*c)))
    (hDt : ∀ p, k (r.D p)=r.D (FivePositive.normParameter J t p))
    (p : FivePositive.Parameter J) (a : E) :
    T p (t^2*a)=FivePositive.normParameter J t (T (FivePositive.normParameter J t p) a) := by
  have hbart : J.conj t ≠ 0 := (map_ne_zero J.conj).mpr ht
  have hz : t/J.conj t*(a*J.conj (FivePositive.normParameter J t p).val.2)=
      (t^2*a)*J.conj p.val.2 := by
    change t/J.conj t*(a*J.conj (t*J.conj t*p.val.2))=_
    simp only [map_mul,J.conj_involutive t]
    field_simp
  have he := congrArg k (hBA a (FivePositive.normParameter J t p))
  simp only [map_mul,hA,hB,hC,hDt,hz] at he
  rw [hBA] at he
  apply hD
  exact mul_left_cancel (mul_right_cancel (mul_right_cancel he))

omit [CharP E 2] in
include hD hBA in
private theorem error_torus (t : E) (ht : t ≠ 0) (k : Y ≃* Y)
    (hA : ∀ a, k (r.A (Multiplicative.ofAdd a))=r.A (Multiplicative.ofAdd (t^2*a)))
    (hB : ∀ p, k (r.B (FivePositive.normParameter J t p))=r.B p)
    (hC : ∀ c, k (r.C (Multiplicative.ofAdd c))=r.C (Multiplicative.ofAdd (t/(J.conj t)*c)))
    (hDt : ∀ p, k (r.D p)=r.D (FivePositive.normParameter J t p))
    (p : FivePositive.Parameter J) (a : E) :
    error J T p (t^2*a)=(t*J.conj t)*error J T (FivePositive.normParameter J t p) a := by
  have he := congrArg (fun q : FivePositive.Parameter J => q.val.2)
    (correction_torus J r T hD hBA t ht k hA hB hC hDt p a)
  change (T p (t^2*a)).val.2=t*J.conj t*(T (FivePositive.normParameter J t p) a).val.2 at he
  dsimp only [error]
  change _ = t*J.conj t*((T (FivePositive.normParameter J t p) a).val.2-a*J.conj a*(t*J.conj t*p.val.2))
  simp only [map_mul,map_pow]
  linear_combination he

include hD hfst hAD hCD hBC hCA hBD hBA in
/-- One actual rank-one torus action determines the correction over F₁₆. -/
theorem correction_eq_norm_of_exceptional_torus
    (θ : E) (hθ : θ^4=θ+1) (hbarθ : J.conj θ=θ+1) (k : Y ≃* Y)
    (hA : ∀ a, k (r.A (Multiplicative.ofAdd a))=r.A (Multiplicative.ofAdd (θ^2*a)))
    (hB : ∀ p, k (r.B (FivePositive.normParameter J θ p))=r.B p)
    (hC : ∀ c, k (r.C (Multiplicative.ofAdd c))=r.C (Multiplicative.ofAdd (θ/(J.conj θ)*c)))
    (hDt : ∀ p, k (r.D p)=r.D (FivePositive.normParameter J θ p))
    (p : FivePositive.Parameter J) (a : E) : T p a=FivePositive.normParameter J a p := by
  have hθne : θ ≠ 0 := by
    intro he
    rw [he] at hθ
    simp at hθ
  have htrace : θ+J.conj θ=1 := by rw [hbarθ,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
  let ω : E := θ*J.conj θ
  have hω : ω^2=ω+1 := by
    dsimp only [ω]
    rw [hbarθ]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hθ
  have hω3 : ω^3=1 := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) (ω+1)*hω
  have hω2ne : ω^2 ≠ 1 := by
    intro he
    have hz : ω=0 := by linear_combination he-hω
    rw [hz] at hω
    simp at hω
  have hc : (ω^2)^3=1 := by rw [show (ω^2)^3=(ω^3)^2 by ring,hω3,one_pow]
  let f := reducedError J T θ htrace
  have hs (x b : E) : f (θ*x) b=ω^2*f x (θ^2*b) := by
    have he := error_torus J r T hD hBA θ hθne k hA hB hC hDt
      (sectionParameter J θ htrace x) b
    simp only [error_eq_reduced J r T hD hfst hCD hBC hBD hBA θ htrace] at he
    change f x (θ^2*b)=ω*f (θ*x) b at he
    linear_combination -ω^2*he-f (θ*x) b*hω3
  have hz := additive_torus_rigidity f θ (ω^2) hθ hc hω2ne
    (reducedError_add_left J r T hD hfst hCD hBC hBD hBA θ htrace)
    (reducedError_add_right J r T hD hfst hAD hCD hCA hBA θ htrace) hs p.val.1 a
  have he : error J T p a=0 :=
    (error_eq_reduced J r T hD hfst hCD hBC hBD hBA θ htrace p a).trans hz
  apply Subtype.ext
  apply Prod.ext (hfst p a)
  exact sub_eq_zero.mp he

include hD hfst hAD hCD hBC hCA hBD hBA in
/-- The exceptional source coefficient supplies the full positive relations. -/
theorem relations_of_exceptional_torus
    (θ : E) (hθ : θ^4=θ+1) (hbarθ : J.conj θ=θ+1) (k : Y ≃* Y)
    (hA : ∀ a, k (r.A (Multiplicative.ofAdd a))=r.A (Multiplicative.ofAdd (θ^2*a)))
    (hB : ∀ p, k (r.B (FivePositive.normParameter J θ p))=r.B p)
    (hC : ∀ c, k (r.C (Multiplicative.ofAdd c))=r.C (Multiplicative.ofAdd (θ/(J.conj θ)*c)))
    (hDt : ∀ p, k (r.D p)=r.D (FivePositive.normParameter J θ p)) : FivePositive.Relations J r where
  AD := hAD
  CD := hCD
  BC := hBC
  CA := hCA
  BD := hBD
  BA a p := by
    rw [hBA, correction_eq_norm_of_exceptional_torus J r T hD hfst hAD hCD hBC hCA hBD hBA θ hθ hbarθ k hA hB hC hDt]

include hD hfst hAD hCD hBC hCA hBD hBA in
/-- The exceptional positive relations need only the three independent
rank-one torus actions: the C action follows from the B--D crossing. -/
theorem relations_of_exceptional_rankOne_torus
    (θ : E) (hθ : θ^4=θ+1) (hbarθ : J.conj θ=θ+1) (k : Y ≃* Y)
    (hA : ∀ a, k (r.A (Multiplicative.ofAdd a))=r.A (Multiplicative.ofAdd (θ^2*a)))
    (hB : ∀ p, k (r.B (FivePositive.normParameter J θ p))=r.B p)
    (hDt : ∀ p, k (r.D p)=r.D (FivePositive.normParameter J θ p)) :
    FivePositive.Relations J r := by
  have hθne : θ ≠ 0 := by
    intro he
    rw [he] at hθ
    simp at hθ
  have htrace : θ+J.conj θ=1 := by
    rw [hbarθ,←add_assoc,CharTwo.add_self_eq_zero,zero_add]
  exact relations_of_exceptional_torus J r T hD hfst hAD hCD hBC hCA hBD hBA
    θ hθ hbarθ k hA hB (crossing_torus_action J r hBD θ htrace θ hθne k hB hDt) hDt

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.FiveMixedRigidity
