module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.PositiveCoefficients

/-!
# Deriving the triality highest-coefficient polarization

The source right-commutator identity on [B(1), A(a)A(b)] forces the
additive defect of the unknown highest-root coefficient g. Collecting the
four radical factors C, D, E and F contributes the two cubic trace terms.
Torus covariance then expresses g(a,1) as N(a)g(1,1), so the group identity
proves the scalar polarization equation (9.33). The existing cubic-norm
argument determines g(1,1)=1, uniformly including q=2.

UnnormalizedStage records the earlier commutator and action equations,
without (9.33). The constructor proves that missing field of the existing
CoefficientStage API. Thus the positive presentation consumer no longer
needs polarization as an independent source premise. Constructing the
remaining module equations and covariance from 6E(b) is still required.
Source: Fong--Seitz II, printed pp.219--220, (9.28)--(9.34).
-/

@[expose] public noncomputable section
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
variable {F Y : Type*} [Field F] [Group Y] {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

private theorem commutator_exchange (x y : Y) :
    x*y = y*x*rightCommutator x y := by simp [rightCommutator, mul_assoc]
private theorem right_conj_eq (x y : Y) :
    y⁻¹*x*y = x*rightCommutator x y := by simp [rightCommutator, mul_assoc]
private theorem rightCommutator_mul_right (x y z : Y) :
    rightCommutator x (y*z) = rightCommutator x z *
      (z⁻¹*rightCommutator x y*z) := by simp [rightCommutator, mul_inv_rev, mul_assoc]

namespace RawRoots
variable (r : RawRoots σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)
/-- Earlier source commutator equations and torus covariance. The highest
coefficient is unknown and its polarization is not assumed. -/
structure UnnormalizedStage where
  g : F → K → K
  highest_injective : Function.Injective (r.long 2)
  short0_long1 : ∀ a b, Commute (r.s 0 a) (r.l 1 b)
  short0_long2 : ∀ a b, Commute (r.s 0 a) (r.l 2 b)
  long0_short1 : ∀ a b, Commute (r.l 0 a) (r.s 1 b)
  long0_short2 : ∀ a b, Commute (r.l 0 a) (r.s 2 b)
  long0_long2 : ∀ a b, Commute (r.l 0 a) (r.l 2 b)
  short1_long1 : ∀ a b, Commute (r.s 1 a) (r.l 1 b)
  short1_long2 : ∀ a b, Commute (r.s 1 a) (r.l 2 b)
  short2_long1 : ∀ a b, Commute (r.s 2 a) (r.l 1 b)
  short2_long2 : ∀ a b, Commute (r.s 2 a) (r.l 2 b)
  long1_long2 : ∀ a b, Commute (r.l 1 a) (r.l 2 b)
  lower : ∀ a b, rightCommutator (r.s 2 b) (r.s 0 a) = r.l 1 (e.trace (a*b))
  upper : ∀ a b, rightCommutator (r.s 2 b) (r.s 1 a) = r.l 2 (e.trace (a*b))
  short_short : ∀ a b, rightCommutator (r.s 1 b) (r.s 0 a) =
    r.s 2 (σ a * σ (σ b) + σ (σ a) * σ b) *
      r.l 1 (e.trace (σ a * σ (σ a) * b)) * r.l 2 (e.trace (a * σ b * σ (σ b)))
  mixed : ∀ a b, rightCommutator (r.l 0 b) (r.s 0 a) =
    r.s 1 (a*b.val) * r.s 2 (σ a * σ (σ a) * b.val) *
      r.l 1 (e.norm a * b) * r.l 2 (g a b)
  long_long : ∀ a b, rightCommutator (r.l 1 b) (r.l 0 a) = r.l 2 (a*b)
  covariance : CoefficientCovariance e g

namespace UnnormalizedStage
variable {r e} (d : r.UnnormalizedStage e)

private def word (r : RawRoots σ Y) (c t : F) (v z : K) : Y := r.s 1 c * r.s 2 t * r.l 1 v * r.l 2 z

include d

private theorem exchange (c t : F) :
    r.s 2 t * r.s 1 c = r.s 1 c * r.s 2 t * r.l 2 (e.trace (c*t)) := by
  rw [commutator_exchange, d.upper]

private theorem word_mul (c t : F) (v z : K) (c' t' : F) (v' z' : K) :
    word r c t v z * word r c' t' v' z' =
      word r (c+c') (t+t') (v+v') (z+z'+e.trace (c'*t)) := by
  have hCD : r.s 1 c * r.s 2 t * (r.s 1 c' * r.s 2 t') =
      r.s 1 (c+c') * r.s 2 (t+t') * r.l 2 (e.trace (c'*t)) := by
    calc
      _ = r.s 1 c * (r.s 2 t * r.s 1 c') * r.s 2 t' := by group
      _ = r.s 1 c * (r.s 1 c' * r.s 2 t * r.l 2 (e.trace (c'*t))) * r.s 2 t' := by
        rw [d.exchange]
      _ = (r.s 1 c * r.s 1 c') * (r.s 2 t * (r.l 2 (e.trace (c'*t)) * r.s 2 t')) := by group
      _ = (r.s 1 c * r.s 1 c') * (r.s 2 t * (r.s 2 t' * r.l 2 (e.trace (c'*t)))) := by
        rw [(d.short2_long2 t' _).eq]
      _ = (r.s 1 c * r.s 1 c') * (r.s 2 t * r.s 2 t') * r.l 2 (e.trace (c'*t)) := by group
      _ = _ := by simp only [s, l, ← map_mul, ← ofAdd_add]
  have hEF : (r.l 1 v * r.l 2 z) * (r.l 1 v' * r.l 2 z') =
      r.l 1 (v+v') * r.l 2 (z+z') := by
    rw [((d.long1_long2 v' z).symm).mul_mul_mul_comm]
    simp only [l, ← map_mul, ← ofAdd_add]
  have hcomm := (((d.short1_long1 c' v).mul_right (d.short1_long2 c' z)).mul_left
    ((d.short2_long1 t' v).mul_right (d.short2_long2 t' z))).symm
  simp only [word]
  calc
    _ = (r.s 1 c * r.s 2 t) * (r.l 1 v * r.l 2 z) *
        ((r.s 1 c' * r.s 2 t') * (r.l 1 v' * r.l 2 z')) := by group
    _ = ((r.s 1 c * r.s 2 t) * (r.s 1 c' * r.s 2 t')) *
        ((r.l 1 v * r.l 2 z) * (r.l 1 v' * r.l 2 z')) := hcomm.mul_mul_mul_comm _ _
    _ = (r.s 1 (c+c') * r.s 2 (t+t') * r.l 2 (e.trace (c'*t))) *
        (r.l 1 (v+v') * r.l 2 (z+z')) := by rw [hCD,hEF]
    _ = (r.s 1 (c+c') * r.s 2 (t+t')) * r.l 1 (v+v') *
        (r.l 2 (e.trace (c'*t)) * r.l 2 (z+z')) :=
      ((d.long1_long2 (v+v') (e.trace (c'*t))).symm).mul_mul_mul_comm _ _
    _ = _ := by
      rw [← map_mul, ← ofAdd_add]
      congr 2
      abel_nf

private theorem word_conjugate (a c t : F) (v z : K) :
    (r.s 0 a)⁻¹ * word r c t v z * r.s 0 a =
      word r c (t + (σ a * σ (σ c) + σ (σ a) * σ c))
        (v + e.trace (σ a * σ (σ a) * c) + e.trace (a*t))
        (z + e.trace (a * σ c * σ (σ c))) := by
  let φ := MulAut.conj (r.s 0 a)⁻¹
  have hc : φ (r.s 1 c) = word r c
      (σ a * σ (σ c) + σ (σ a) * σ c)
      (e.trace (σ a * σ (σ a) * c)) (e.trace (a * σ c * σ (σ c))) := by
    change (r.s 0 a)⁻¹ * r.s 1 c * ((r.s 0 a)⁻¹)⁻¹ = _
    rw [inv_inv, right_conj_eq, d.short_short]
    simp only [word, mul_assoc]
  have ht : φ (r.s 2 t) = word r 0 t (e.trace (a*t)) 0 := by
    change (r.s 0 a)⁻¹ * r.s 2 t * ((r.s 0 a)⁻¹)⁻¹ = _
    rw [inv_inv, right_conj_eq, d.lower]
    simp [word, s, l]
  have hv : φ (r.l 1 v) = word r 0 0 v 0 := by
    change (r.s 0 a)⁻¹ * r.l 1 v * ((r.s 0 a)⁻¹)⁻¹ = _
    rw [inv_inv, (d.short0_long1 a v).inv_left.eq]
    simp [word, s, l, mul_assoc]
  have hz : φ (r.l 2 z) = word r 0 0 0 z := by
    change (r.s 0 a)⁻¹ * r.l 2 z * ((r.s 0 a)⁻¹)⁻¹ = _
    rw [inv_inv, (d.short0_long2 a z).inv_left.eq]
    simp [word, s, l, mul_assoc]
  have hφ (x : Y) : φ x = (r.s 0 a)⁻¹ * x * r.s 0 a := by simp [φ]
  rw [← hφ (word r c t v z)]
  calc
    _ = word r c (σ a * σ (σ c) + σ (σ a) * σ c)
          (e.trace (σ a * σ (σ a) * c)) (e.trace (a * σ c * σ (σ c))) *
        word r 0 t (e.trace (a*t)) 0 * word r 0 0 v 0 * word r 0 0 0 z := by
      change φ (r.s 1 c * r.s 2 t * r.l 1 v * r.l 2 z) = _
      rw [map_mul, map_mul, map_mul, hc, ht, hv, hz]
    _ = _ := by
      rw [d.word_mul, d.word_mul, d.word_mul]
      have hzero : e.trace 0 = 0 := Subtype.ext (by simp [ScalarMarking.trace])
      simp only [zero_mul, hzero, add_zero]
      congr 1 <;> abel

private theorem mixed_one (a : F) :
    rightCommutator (r.l 0 1) (r.s 0 a) =
      word r a (σ a * σ (σ a)) (e.norm a) (d.g a 1) := by
  simpa only [Subfield.coe_one, mul_one, word] using d.mixed a 1

/-- The commutator identity forces the highest coefficient's additive defect.
No polarization identity is assumed. -/
theorem g_add_one (a b : F) :
    d.g (a+b) 1 = d.g a 1 + d.g b 1 +
      e.trace (b * σ a * σ (σ a)) + e.trace (a * σ b * σ (σ b)) := by
  have hadd : r.s 0 a * r.s 0 b = r.s 0 (a+b) := by
    simp only [s, ← map_mul, ← ofAdd_add]
  have he := rightCommutator_mul_right (r.l 0 1) (r.s 0 a) (r.s 0 b)
  rw [hadd, d.mixed_one, d.mixed_one, d.mixed_one, d.word_conjugate, d.word_mul] at he
  have hD : σ b * σ (σ b) +
      (σ a * σ (σ a) + (σ b * σ (σ a) + σ (σ b) * σ a)) =
        σ (a+b) * σ (σ (a+b)) := by simp only [map_add]; ring
  have hE : e.norm b + (e.norm a + e.trace (σ b * σ (σ b) * a) +
      e.trace (b * (σ a * σ (σ a)))) = e.norm (a+b) := by
    apply Subtype.ext
    simp only [ScalarMarking.norm, ScalarMarking.trace, Subfield.coe_add, map_add, map_mul, e.cubic]
    ring
  rw [add_comm b a, hD, hE] at he
  have hF : d.g b 1 + (d.g a 1 + e.trace (b * σ a * σ (σ a))) +
      e.trace (a * (σ b * σ (σ b))) =
      d.g a 1 + d.g b 1 + e.trace (b * σ a * σ (σ a)) +
        e.trace (a * σ b * σ (σ b)) := by rw [← mul_assoc a]; abel
  rw [hF] at he
  apply Multiplicative.ofAdd.injective
  apply d.highest_injective
  exact mul_left_cancel he

private theorem g_zero_left (b : K) : d.g 0 b = 0 := by
  apply Multiplicative.ofAdd.injective
  apply d.highest_injective
  have h := d.mixed 0 b
  simpa [s, l, rightCommutator] using h.symm

private theorem g_zero_right (a : F) : d.g a 0 = 0 := by
  apply Multiplicative.ofAdd.injective
  apply d.highest_injective
  have h := d.mixed a 0
  simpa [s, l, rightCommutator] using h.symm

variable [Finite F] [CharP F 2]

/-- The source action covariance and commutator multiplication imply (9.33),
including q=2. -/
theorem polarization (a b : F) :
    (e.norm (a+b) + e.norm a + e.norm b) * d.g 1 1 =
      e.trace (a * σ a * σ (σ b)) + e.trace (a * σ b * σ (σ b)) := by
  have hshape (x : F) : d.g x 1 = e.norm x * d.g 1 1 := by
    simpa only [one_pow, mul_one] using
      coefficient_shape e d.g d.covariance d.g_zero_left d.g_zero_right x 1
  calc
    _ = d.g (a+b) 1 + d.g a 1 + d.g b 1 := by
      rw [add_mul, add_mul, ← hshape (a+b), ← hshape a, ← hshape b]
    _ = (d.g a 1 + d.g a 1) + (d.g b 1 + d.g b 1) +
        (e.trace (b * σ a * σ (σ a)) + e.trace (a * σ b * σ (σ b))) := by
      rw [d.g_add_one]; abel
    _ = e.trace (b * σ a * σ (σ a)) + e.trace (a * σ b * σ (σ b)) := by
      simp only [CharTwo.add_self_eq_zero, zero_add]
    _ = _ := by
      rw [show b * σ a * σ (σ a) = σ a * σ (σ a) * b by ring, trace_short_short]

/-- The original coefficient-stage contract is constructed with its polarization
field proved by the group identity, rather than supplied. -/
def toCoefficientStage : r.CoefficientStage e :=
  { d with polarization := d.polarization }

/-- All fifteen ordered source relations now follow without assuming (9.33). -/
theorem relations : e.SourceRelations r.markedShort r.long :=
  d.toCoefficientStage.relations

end UnnormalizedStage
end RawRoots
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
