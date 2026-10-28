module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.CubicCoefficient

/-!
# Triality source commutators and the positive presentation

The short source roots are U₂, U₂^s₁ and U₂^(s₁s₂). The native third
short root at t is the source third short root at σ(t); this Frobenius
shift is necessary in both the trace pairings and the mixed exchange.

At the coefficient stage, the right commutator [U₁(b), U₂(a)] still
contains an unknown highest-root coefficient g(a,b). The source torus
covariance and polarization determine g(a,b)=N(a)b² in every binary field.
Reversing this commutator reverses the two middle short factors; their
commutator contributes N(a)b² again, cancelling the extra highest factor.
The result is all fifteen literal ordered equations of ScalarMarking.

The CoefficientStage inputs are intermediate equations (9.28)--(9.33) and
(9.35), not a theorem deriving them from 6E(b). Constructing these inputs
from the actual source modules, roots and torus remains necessary. No
ambient model map or desired final SourceRelations certificate is assumed.

Source: Fong--Seitz II, printed pp.219--220, equations (9.27)--(9.35);
GLS3 2.4.5 in the native D₄ orbit marking.
-/

@[expose] public noncomputable section
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource

/-- The paper uses right commutators and right conjugation. -/
def rightCommutator {Y : Type*} [Group Y] (x y : Y) : Y := x⁻¹*y⁻¹*x*y

private theorem reverse_commutator_exchange {Y : Type*} [Group Y] (x y : Y) :
    x*y = y*x*(rightCommutator y x)⁻¹ := by
  simp [rightCommutator, mul_inv_rev, mul_assoc]

private theorem root_inv {R Y : Type*} [Field R] [CharP R 2] [Group Y]
    (f : Multiplicative R →* Y) (x : R) : (f (.ofAdd x))⁻¹ = f (.ofAdd x) := by
  rw [← map_inv, ← ofAdd_neg, CharTwo.neg_eq]

private theorem root_square {R Y : Type*} [Field R] [CharP R 2] [Group Y]
    (f : Multiplicative R →* Y) (x : R) : f (.ofAdd x) * f (.ofAdd x) = 1 := by
  rw [← map_mul, ← ofAdd_add, CharTwo.add_self_eq_zero]
  exact map_one f

variable {F Y : Type*} [Field F] [Group Y] {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

/-- The source order is U₂, U₂^s₁, U₂^(s₁s₂) on short roots and
U₁, U₁^s₂, U₁^(s₂s₁) on long roots. -/
structure RawRoots (σ : F ≃+* F) (Y : Type*) [Group Y] where
  short : Fin 3 → Multiplicative F →* Y
  long : Fin 3 → Multiplicative (ScalarMarking.SourceFixed (σ := σ)) →* Y

namespace RawRoots
variable (r : RawRoots σ Y)
abbrev s (i : Fin 3) (x : F) : Y := r.short i (.ofAdd x)
abbrev l (i : Fin 3) (x : K) : Y := r.long i (.ofAdd x)

/-- The third short root changes its orbit origin by one Frobenius.
The other five source parametrizations are retained. -/
def markedShort (i : Fin 3) : Multiplicative F →* Y :=
  if i = 2 then (r.short i).comp σ.toRingHom.toAddMonoidHom.toMultiplicative else r.short i

@[simp] theorem markedShort_zero (x : F) : r.markedShort 0 (.ofAdd x) = r.s 0 x := rfl
@[simp] theorem markedShort_one (x : F) : r.markedShort 1 (.ofAdd x) = r.s 1 x := rfl
@[simp] theorem markedShort_two (x : F) : r.markedShort 2 (.ofAdd x) = r.s 2 (σ x) := rfl

variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

/-- Equations at the coefficient stage of II §9B. The function g is still
unknown. Deriving these premises from 6E(b) and the actual module actions
is a separate, still necessary source construction. -/
structure CoefficientStage where
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
  polarization : ∀ a b, (e.norm (a+b) + e.norm a + e.norm b) * g 1 1 =
    e.trace (a * σ a * σ (σ b)) + e.trace (a * σ b * σ (σ b))

namespace CoefficientStage
variable {r e} (d : r.CoefficientStage e)
include d

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
/-- The unknown highest coefficient is determined, without excluding q=2. -/
theorem coefficient (a : F) (b : K) : d.g a b = e.norm a * b^2 :=
  coefficient_eq_norm e d.g d.covariance d.g_zero_left d.g_zero_right d.polarization a b

omit [Finite F] in
private theorem upper_exchange (a b : F) :
    r.s 1 a * r.s 2 (σ b) = r.s 2 (σ b) * r.s 1 a *
      r.l 2 (e.trace (σ (σ a) * b)) := by
  rw [reverse_commutator_exchange, d.upper, root_inv, trace_shift]

private theorem mixed_exchange (a : F) (b : K) :
    r.s 0 a * r.l 0 b = r.l 0 b * r.s 0 a * r.s 1 (a*b.val) *
      r.s 2 (σ (a*σ a*b.val)) * r.l 1 (e.norm a * b) := by
  have hb : σ b.val = b.val := b.property
  have hshift : σ a * σ (σ a) * b.val = σ (a * σ a * b.val) := by
    simp only [map_mul, hb]
  have hCD := d.upper_exchange (a*b.val) (a*σ a*b.val)
  rw [trace_mixed_correction e] at hCD
  have hDC : r.s 2 (σ (a*σ a*b.val)) * r.s 1 (a*b.val) =
      r.s 1 (a*b.val) * r.s 2 (σ (a*σ a*b.val)) * r.l 2 (e.norm a*b^2) := by
    rw [hCD]
    simp only [mul_assoc, l, root_square, mul_one]
  rw [reverse_commutator_exchange, d.mixed, d.coefficient, hshift]
  simp only [mul_inv_rev, root_inv]
  have hEF := d.long1_long2 (e.norm a*b) (e.norm a*b^2)
  have hCE := d.short1_long1 (a*b.val) (e.norm a*b)
  have hCF := d.short1_long2 (a*b.val) (e.norm a*b^2)
  have hDE := d.short2_long1 (σ (a*σ a*b.val)) (e.norm a*b)
  have hDF := d.short2_long2 (σ (a*σ a*b.val)) (e.norm a*b^2)
  calc
    _ = r.l 0 b * r.s 0 a *
        ((r.s 2 (σ (a*σ a*b.val)) * r.s 1 (a*b.val)) *
          (r.l 1 (e.norm a*b) * r.l 2 (e.norm a*b^2))) := by
      congr 1
      calc
        _ = (r.l 1 (e.norm a*b) * r.l 2 (e.norm a*b^2)) *
            (r.s 2 (σ (a*σ a*b.val)) * r.s 1 (a*b.val)) := by rw [hEF.eq]; group
        _ = _ := ((hDE.mul_right hDF).mul_left (hCE.mul_right hCF)).eq.symm
    _ = _ := by
      rw [hDC]
      simp only [mul_assoc]
      rw [← mul_assoc (r.l 2 (e.norm a*b^2)) (r.l 1 (e.norm a*b)) _, ← hEF.eq]
      simp only [mul_assoc, l, root_square, mul_one]

/-- The original right-commutator equations give the published fifteen ordered
exchanges after normalizing g and shifting the third short orbit. -/
theorem relations : e.SourceRelations r.markedShort r.long where
  short0_long1 := d.short0_long1
  short0_long2 := d.short0_long2
  long0_short1 := d.long0_short1
  long0_short2 a b := d.long0_short2 a (σ b)
  long0_long2 := d.long0_long2
  short1_long1 := d.short1_long1
  short1_long2 := d.short1_long2
  short2_long1 a b := d.short2_long1 (σ a) b
  short2_long2 a b := d.short2_long2 (σ a) b
  long1_long2 := d.long1_long2
  short0_long0 := d.mixed_exchange
  short1_short2 := d.upper_exchange
  short0_short2 a b := by
    change r.s 0 a * r.s 2 (σ b) = _
    rw [reverse_commutator_exchange, d.lower, root_inv, trace_shift]
    rfl
  long0_long1 a b := by
    change r.l 0 a * r.l 1 b = _
    rw [reverse_commutator_exchange, d.long_long, root_inv]
  short0_short1 a b := by
    change r.s 0 a * r.s 1 b = r.s 1 b * r.s 0 a *
      r.s 2 (σ (a * σ b + σ a * b)) * r.l 1 (e.trace (a * σ a * σ (σ b))) *
        r.l 2 (e.trace (a * σ b * σ (σ b)))
    rw [reverse_commutator_exchange, d.short_short, trace_short_short]
    have hshift : σ a * σ (σ b) + σ (σ a) * σ b = σ (a * σ b + σ a * b) := by
      simp only [map_add, map_mul]
    rw [hshift]
    simp only [mul_inv_rev, root_inv]
    have hDE := d.short2_long1 (σ (a * σ b + σ a * b)) (e.trace (a * σ a * σ (σ b)))
    have hDF := d.short2_long2 (σ (a * σ b + σ a * b)) (e.trace (a * σ b * σ (σ b)))
    have hEF := d.long1_long2 (e.trace (a * σ a * σ (σ b))) (e.trace (a * σ b * σ (σ b)))
    calc
      _ = r.s 1 b * r.s 0 a *
          ((r.l 1 (e.trace (a * σ a * σ (σ b))) * r.l 2 (e.trace (a * σ b * σ (σ b)))) *
            r.s 2 (σ (a * σ b + σ a * b))) := by rw [hEF.eq]; group
      _ = _ := by rw [← (hDE.mul_right hDF).eq]; simp only [mul_assoc]

end CoefficientStage
end RawRoots
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
