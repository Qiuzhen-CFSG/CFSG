module
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneTransport
import Mathlib.Tactic.FinCases

/-!
# Changes of natural plane coordinates compatible with a four-group

Linear coordinate changes and coefficient Frobenius preserve the literal
GL₂(4) action, provided its group marking changes with them. A nonidentity
linear actor fixing a prescribed nonzero vector fixes only the field line
through that vector. On a normalized field line, its two remaining nonzero
vectors differ by a coefficient automorphism.

These facts align the common root center in the two actual plane normalizers
of a J₃-type group. The application is in `J3Recognition/Ambient/Overlap`.
Source: Aschbacher, *Sporadic Groups* (1994), 46.14, pp.257–258;
Aschbacher–Smith I.4.7(2), p.418. No ambient recognition is asserted.
-/

@[expose] public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.PlaneCoordinates
open Representation.CentralCubicNaturalFour
open Representation.SL2FourNatural (F V)
open Representation.SL2FourNatural.SemilinearNormalizer (coefficient)

/-- The common coordinate line, with its original additive parameter. -/
def axis : Multiplicative F →* Plane where
  toFun c := Multiplicative.ofAdd ![c.toAdd, 0]
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> rfl
  map_mul' c d := by
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> simp

theorem axis_injective : Function.Injective axis := by
  intro c d h
  exact congrArg (fun v : Plane => Multiplicative.ofAdd (v.toAdd 0)) h

def coefficientPlane (σ : F ≃+* F) : MulAut Plane :=
  (coefficient σ).toAddEquiv.toMultiplicative

theorem coefficientPlane_axis (σ : F ≃+* F) (c : Multiplicative F) :
    coefficientPlane σ (axis c) = axis (Multiplicative.ofAdd (σ c.toAdd)) := by
  change (fun i => σ (![c.toAdd, 0] i)) = ![σ c.toAdd, 0]
  funext i
  fin_cases i <;> simp

theorem linear_change_action (t g : LinearGroup) (v : Plane) :
    naturalAction (MulAut.conj t g) (naturalAction t v) =
      naturalAction t (naturalAction g v) := by
  change naturalAction (t * g * t⁻¹) (naturalAction t v) = _
  simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply,
    MulEquiv.symm_apply_apply]

theorem coefficient_change_action (σ : F ≃+* F) (g : LinearGroup) (v : Plane) :
    naturalAction (Matrix.GeneralLinearGroup.coefficientEquiv σ g) (coefficientPlane σ v) =
      coefficientPlane σ (naturalAction g v) := by
  apply congrArg Multiplicative.ofAdd
  funext i
  change ((g.val.map σ).mulVec (fun j => σ (v.toAdd j))) i = σ (g.val.mulVec v.toAdd i)
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem normalize_nonidentity (v : Plane) (hv : v ≠ 1) :
    ∃ t : LinearGroup, naturalAction t v = axis (Multiplicative.ofAdd 1) := by
  have hv0 : v.toAdd ≠ 0 := hv
  have h10 : (![1, 0] : V) ≠ 0 := by
    intro h
    have hh := congrFun h 0
    exact one_ne_zero hh
  obtain ⟨t,ht⟩ := Representation.SL2FourNatural.transitive_nonzero v.toAdd ![1,0] hv0 h10
  exact ⟨Matrix.SpecialLinearGroup.toGL t, congrArg Multiplicative.ofAdd ht⟩

/-- A nonidentity linear map fixing the first basis vector fixes only its line. -/
theorem fixed_axis (g : LinearGroup) (hg : g ≠ 1)
    (h1 : naturalAction g (axis (Multiplicative.ofAdd 1)) = axis (Multiplicative.ofAdd 1))
    (v : Plane) (hv : naturalAction g v = v) : v.toAdd 1 = 0 := by
  by_contra hn
  have h00 : g.val 0 0 = 1 := by
    have hh := congrArg (fun w : Plane => w.toAdd 0) h1
    simpa [naturalAction_apply, axis, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hh
  have h10 : g.val 1 0 = 0 := by
    have hh := congrArg (fun w : Plane => w.toAdd 1) h1
    simpa [naturalAction_apply, axis, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hh
  have h01 : g.val 0 1 = 0 := by
    have hh := congrArg (fun w : Plane => w.toAdd 0) hv
    have hz : g.val 0 1 * v.toAdd 1 = 0 := by
      simpa [naturalAction_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00] using hh
    exact (mul_eq_zero.mp hz).resolve_right hn
  have h11 : g.val 1 1 = 1 := by
    apply mul_right_cancel₀ hn
    have hh := congrArg (fun w : Plane => w.toAdd 1) hv
    simpa [naturalAction_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10] using hh
  apply hg
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h00,h01,h10,h11]

/-- The two possible nonbinary parameters on a normalized four-group differ by Frobenius. -/
theorem align_nonbinary (c d : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1) : ∃ σ : F ≃+* F, σ c = d := by
  have hh : ∀ c d : F, c ≠ 0 → c ≠ 1 → d ≠ 0 → d ≠ 1 →
      ∃ b : Bool, (if b then Representation.SL2FourNatural.fieldFrobenius else 1) c = d := by
    decide +kernel
  obtain ⟨b,hb⟩ := hh c d hc0 hc1 hd0 hd1
  exact ⟨if b then Representation.SL2FourNatural.fieldFrobenius else 1,hb⟩


/-- The additive base field inside the sixteen-element translation root. -/
def baseRoot : Multiplicative F →* SingerField.Model :=
  SingerField.root.comp (algebraMap F SingerField.K).toAddMonoidHom.toMultiplicative

theorem rootCoordinates_base (c : Multiplicative F) :
    SingerField.rootCoordinates
      (Multiplicative.ofAdd (algebraMap F SingerField.K c.toAdd)) = axis c := rfl

end Sporadic.Janko3.SourceRecognition.PlaneCoordinates
