module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortOrbit
import all Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortOrbit

/-!
# The singular cone in the short-root three-space

The fixed-field pair parametrization identifies the long-root orbit
with the nonzero singular symmetric Hermitian matrices. Frobenius
injectivity recovers the off-diagonal coordinate from the diagonal
square roots. This characterizes the orbit used in the full-stabilizer
argument of Aschbacher–Smith F.4.42, printed pp.295–296.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "C" => shortCentralizer F σ hσ

/-- Inside the orthogonal three-space the long-root orbit is exactly the
nonzero singular cone, with the original unipotent parameters retained. -/
theorem longClass_iff_singular (X : hermitianMatrices F σ)
    (hX : X ∈ fixedHermitian F σ) :
    IsConj (longMark F σ hσ)
      (radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd X)) ↔
      X ≠ 0 ∧ X.val.det = 0 := by
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := isConj_iff.mp hx
    obtain ⟨v,hv,he⟩ := conjugate_long F σ hσ a
    have hpar : X = symmetric F σ (v.1^2) (v.1*v.2) (v.2^2) := by
      apply Multiplicative.ofAdd.injective
      exact radicalHom_injective F σ hσ
        (congrArg (fun x : C => x.val) (ha.symm.trans he))
    refine ⟨?_,?_⟩
    · intro hz
      have hone : a * longMark F σ hσ * a⁻¹ = 1 := by
        rw [ha,hz]
        exact map_one _
      have hz1 : longMark F σ hσ = 1 :=
        (MulAut.conj a).injective (hone.trans (map_one _).symm)
      have ho := longMark_order F σ hσ
      rw [hz1,orderOf_one] at ho
      contradiction
    · rw [hpar]
      simp [symmetric,fixedHermitianEquiv,Matrix.det_fin_two]
      ring
  · rintro ⟨hzero,hdet⟩
    let p := fixedHermitianEquiv F σ ⟨X,hX⟩
    have hp : X = symmetric F σ p.1 p.2.1 p.2.2 :=
      (congrArg Subtype.val ((fixedHermitianEquiv F σ).symm_apply_apply ⟨X,hX⟩)).symm
    obtain ⟨r,hr⟩ := (frobeniusEquiv K 2).surjective p.1
    obtain ⟨s,hs⟩ := (frobeniusEquiv K 2).surjective p.2.2
    have hr2 : r^2 = p.1 := hr
    have hs2 : s^2 = p.2.2 := hs
    have hb : p.2.1 = r*s := by
      apply (frobeniusEquiv K 2).injective
      apply Subtype.ext
      have hd : (p.1 : F) * p.2.2 - p.2.1 * p.2.1 = 0 := by
        simpa [hp,symmetric,fixedHermitianEquiv,Matrix.det_fin_two] using hdet
      change (p.2.1 : F)^2 = ((r : F) * s)^2
      have hr' := congrArg (fun a : K => (a : F)) hr2
      have hs' := congrArg (fun a : K => (a : F)) hs2
      change (r : F)^2 = p.1 at hr'
      change (s : F)^2 = p.2.2 at hs'
      rw [mul_pow,hr',hs',pow_two]
      exact (sub_eq_zero.mp hd).symm
    have hv : (r,s) ≠ (0 : K × K) := by
      intro he
      have hr0 : r = 0 := congrArg Prod.fst he
      have hs0 : s = 0 := congrArg Prod.snd he
      apply hzero
      rw [hp,←hr2,←hs2,hb,hr0,hs0]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [symmetric,fixedHermitianEquiv]
    have hx : radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd X) =
        rootPair F σ hσ (r,s) := by
      rw [hp,←hr2,←hs2,hb]
      rfl
    rw [hx]
    exact rootPair_conjugate F σ hσ (r,s) hv
end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
