module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.RootRecovery.RankOneInputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.RootRecovery.FiniteExponents
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.RootRecovery.SL2Separation.RationalEndpoint

/-!
# Recovering rational SL2 highest exponents from a finite intertwiner

A finite diagonal comparison separates the restricted exponents except at zero
and `|F|-1`. The rational endpoint theorem detects zero by fixation under the
actual Weyl matrix, which belongs to SL2 over every subfield. Both tests are
preserved by the supplied linear intertwiner. Thus the highest exponents agree,
without any irreducibility assumption on the rational representations.

This proves the independent rank-one contract used in GLS3 2.8.2 / Steinberg
§13.3(a), `refs/KGroup/GLS3/Chapter2St2.tex`. It makes no assertion about the
separate D4 finite root charts.
-/

open Theory.AlgebraicGroup
open scoped MatrixGroups
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private def finiteWeyl (F : Subfield k) : SL(2, F) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

private theorem finiteSL2Inclusion_weyl (F : Subfield k) :
    finiteSL2Inclusion F (finiteWeyl F) = SL2FiniteRecovery.weylPoint := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change F.subtype.mapMatrix !![(0 : F), -1; 1, 0] = !![(0 : k), -1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private def finiteDiagonal (F : Subfield k) (a : Fˣ) : SL(2, F) :=
  ⟨!![(a : F), 0; 0, (a⁻¹ : Fˣ)], by simp [Matrix.det_fin_two_of]⟩

private noncomputable def finiteTorusPoint (F : Subfield k) (a : Fˣ) :
    Variety.Point (KMult k) :=
  (dPointEquiv 1).symm (fun _ => Units.map F.subtype.toMonoidHom a)

private theorem finiteSL2Inclusion_diagonal (F : Subfield k) (a : Fˣ) :
    finiteSL2Inclusion F (finiteDiagonal F a) =
      standardSL2DiagonalMorphism.onPoints (finiteTorusPoint F a) := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change F.subtype.mapMatrix !![(a : F), 0; 0, (a⁻¹ : Fˣ)] =
    typeASLDiagonalMatrix 1 (finiteTorusPoint F a)
  rw [typeASLDiagonalMatrix, Matrix.diagonal_fin_two]
  have h0 : typeASLDiagonalEntries 1 (finiteTorusPoint F a) 0 =
      Units.map F.subtype.toMonoidHom a := by
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
      typeASLDiagonalEntries_castSucc]
    simp [finiteTorusPoint]
  have h1 : typeASLDiagonalEntries 1 (finiteTorusPoint F a) 1 =
      (Units.map F.subtype.toMonoidHom a)⁻¹ := by
    rw [show (1 : Fin 2) = Fin.last 1 from rfl, typeASLDiagonalEntries_last]
    simp [finiteTorusPoint]
  rw [h0, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Restricted rational highest exponents are recovered from an actual
finite SL2 intertwiner carrying the chosen highest vectors to each other. -/
public theorem finiteSL2HighestVectorRecovery [CharP k 2] :
    FiniteSL2HighestVectorRecovery (k := k) := by
  intro F _ V _ _ _ W _ _ _ rho tau hrho htau m l hm hmF hl hlF
    v w hv hw hUv hUw hDv hDw e he hinter
  have hfix : (rho.action SL2FiniteRecovery.weylPoint).1 v = v ↔
      (tau.action SL2FiniteRecovery.weylPoint).1 w = w := by
    have h := hinter (finiteWeyl F) v
    rw [finiteSL2Inclusion_weyl, he] at h
    constructor
    · intro hvf
      rw [hvf, he] at h
      exact h.symm
    · intro hwf
      apply e.injective
      rw [h, hwf, he]
  have hzero : m = 0 ↔ l = 0 :=
    (SL2FiniteRecovery.weyl_fixed_iff_exponent_zero rho hrho v m hv hUv hDv).symm.trans
      (hfix.trans (SL2FiniteRecovery.weyl_fixed_iff_exponent_zero tau htau w l hw hUw hDw))
  have hpowers (a : Fˣ) : a ^ m.toNat = a ^ l.toNat := by
    have h := hinter (finiteDiagonal F a) v
    rw [finiteSL2Inclusion_diagonal, hDv, he, hDw, e.map_smul] at h
    have hs : (((a : F) : k) ^ m) = (((a : F) : k) ^ l) := by
      apply (smul_left_injective k hw)
      simpa [finiteTorusPoint, he] using h
    rw [← Int.toNat_of_nonneg hm, ← Int.toNat_of_nonneg hl] at hs
    simp only [zpow_natCast] at hs
    apply Units.ext
    apply Subtype.val_injective
    simpa using hs
  have heq := restricted_nat_exponents_eq
    (F := F) (m := m.toNat) (l := l.toNat)
    (by omega) (by omega) (by omega) hpowers
  omega

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
