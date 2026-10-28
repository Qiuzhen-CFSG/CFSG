module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Inverse similarity obstructs a natural SL₄(2) action

Every permutation is conjugate to its inverse. Thus every restriction of a
symmetric-group representation acts by operators similar to their inverses.
This property is preserved by the actual group and linear equivalences used
in the B.5.1 module alternatives.

An explicit element of SL₄(2) satisfies A⁴ + A³ + A² + I = 0 on its natural
module, while its inverse does not. The same identity, coordinate by
coordinate, excludes every positive number of repeated natural summands.
Only two four-by-four matrices are checked; no group enumeration is used.

This is the extension obstruction used in the middle-node branch of
Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.49,
printed p.1145, after the B.5.1 alternatives on pp.99–103.
-/

@[expose] public section

open Matrix Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.PointGeometry

section General
variable {D E K V W : Type*} [Group D] [Group E] [Group K]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- Every actor acts by an operator similar to its inverse. -/
def InverseSimilar (ρ : Representation (ZMod 2) D V) : Prop :=
  ∀ g, ∃ e : V ≃ₗ[ZMod 2] V, ∀ v, e (ρ g v) = ρ g⁻¹ (e v)

/-- An actual equivalence of actions preserves inverse similarity. -/
theorem inverseSimilar_transport {ρ : Representation (ZMod 2) D V}
    {σ : Representation (ZMod 2) E W} (f : ActionEquiv ρ σ)
    (h : InverseSimilar ρ) : InverseSimilar σ := by
  intro g
  obtain ⟨a, rfl⟩ := f.groupEquiv.surjective g
  obtain ⟨e, he⟩ := h a
  have hf (a : D) (w : W) : f.linearEquiv.symm (σ (f.groupEquiv a) w) =
      ρ a (f.linearEquiv.symm w) := by
    apply f.linearEquiv.injective
    simp only [f.intertwines, f.linearEquiv.apply_symm_apply]
  refine ⟨f.linearEquiv.symm.trans (e.trans f.linearEquiv), ?_⟩
  intro w
  dsimp only [LinearEquiv.trans_apply]
  rw [hf, he, f.intertwines, map_inv]

/-- Restriction from a group in which every element is conjugate to its
inverse makes every representing operator similar to its inverse. -/
theorem inverseSimilar_of_extension (τ : Representation (ZMod 2) K V)
    (f : D →* K) (h : ∀ k : K, IsConj k k⁻¹) : InverseSimilar (τ.comp f) := by
  intro g
  obtain ⟨t, ht⟩ := isConj_iff.mp (h (f g))
  refine ⟨LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom t), ?_⟩
  intro v
  change τ t (τ (f g) v) = τ (f g⁻¹) (τ t v)
  rw [map_inv]
  have ht' : t * f g = (f g)⁻¹ * t := by
    have hh := congrArg (fun k => k * t) ht
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  change (τ t * τ (f g)) v = (τ (f g)⁻¹ * τ t) v
  rw [← map_mul, ← map_mul, ht']

/-- A symmetric-group extension supplies inverse similarity on every
restricted representation, independently of the chosen actor coordinates. -/
theorem inverseSimilar_of_symmetric_extension (τ : Representation (ZMod 2) K V)
    (f : D →* K) {n : ℕ} (e : K ≃* Equiv.Perm (Fin n)) : InverseSimilar (τ.comp f) := by
  apply inverseSimilar_of_extension τ f
  intro g
  have h : IsConj (e g) (e g)⁻¹ :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (Equiv.Perm.cycleType_inv _).symm
  have hh := e.symm.toMonoidHom.map_isConj h
  change IsConj (e.symm (e g)) (e.symm ((e g)⁻¹)) at hh
  simpa only [map_inv, e.symm_apply_apply] using hh


end General

private abbrev W := Fin 4 → ZMod 2
private abbrev natural : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) W :=
  linearNatural BinaryField.two 4
/-- A fixed line plus the companion of X³ + X + 1. -/
private def a : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1,0,0,0; 0,0,0,1; 0,1,0,1; 0,0,1,0], by decide⟩
private def b : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1,0,0,0; 0,1,1,0; 0,0,0,1; 0,1,0,0], by decide⟩
private theorem ainv : a⁻¹ = b := by
  apply inv_eq_of_mul_eq_one_left
  exact Subtype.ext (by decide)
private theorem act_a (v : W) :
    natural a v = ![v 0, v 3, v 1 + v 3, v 2] := by
  change Matrix.mulVec a.val v = _
  ext i
  fin_cases i <;> simp [a, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
private theorem act_b (v : W) :
    natural b v = ![v 0, v 1 + v 2, v 3, v 1] := by
  change Matrix.mulVec b.val v = _
  ext i
  fin_cases i <;> simp [b, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
/-- The polynomial (X + 1)(X³ + X + 1) annihilates the natural action. -/
private theorem ann (v : W) :
    natural (a^4) v +
      natural (a^3) v +
      natural (a^2) v + v = 0 := by
  rw [map_pow, map_pow, map_pow]
  simp only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply, act_a]
  ext i
  fin_cases i <;> simp <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl,
      mul_zero, zero_add]

private theorem intertwines_pow {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {D : Type*} [Group D] (ρ : Representation (ZMod 2) D U)
    (g h : D) (e : U ≃ₗ[ZMod 2] U)
    (he : ∀ v, e (ρ g v) = ρ h (e v)) (n : ℕ) (v : U) :
    e (ρ (g^n) v) = ρ (h^n) (e v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', map_mul, Module.End.mul_apply, he, ih]

private theorem repeated_obstruction {ι : Type*} [Nonempty ι]
    (e : (ι → W) ≃ₗ[ZMod 2] (ι → W))
    (he : ∀ v, e (fun i => natural a (v i)) = fun i => natural a⁻¹ (e v i)) : False := by
  let ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (ι → W) :=
    { toFun g := LinearMap.pi (fun i => (natural g).comp (LinearMap.proj i))
      map_one' := by ext v i; simp
      map_mul' g h := by ext v i; simp [Module.End.mul_apply] }
  have hp (n : ℕ) (v : ι → W) := intertwines_pow ρ a a⁻¹ e he n v
  let v : ι → W := e.symm (fun _ => ![0,1,0,0])
  have hz : ρ (a^4) v + ρ (a^3) v + ρ (a^2) v + v = 0 := by
    funext i
    exact ann (v i)
  have hh := congrArg e hz
  simp only [map_add, map_zero, hp] at hh
  have hv : e v = fun _ => (![0,1,0,0] : W) := e.apply_symm_apply _
  rw [hv] at hh
  have hc := congrArg (fun w : ι → W => w (Classical.choice inferInstance) 1) hh
  change (natural ((a⁻¹)^4) ![0,1,0,0] + natural ((a⁻¹)^3) ![0,1,0,0] +
    natural ((a⁻¹)^2) ![0,1,0,0] + (![0,1,0,0] : W)) 1 = 0 at hc
  rw [ainv, map_pow, map_pow, map_pow] at hc
  simp only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply, act_b] at hc
  exact (by decide : (1 : ZMod 2) ≠ 0) hc

/-- The binary four-dimensional natural action is not similar to its inverse
on every group element. -/
theorem natural_not_inverseSimilar :
    ¬ InverseSimilar (linearNatural BinaryField.two 4) := by
  intro h
  obtain ⟨e, he⟩ := h a
  apply repeated_obstruction (ι := Unit) (LinearEquiv.piCongrRight (fun _ => e))
  intro v
  funext i
  exact he (v i)

/-- No positive number of identical binary natural summands admits inverse
similarity on every group element. There is no multiplicity upper bound. -/
theorem repeated_not_inverseSimilar (k : ℕ) (hk : 0 < k) :
    ¬ InverseSimilar (repeated (linearNatural BinaryField.two 4) k) := by
  intro h
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨e, he⟩ := h a
  exact repeated_obstruction e he


end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.PointGeometry
