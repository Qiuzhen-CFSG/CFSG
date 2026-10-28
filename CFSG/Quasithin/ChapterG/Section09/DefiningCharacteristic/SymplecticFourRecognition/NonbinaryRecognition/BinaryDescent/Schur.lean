module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.BinaryDescent.Support
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent
public import Theory.SpecificGroups.SymplecticFour.DerivedInvolution
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Schur-field parameters for a faithful binary symplectic action

Extend the actual endomorphism-field action to its algebraic closure and
apply the explicit absolute tensor catalogue. The spanning-trace theorem
identifies the Schur degree with the Frobenius period. It divides n, and
catalogue uniqueness forces support repetition. The explicit derived
involution excludes empty support by faithfulness. The dimension tower
then gives s(4^a)^t with n = st and positive a,t.

The absolute catalogue is an explicit premise, as in GLS3, Corollary
2.8.6(a), Remark 2.8.8 and Examples 2.8.10(d). No recognition conclusion
or ambient automorphism-rank hypothesis is assumed.
-/

@[expose] public section

open Representation Representation.FrobeniusTensor
open scoped MonoidAlgebra TensorProduct
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
noncomputable section
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- The empty tensor support gives the trivial action. -/
theorem tensorModel_empty_apply {E : Type*} [Field E] {n : ℕ}
    (e : F →+* E) (g : Derived F) : tensorModel e (∅ : Finset (Fin (2*n))) g = 1 := by
  classical
  change (tensorMatrix e ∅ g).mulVecLin = 1
  have hm : tensorMatrix e (∅ : Finset (Fin (2*n))) g = 1 := by
    ext x y
    have hxy : x = y := Subsingleton.elim _ _
    subst y
    simp [tensorMatrix]
  rw [hm, Matrix.mulVecLin_one]
  rfl

/-- A faithful action of the literal derived group cannot have empty support. -/
theorem tensorSupport_nonempty {E : Type*} [Field E]
    {W : Type*} [AddCommGroup W] [Module E W]
    (σ : Representation E (Derived F) W) (hσ : Function.Injective σ)
    {n : ℕ} (e : F →+* E) (S : Finset (Fin (2*n)))
    (φ : σ.Equiv (tensorModel e S)) : S.Nonempty := by
  classical
  by_contra! h
  subst S
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨g, hg, _⟩ :=
    Theory.SpecificGroups.SymplecticFour.exists_involution_derived_of_char_two (F := F)
  apply hg
  apply hσ
  rw [map_one]
  ext v
  apply φ.toLinearEquiv.injective
  have hh := IntertwiningMap.isIntertwining σ (tensorModel e ∅) φ.toIntertwiningMap g v
  rw [tensorModel_empty_apply] at hh
  exact hh

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (Derived F) V) [ρ.IsIrreducible]

/-- Construct periodic tensor parameters over the actual Schur field. -/
theorem exists_schur_tensor_parameters {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hρ : Function.Injective ρ)
    (cat : ∀ e : F →+* Closure ρ, AbsoluteTensorCatalogue F (Closure ρ) e n) :
    ∃ (e : F →+* Closure ρ) (S : Finset (Fin (2*n))) (t a : ℕ),
      0 < t ∧ 0 < a ∧ n = Module.finrank (ZMod 2) (SchurField ρ) * t ∧
      S.card = a*t ∧
      Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (SchurField ρ) * (4^a)^t ∧
      Nonempty ((absoluteRep ρ).Equiv (tensorModel e S)) := by
  classical
  let : NeZero (2*n) := ⟨by omega⟩
  let : Algebra (ZMod 2) (Closure ρ) := ZMod.algebra _ _
  let : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  let e : F →+* Closure ρ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := Closure ρ)).toRingHom
  obtain ⟨S, ⟨φ⟩⟩ := (cat e).exhaustive (AbsoluteSpace ρ) (absoluteRep ρ) inferInstance
  let s := Module.finrank (ZMod 2) (SchurField ρ)
  have hχ (g : Derived F) : (absoluteRep ρ).character g = (tensorModel e S).character g :=
    congrFun (char_iso φ) g
  have hsn : s ∣ n := (character_pow_iff ρ n).mp (by
    intro g
    rw [hχ]
    exact tensorModel_character_field_fixed hF e S g)
  have hperiod : rotateSupport s S = S :=
    rotateSupport_eq_of_character_fixed hF e (cat e) s S (by
      intro g
      rw [← hχ]
      exact (character_pow_iff ρ s).mpr (dvd_refl s) g)
  obtain ⟨t, hnt⟩ := hsn
  have ht : 0 < t := by
    by_contra! hz
    have : t = 0 := Nat.eq_zero_of_le_zero hz
    simp only [this, mul_zero] at hnt
    omega
  obtain ⟨a, hcard⟩ := rotateSupport_card_multiple hnt S hperiod
  have ha : 0 < a := by
    have hpos := Finset.card_pos.mpr (tensorSupport_nonempty (absoluteRep ρ)
      (absoluteRep_injective ρ hρ) e S φ)
    rw [hcard] at hpos
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hpos)
  refine ⟨e, S, t, a, ht, ha, hnt, hcard, ?_, ⟨φ⟩⟩
  rw [binary_finrank_eq ρ, φ.toLinearEquiv.finrank_eq, tensorModel_finrank,
    hcard, pow_mul]

end
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
