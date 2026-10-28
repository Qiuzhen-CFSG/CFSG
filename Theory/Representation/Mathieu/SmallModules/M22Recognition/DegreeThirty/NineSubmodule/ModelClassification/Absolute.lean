module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.Models
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.ScalarTransport

/-!
# The two absolute words of binary degree nine

The SL₃(4) tensor catalogue and its exact Frobenius period force the commuting
field of a binary simple module of degree nine to have degree one. Its word
is natural–natural or dual–dual. Evaluation of scalar endomorphisms then
identifies the Schur extension with the extension of the original binary
module. No absolute irreducibility is imposed on that original module.

Source: GLS III, 2.8.6, 2.8.8 and 2.8.10(c). The concrete model comparison
for Aschbacher–Smith H.4.2–4, pp.380–381, is supplied separately.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation
open scoped MonoidAlgebra TensorProduct
open Representation.SL3.BinaryDefiningFactors
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.ModelClassification

/-- The two words retain the natural/dual distinction. -/
def modelWord : Bool → List Factor
  | false => [.natural, .natural]
  | true => [.dual, .dual]

private lemma nine_word (w : List Factor) (hlen : w.length = 2)
    (s : ℕ) (hd : 9 = s * wordDegree w)
    (hperiod : ∀ j, w.rotate j = w ↔ s ∣ j) :
    s = 1 ∧ ∃ b, w = modelWord b := by
  have hs : s = 1 ∨ s = 2 := (Nat.dvd_prime Nat.prime_two).mp
    ((hperiod 2).mp (hlen ▸ List.rotate_length w))
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  rcases hs with rfl | rfl
  · have hr := (hperiod 1).mpr (one_dvd 1)
    have hab : a = b := (by simpa using hr : b = a ∧ a = b).2
    subst b
    refine ⟨rfl, ?_⟩
    cases a
    · simp [wordDegree, Factor.dimension] at hd
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
    · simp [wordDegree, Factor.dimension] at hd
  · omega

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (σ : Representation (ZMod 2) Matrix.PSL3Four.SL W) [σ.IsIrreducible]

abbrev SchurField := Module.End (ZMod 2)[Matrix.PSL3Four.SL] σ.asModule
abbrev SplittingField := AlgebraicClosure (SchurField σ)

instance schurField_charTwo : CharP (SchurField σ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField σ)).injective 2

/-- Degree nine forces Schur degree one and the two constant tensor words. -/
theorem absolute_word (hd : Module.finrank (ZMod 2) W = 9) :
    Representation.schurDegree 2 σ = 1 ∧
      ∃ (ι : Matrix.PSL3Four.F →+* SplittingField σ) (b : Bool),
        Nonempty ((extendScalars (SplittingField σ) σ.endFieldRep).Equiv
          (wordRep ι (modelWord b))) := by
  let : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra _ 2
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars (SplittingField σ) σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep (SplittingField σ)
  let ι : Matrix.PSL3Four.F →+* SplittingField σ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := Matrix.PSL3Four.F)
      (M := SplittingField σ)).toRingHom
  have hcard : Nat.card Matrix.PSL3Four.F = 2 ^ 2 := by
    simpa using Matrix.PSL3Four.card_F
  obtain ⟨w, hw, ⟨e⟩⟩ := exists_word_equiv ι 2 hcard
    (extendScalars (SplittingField σ) σ.endFieldRep)
  have hp := word_rotate_iff_schurDegree_dvd σ ι w (hw ▸ hcard)
    (fun v hv => wordRep_isIrreducible ι 2 hcard v (hv.trans hw))
    (fun u v hu hv h =>
      (wordRep_equiv_iff ι 2 hcard u v (hu.trans hw) (hv.trans hw)).mp h) ⟨e⟩
  have hdim : 9 = Representation.schurDegree 2 σ * wordDegree w := by
    rw [← hd, Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ),
      e.toLinearEquiv.finrank_eq, finrank_wordSpace]
  obtain ⟨hs, b, rfl⟩ := nine_word w hw _ hdim hp
  exact ⟨hs, ι, b, ⟨e⟩⟩

private def schurOneEquiv (hs : Representation.schurDegree 2 σ = 1) :
    (extendScalars (SchurField σ) σ).Equiv σ.endFieldRep := by
  let E := SchurField σ
  let : Finite σ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) σ.asModule)
  let : Module.Finite E σ.asModule := Module.Finite.of_finite
  let L := LinearMap.liftBaseChange E σ.asModuleEquiv.symm.toLinearMap
  have hsurj : Function.Surjective L := by
    intro v
    exact ⟨1 ⊗ₜ[ZMod 2] σ.asModuleEquiv v, by simp [L]⟩
  have hdim : Module.finrank E (E ⊗[ZMod 2] W) = Module.finrank E σ.asModule := by
    rw [Module.finrank_baseChange]
    have ht := Module.finrank_mul_finrank (ZMod 2) E σ.asModule
    change Module.finrank (ZMod 2) E = 1 at hs
    rw [hs, one_mul] at ht
    exact σ.asModuleEquiv.finrank_eq.symm.trans ht.symm
  refine .mk (LinearEquiv.ofBijective L
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩) ?_
  intro g
  apply LinearMap.ext
  intro z
  change L ((extendScalars E σ) g z) = σ.endFieldRep g (L z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a v =>
    simp [L, extendScalars_apply, LinearMap.baseChange_tmul, endFieldRep_apply]

/-- The word equivalence is an extension of the original binary action,
not just of an action on its Schur carrier. -/
theorem original_absolute_word (hd : Module.finrank (ZMod 2) W = 9) :
    letI : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra _ 2
    ∃ (ι : Matrix.PSL3Four.F →+* SplittingField σ) (b : Bool),
      Nonempty ((extendScalars (SplittingField σ) σ).Equiv
        (wordRep ι (modelWord b))) := by
  let : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra _ 2
  obtain ⟨hs, ι, b, ⟨e⟩⟩ := absolute_word σ hd
  let t := Representation.SL2.BinarySmall.scalarTowerRepEquiv
    (S := SchurField σ) (F := SplittingField σ) σ
  exact ⟨ι, b, ⟨t.symm.trans ((BinaryFieldDescent.extendEquiv
    (K := SplittingField σ) (schurOneEquiv σ hs)).trans e)⟩⟩

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.ModelClassification
