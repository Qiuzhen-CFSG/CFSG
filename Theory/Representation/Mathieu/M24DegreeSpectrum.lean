module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.Inputs
public import Theory.Representation.EndFieldDegree
public import Theory.Representation.EndFieldFrobenius

/-!
# Descent of the M₂₄ absolute degree spectrum to the binary field

For a binary irreducible module, enlarge scalars inside its commuting
endomorphism algebra. The resulting faithful representation is absolutely
irreducible, and its degree multiplies by the actual Schur-field degree.
The absolute spectrum alone leaves binary dimensions 11, 22, 33 and 44.
Frobenius-fixed degree-eleven traces exclude the extra field degrees;
absolute degree 44 needs only the original dimension bound 48.

The two concrete calculations in `Inputs` remain explicit hypotheses.
This module proves their descent, not the unconditional spectrum.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17.
-/

public section
open scoped MonoidAlgebra
namespace Representation.Mathieu.M24DegreeSpectrum
open Sporadic.Mathieu
universe v

section Binary
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) M24 V) [σ.IsIrreducible]

/-- The absolute window alone retains all possible Schur-field multiples. -/
theorem finrank_cases_of_absolute_spectrum
    (hdegree : AbsoluteSmallSpectrum.{v}) (hf : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) V ≤ 48) :
    Module.finrank (ZMod 2) V = 11 ∨ Module.finrank (ZMod 2) V = 22 ∨
      Module.finrank (ZMod 2) V = 33 ∨ Module.finrank (ZMod 2) V = 44 := by
  let E := Module.End (ZMod 2)[M24] σ.asModule
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  have ha := hdegree E σ.asModule σ.endFieldRep
    ((endFieldRep_injective_iff σ).mpr hf) (endFieldRep_isAbsolutelyIrreducible σ)
    ((endField_finrank_le σ).trans hd)
  have hm := finrank_eq_endField_mul σ
  have hp := schurDegree_pos 2 σ
  change 0 < Module.finrank (ZMod 2) E at hp
  rcases ha with ha | ha <;> rw [ha] at hm <;> dsimp only [E] at hp <;> omega

/-- The trace calculation identifies the actual Schur field with the binary field. -/
theorem finrank_eq_eleven_of_absolute_eleven
    (htrace : DegreeElevenTraceField.{v}) (hf : Function.Injective σ)
    (ha : Module.finrank (Module.End (ZMod 2)[M24] σ.asModule) σ.asModule = 11) :
    Module.finrank (ZMod 2) V = 11 := by
  let E := Module.End (ZMod 2)[M24] σ.asModule
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  have ht := htrace E σ.asModule σ.endFieldRep
    ((endFieldRep_injective_iff σ).mpr hf) (endFieldRep_isAbsolutelyIrreducible σ) ha
  have hdiv : schurDegree 2 σ ∣ 1 :=
    (endFieldRep_trace_frobenius_iff 2 σ 1).mp (by simpa using ht)
  have hE : Module.finrank (ZMod 2) E = 1 := Nat.dvd_one.mp hdiv
  rw [finrank_eq_endField_mul σ, hE, ha, one_mul]

/-- The dimension bound alone settles the absolute degree-forty-four branch. -/
theorem finrank_eq_forty_four_of_absolute_forty_four
    (ha : Module.finrank (Module.End (ZMod 2)[M24] σ.asModule) σ.asModule = 44)
    (hd : Module.finrank (ZMod 2) V ≤ 48) : Module.finrank (ZMod 2) V = 44 := by
  have hm := finrank_eq_endField_mul σ
  have hp := schurDegree_pos 2 σ
  change 0 < Module.finrank (ZMod 2) (Module.End (ZMod 2)[M24] σ.asModule) at hp
  rw [ha] at hm
  omega

/-- Both independent calculations give the exact binary spectrum on native M₂₄. -/
theorem finrank_cases_of_absolute_calculations
    (hdegree : AbsoluteSmallSpectrum.{v}) (htrace : DegreeElevenTraceField.{v})
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V ≤ 48) :
    Module.finrank (ZMod 2) V = 11 ∨ Module.finrank (ZMod 2) V = 44 := by
  let E := Module.End (ZMod 2)[M24] σ.asModule
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  have ha := hdegree E σ.asModule σ.endFieldRep
    ((endFieldRep_injective_iff σ).mpr hf) (endFieldRep_isAbsolutelyIrreducible σ)
    ((endField_finrank_le σ).trans hd)
  rcases ha with ha | ha
  · exact Or.inl (finrank_eq_eleven_of_absolute_eleven σ htrace hf ha)
  · exact Or.inr (finrank_eq_forty_four_of_absolute_forty_four σ ha hd)
end Binary

end Representation.Mathieu.M24DegreeSpectrum
