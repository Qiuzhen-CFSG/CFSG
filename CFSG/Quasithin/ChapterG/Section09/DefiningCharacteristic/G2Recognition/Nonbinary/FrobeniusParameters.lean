module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.TensorDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Unconditional nonbinary G₂ Frobenius parameters

Extend the given irreducible binary representation over its actual Schur
endomorphism field to an algebraic closure. The concrete G₂ tensor
classification supplies a unique word in the four proved restricted factors.
The Frobenius-period theorem and scalar-dimension tower yield positive
parameters `s,t`, a basic-degree block of length `s`, and binary dimension
`s * l.prod ^ t`, with `n = s*t`. Here `s` is the actual Schur degree.

The same witnesses carry natural recognition when `t = 1` and `l.prod = 6`:
the full tensor then has one natural factor, and the genuine intertwiner
descends along the compatible Schur/defining-field identification. No degree
bound or unproved classification premise is imposed. The parent owns the
small-degree arithmetic exclusion and the original actor's rank bounds.

Source: GLS3, 2.8.6, Remark 2.8.8 and 2.8.10(g); Aschbacher--Smith,
G.9.3(10), printed pp.354,356--357.
-/

open scoped MonoidAlgebra
public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
open Atlas.G2 Atlas.G2.TensorClassification
attribute [local instance] ZMod.algebra

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (Atlas.G2.Model F) V) [Representation.IsIrreducible ρ]

/-- The complete basic-degree parameters of a faithful irreducible binary
G₂ representation. The block length is the actual Schur-field degree, and the
single-natural block gives quasiequivalence to the octonion quotient action.
There is no small-degree premise. -/
theorem exists_basic_parameters_and_natural {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hρ : Function.Injective ρ) :
    let s := Representation.schurDegree 2 ρ
    0 < s ∧ ∃ (t : ℕ) (l : List ℕ), 0 < t ∧ l.length = s ∧ n = s * t ∧
      Module.finrank (ZMod 2) V = s * l.prod ^ t ∧ l.prod ≠ 1 ∧
      (∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64) ∧
      (t = 1 → l.prod = 6 → Quasiequivalent ρ (naturalBinary F)) := by
  let E := Module.End (ZMod 2)[Model F] ρ.asModule
  let Ω := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap E Ω).injective 2
  let : Algebra (ZMod 2) Ω := ZMod.algebra Ω 2
  let ι : F →+* Ω := (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := Ω)).toRingHom
  let : Algebra F Ω := ι.toAlgebra
  let : Representation.IsAbsolutelyIrreducible ρ.endFieldRep :=
    Representation.endFieldRep_isAbsolutelyIrreducible ρ
  let : Representation.IsIrreducible (Representation.extendScalars Ω ρ.endFieldRep) :=
    Representation.IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep Ω
  obtain ⟨w, ⟨e⟩⟩ := exists_tensorRep_equiv hF
    (Representation.extendScalars Ω ρ.endFieldRep) inferInstance
  obtain ⟨hs, t, l, ht, hlen, hnt, hd, hne, hbasic⟩ :=
    parameters_of_tensor_equiv ρ Ω (by omega) hF w e hρ
  refine ⟨hs, t, l, ht, hlen, hnt, hd, hne, hbasic, ?_⟩
  intro ht1 hb6
  have hsn : Representation.schurDegree 2 ρ = n := by simpa [ht1] using hnt.symm
  apply natural_of_schur_tensor ρ Ω hF hsn w e
  have hdim := Representation.finrank_eq_schurDegree_mul 2 ρ Ω
  rw [e.toLinearEquiv.finrank_eq, finrank_tensorSpace] at hdim
  rw [ht1, pow_one, hb6] at hd
  exact Nat.eq_of_mul_eq_mul_left hs (hdim.symm.trans hd)

/-- The unconditional degree formula, with the block length identified with
the original representation's endomorphism-field degree. -/
theorem exists_basic_parameters {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hρ : Function.Injective ρ) :
    let s := Representation.schurDegree 2 ρ
    0 < s ∧ ∃ (t : ℕ) (l : List ℕ), 0 < t ∧ l.length = s ∧ n = s * t ∧
      Module.finrank (ZMod 2) V = s * l.prod ^ t ∧ l.prod ≠ 1 ∧
        ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64 := by
  obtain ⟨hs, t, l, ht, hlen, hnt, hd, hne, hb, _⟩ :=
    exists_basic_parameters_and_natural ρ hn hF hρ
  exact ⟨hs, t, l, ht, hlen, hnt, hd, hne, hb⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
