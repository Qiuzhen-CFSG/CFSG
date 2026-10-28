module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.FieldDescent.Models
public import Theory.Representation.EndFieldFrobenius
public import Theory.Representation.SL3.BinaryFieldDescent
public import Theory.Representation.SL3.BinaryFieldDescent.Fields

/-!
# Descent of the absolute SL₃ models

The absolute natural model descends to the actual natural or dual-natural
binary action. The absolute half-field tensor model supplies a scalar action
on the original carrier V over the actual Frobenius fixed subfield, with
exact binary restriction and the required equivalence after extension to F.
Its binary dimension is nine times the Schur degree.

The Schur-field embedding is chosen compatibly with the arbitrary matrix-field
embedding in the absolute predicate. Functorial base-change comparisons and
descent of representation equivalences then retain the coefficient twist.
The absolute-model hypotheses are conditional inputs, not a classification
theorem proved here.

Source: GLS III, Remark 2.8.8 and Example 2.8.10(c); Aschbacher--Smith,
G.9.3(8),(17), printed pp.354,356--357.
-/

@[expose] public section

open Representation
open scoped MatrixGroups TensorProduct MonoidAlgebra

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]

/-- The absolute natural alternative has binary dimension three times the Schur degree. -/
theorem binary_finrank_of_absolute_natural (h : HasAbsoluteNaturalModel ρ) :
    Module.finrank (ZMod 2) V = 3 * schurDegree ρ := by
  have hd := finrank_eq_schurDegree_mul 2 ρ (SplittingField ρ)
  change Module.finrank (ZMod 2) V = schurDegree ρ * _ at hd
  rw [hd]
  obtain ⟨ι, h⟩ := h
  rcases h with h | h <;> obtain ⟨e⟩ := h
  · rw [e.toLinearEquiv.finrank_eq]
    simp [mul_comm]
  · rw [e.toLinearEquiv.finrank_eq]
    simp [mul_comm]

/-- The absolute tensor alternative has binary dimension nine times the Schur degree. -/
theorem binary_finrank_of_absolute_twisted (r : ℕ) (h : HasAbsoluteTwistedModel ρ r) :
    Module.finrank (ZMod 2) V = 9 * schurDegree ρ := by
  have hd := finrank_eq_schurDegree_mul 2 ρ (SplittingField ρ)
  change Module.finrank (ZMod 2) V = schurDegree ρ * _ at hd
  rw [hd]
  obtain ⟨σ, _, ι, h⟩ := h
  rcases h with h | h <;> obtain ⟨e⟩ := h
  · rw [e.toLinearEquiv.finrank_eq, Module.finrank_tensorProduct]
    simp [mul_comm]
  · rw [e.toLinearEquiv.finrank_eq, Subspace.dual_finrank_eq, Module.finrank_tensorProduct]
    simp [mul_comm]

omit [IsIrreducible ρ] in
/-- The order of the actual binary Schur field. -/
theorem schurField_natCard : Nat.card (SchurField ρ) = 2 ^ schurDegree ρ := by
  let : Module.Finite (ZMod 2) (SchurField ρ) := Module.Finite.of_finite
  simpa only [Nat.card_zmod, schurDegree] using
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := SchurField ρ)

/-- The absolute natural field embedding is compatible with an actual Schur-field
isomorphism onto F. -/
theorem exists_natural_schur_equiv [Finite F] (n : ℕ)
    (hF : Nat.card F = 2 ^ n) (hE : schurDegree ρ = n)
    (ι : F →+* SplittingField ρ) :
    ∃ e : SchurField ρ ≃+* F,
      ∀ a, ι (e a) = algebraMap (SchurField ρ) (SplittingField ρ) a := by
  apply FiniteField.exists_compatible_equiv_of_card_eq
  rw [schurField_natCard ρ, hE, hF]

/-- The absolute tensor field embedding identifies the Schur field with the
actual fixed field of its specified half-degree Frobenius. -/
theorem exists_twisted_schur_equiv [Finite F] (r : ℕ) (hr : 0 < r)
    (hF : Nat.card F = 2 ^ (2 * r)) (hE : schurDegree ρ = r)
    (σ : F ≃+* F) (hσ : ∀ a, σ a = a ^ (2 ^ r))
    (ι : F →+* SplittingField ρ) :
    ∃ e : SchurField ρ ≃+* FixedBy.subfield F σ,
      ∀ a, ι (e a : F) = algebraMap (SchurField ρ) (SplittingField ρ) a := by
  apply FiniteField.exists_compatible_binary_fixedField_equiv
    (algebraMap (SchurField ρ) (SplittingField ρ)) ι σ r hr
      (by rw [schurField_natCard ρ, hE]) hF hσ

section Descent
variable [Finite F] [CharP F 2]
open Representation.BinaryFieldDescent

/-- An absolute natural or dual-natural model descends to the literal binary
natural or dual-natural action. Choosing the Schur-field isomorphism compatibly
with the absolute embedding accounts for its arbitrary coefficient twist. -/
theorem descend_absolute_natural (n : ℕ) (hF : Nat.card F = 2 ^ n)
    (hE : schurDegree ρ = n) (h : HasAbsoluteNaturalModel ρ) :
    let := ZMod.algebra F 2
    Nonempty (ρ.Equiv (naturalBinary F)) ∨ Nonempty (ρ.Equiv (dualBinary F)) := by
  let := ZMod.algebra F 2
  obtain ⟨ι, h⟩ := h
  let : Algebra F (SplittingField ρ) := ι.toAlgebra
  obtain ⟨e, he⟩ := exists_natural_schur_equiv ρ n hF hE ι
  let := scalarModule ρ e
  let : Finite V := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) V)
  let : Module.Finite F V := Module.Finite.of_finite
  let τ := scalarRep ρ e
  let eS := scalarExtensionEquiv ρ e he
  let eN := naturalUntwistedBaseChange (F := F) (K := SplittingField ρ)
  rcases h with h | h
  · obtain ⟨ea⟩ := h
    obtain ⟨ed⟩ := equiv_of_extendScalars (K := SplittingField ρ) τ (specialLinearNatural (k := F) 3)
      ⟨eS.symm.trans (ea.trans eN.symm)⟩
    left
    have eb := restrictBinaryEquiv ed
    simpa only [τ, restrict_scalarRep, naturalBinary] using Nonempty.intro eb
  · obtain ⟨ea⟩ := h
    let eD := (dualBaseChange (K := SplittingField ρ)
      (specialLinearNatural (k := F) 3)).trans (dualEquiv eN)
    obtain ⟨ed⟩ := equiv_of_extendScalars (K := SplittingField ρ) τ (specialLinearNatural (k := F) 3).dual
      ⟨eS.symm.trans (ea.trans eD.symm)⟩
    right
    have eb := (restrictBinaryEquiv ed).trans (dualBinaryEquiv F).symm
    simpa only [τ, restrict_scalarRep] using Nonempty.intro eb

/-- An absolute half-field tensor model descends on the original carrier V.
The witness includes the actual fixed subfield, its scalar action, exact binary
restriction, an equivalence over F, and the binary dimension. This holds for
every positive r, hence in particular for the source cases r = 1 and r = 2. -/
theorem descend_absolute_twisted (r : ℕ) (hr : 0 < r)
    (hF : Nat.card F = 2 ^ (2 * r)) (hE : schurDegree ρ = r)
    (h : HasAbsoluteTwistedModel ρ r) :
    ∃ σ : F ≃+* F, (∀ a, σ a = a ^ (2 ^ r)) ∧ Function.Involutive σ ∧
      σ ≠ RingEquiv.refl F ∧
      ∃ S : Subfield F, S = FixedBy.subfield F σ ∧ Nat.card S = 2 ^ r ∧
      ∃ m : Module S V, letI := m; letI := ZMod.algebra S 2
      ∃ τ : Representation S SL(3,F) V,
        restrictScalars (k := ZMod 2) τ = ρ ∧
        (Nonempty ((extendScalars F τ).Equiv (twistedTensor F σ)) ∨
         Nonempty ((extendScalars F τ).Equiv (twistedTensor F σ).dual)) ∧
        Module.finrank (ZMod 2) V = 9 * r := by
  have hdim : Module.finrank (ZMod 2) V = 9 * r := by
    rw [binary_finrank_of_absolute_twisted ρ r h, hE]
  obtain ⟨σ, hσ, ι, h⟩ := h
  have hσeq : σ = iterateFrobeniusEquiv F 2 r := by
    ext a
    exact hσ a
  have hf := FiniteField.binary_quadratic_frobenius_data r hr hF
  rw [← hσeq] at hf
  let S := FixedBy.subfield F σ
  obtain ⟨e, he⟩ := exists_twisted_schur_equiv ρ r hr hF hE σ hσ ι
  let : Algebra F (SplittingField ρ) := ι.toAlgebra
  let : Algebra S (SplittingField ρ) := (ι.comp S.subtype).toAlgebra
  let := scalarModule ρ e
  let := ZMod.algebra S 2
  let : Finite V := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) V)
  let : Module.Finite S V := Module.Finite.of_finite
  let τ := scalarRep ρ e
  let eS := scalarExtensionEquiv ρ e he
  let eT := twistedTensorBaseChange (K := SplittingField ρ) σ
  refine ⟨σ, hσ, hf.1, hf.2.1, S, rfl, hf.2.2, scalarModule ρ e,
    τ, restrict_scalarRep ρ e, ?_, hdim⟩
  rcases h with h | h
  · obtain ⟨ea⟩ := h
    apply Or.inl
    apply equiv_of_extendScalars (K := SplittingField ρ)
    let tower : IsScalarTower S F (SplittingField ρ) :=
      IsScalarTower.of_algebraMap_eq (fun a => rfl)
    exact ⟨(@extendScalars_comp S SL(3,F) V _ _ _ _ F _ _ τ
      (SplittingField ρ) _ _ _ tower).toRepresentationEquiv.trans
        (eS.symm.trans (ea.trans eT.symm))⟩
  · obtain ⟨ea⟩ := h
    apply Or.inr
    let eD := (dualBaseChange (K := SplittingField ρ) (twistedTensor F σ)).trans
      (dualEquiv eT)
    apply equiv_of_extendScalars (K := SplittingField ρ)
    let tower : IsScalarTower S F (SplittingField ρ) :=
      IsScalarTower.of_algebraMap_eq (fun a => rfl)
    exact ⟨(@extendScalars_comp S SL(3,F) V _ _ _ _ F _ _ τ
      (SplittingField ρ) _ _ _ tower).toRepresentationEquiv.trans
        (eS.symm.trans (ea.trans eD.symm))⟩

end Descent

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
