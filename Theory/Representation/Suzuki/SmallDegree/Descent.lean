module

public import Theory.Representation.Suzuki.SmallDegree.Descent.Rotation
public import Theory.Representation.Suzuki.SmallDegree.Reduction
public import Theory.Representation.SL3.BinaryFieldDescent
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange
public import Theory.Representation.SL3.BinaryFieldDescent.Fields

/-!
# Field periods and binary descent of Suzuki tensors

For an actual tensor model of the absolute Schur representation, Frobenius
rotation and distinctness of supports imply `(2*m+1) ∣ I.card*d`, where `d`
is the degree of the commuting endomorphism field. All tensors are defined
over the Suzuki field, so also `d ∣ 2*m+1`. A singleton thus has `d = 2*m+1`.

Equal finite subfields of the common algebraic closure identify the Schur
field with the defining field compatibly with their specified embeddings.
Scalar descent then supplies an actual binary intertwiner, and the proved
natural-module automorphism intertwiners remove the remaining field twist.
The original group marking is retained, including for Sz(8).

Tensor irreducibility and distinctness are explicit independent catalogue
inputs. The final applications discharge the period premise of `SmallDegree`
and recognize every supplied nonempty tensor model in its degree window;
exhaustion by those models remains with the classification owner.
Source: GLS3, Remark 2.8.8; Guralnick–Malle, *Classification of 2F-modules, II*,
§3.1 and Lemma 8.3.
-/

public noncomputable section
open scoped TensorProduct Fin.NatCast
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural FrobeniusTensor

section Schur
variable {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) [ρ.IsIrreducible]
  [Algebra (F m) (Closure ρ)]

/-- Every concrete tensor is defined over the Suzuki field, so the degree of the
actual binary Schur field divides its exponent. -/
theorem schurDegree_dvd_field_exponent (I : Support m)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I)) :
    Module.finrank (ZMod 2) (SchurField ρ) ∣ 2 * m + 1 := by
  apply (character_pow_iff ρ _).mp
  intro g
  rw [char_iso e, ← character_tensor_rotate]
  have hr : rotateSupport (2 * m + 1) I = I := by
    simp [rotateSupport]
  rw [hr]

/-- The actual Schur Frobenius period fixes the support, by tensor distinctness. -/
theorem support_rotate_schurDegree (I : Support m)
    (hirr : ∀ J : Support m, (tensorRep m (Closure ρ) J).IsIrreducible)
    (hunique : ∀ J L : Support m,
      Nonempty ((tensorRep m (Closure ρ) J).Equiv (tensorRep m (Closure ρ) L)) → J = L)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I)) :
    rotateSupport (Module.finrank (ZMod 2) (SchurField ρ)) I = I := by
  let d := Module.finrank (ZMod 2) (SchurField ρ)
  obtain ⟨f⟩ := tensor_frobenius_equiv_rotate m (Closure ρ) hirr d I
  let := hirr I
  let := hirr (rotateSupport d I)
  apply hunique
  apply (character_eq_iff_equiv_of_irreducible _ _).mp
  funext g
  rw [← char_iso f, character_frobeniusConjugate, ← char_iso e]
  exact (character_pow_iff ρ d).mpr (dvd_refl d) g

/-- The field exponent divides the support size times the actual Schur degree.
Only irreducibility and distinctness of the tensor catalogue are additional inputs. -/
theorem field_period_dvd (I : Support m)
    (hirr : ∀ J : Support m, (tensorRep m (Closure ρ) J).IsIrreducible)
    (hunique : ∀ J L : Support m,
      Nonempty ((tensorRep m (Closure ρ) J).Equiv (tensorRep m (Closure ρ) L)) → J = L)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I)) :
    2 * m + 1 ∣ I.card * Module.finrank (ZMod 2) (SchurField ρ) :=
  support_period_dvd_card_mul _ I (support_rotate_schurDegree ρ I hirr hunique e)

/-- A singleton tensor has the full Suzuki field as its minimal coefficient field. -/
theorem singleton_schurDegree (I : Support m) (hI : I.card = 1)
    (hirr : ∀ J : Support m, (tensorRep m (Closure ρ) J).IsIrreducible)
    (hunique : ∀ J L : Support m,
      Nonempty ((tensorRep m (Closure ρ) J).Equiv (tensorRep m (Closure ρ) L)) → J = L)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I)) :
    Module.finrank (ZMod 2) (SchurField ρ) = 2 * m + 1 := by
  apply Nat.dvd_antisymm (schurDegree_dvd_field_exponent ρ I e)
  simpa only [hI, one_mul] using field_period_dvd ρ I hirr hunique e

open BinaryFieldDescent in
/-- A singleton absolute tensor descends to the natural binary module on the
originally marked Suzuki group, including `m = 1`. The Schur-field isomorphism
respects both prescribed embeddings into the algebraic closure. -/
theorem singleton_descent (hm : 1 ≤ m) (I : Support m) (hI : I.card = 1)
    (hirr : ∀ J : Support m, (tensorRep m (Closure ρ) J).IsIrreducible)
    (hunique : ∀ J L : Support m,
      Nonempty ((tensorRep m (Closure ρ) J).Equiv (tensorRep m (Closure ρ) L)) → J = L)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I)) :
    Nonempty (ρ.Equiv (natural m)) := by
  have hd := singleton_schurDegree ρ I hI hirr hunique e
  have hc : Nat.card (F m) = Nat.card (SchurField ρ) := by
    let : Module.Finite (ZMod 2) (SchurField ρ) := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := SchurField ρ), Nat.card_zmod, hd]
    exact GaloisField.card 2 _ (by omega)
  obtain ⟨c, hc⟩ := FiniteField.exists_compatible_equiv_of_card_eq
    (algebraMap (SchurField ρ) (Closure ρ)) (algebraMap (F m) (Closure ρ)) hc
  let := scalarModule ρ c
  let : Finite V := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) V)
  let : Module.Finite (F m) V := Module.Finite.of_finite
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
  have hi : exponents ({i} : Support m) = [i.val] := by simp [exponents]
  have ee : (absoluteRep ρ).Equiv (extendScalars (Closure ρ) (wordRep m [i.val])) := by
    change (absoluteRep ρ).Equiv (extendScalars (Closure ρ) (wordRep m (exponents {i}))) at e
    rw [hi] at e
    exact e
  let es := scalarExtensionEquiv ρ c hc
  obtain ⟨ed⟩ := equiv_of_extendScalars (K := Closure ρ) (scalarRep ρ c) (factorRep m i.val)
    ⟨es.symm.trans (ee.trans (extendEquiv (K := Closure ρ) (singletonFieldEquiv m i.val)))⟩
  have eb := restrictBinaryEquiv ed
  rw [restrict_scalarRep] at eb
  have eb' : ρ.Equiv ((natural m).comp (suzukiFieldAutomorphism m ^ i.val).toMonoidHom) := by
    exact .mk eb.toLinearEquiv (fun g => eb.isIntertwining' g)
  exact equiv_of_aut_twist hm ρ _ eb'

/-- Discharge the period premise of the existing small-degree support exclusion
using the concrete tensor catalogue. -/
theorem support_card_eq_one_of_tensor_model (I : Support m) (hI : I.Nonempty)
    (hirr : ∀ J : Support m, (tensorRep m (Closure ρ) J).IsIrreducible)
    (hunique : ∀ J L : Support m,
      Nonempty ((tensorRep m (Closure ρ) J).Equiv (tensorRep m (Closure ρ) L)) → J = L)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I))
    (hsmall : Module.finrank (ZMod 2) V < 10 * (2 * m + 1)) : I.card = 1 :=
  support_card_eq_one_of_smallDegree ρ I hI e (field_period_dvd ρ I hirr hunique e) hsmall

/-- The small-degree bound and an actual nonempty tensor model give the marked
binary natural module. The source-classification owner supplies the tensor
model, irreducibility and distinctness; no further descent premise remains. -/
theorem natural_equiv_of_smallDegree_tensor_model (hm : 1 ≤ m)
    (I : Support m) (hI : I.Nonempty)
    (hirr : ∀ J : Support m, (tensorRep m (Closure ρ) J).IsIrreducible)
    (hunique : ∀ J L : Support m,
      Nonempty ((tensorRep m (Closure ρ) J).Equiv (tensorRep m (Closure ρ) L)) → J = L)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I))
    (hsmall : Module.finrank (ZMod 2) V < 10 * (2 * m + 1)) :
    Nonempty (ρ.Equiv (natural m)) :=
  singleton_descent ρ hm I
    (support_card_eq_one_of_tensor_model ρ I hI hirr hunique e hsmall) hirr hunique e

end Schur
end Representation.SuzukiSmallDegree
