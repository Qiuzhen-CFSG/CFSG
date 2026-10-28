module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.BinaryDescent.Schur
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.BinaryDescent.Singleton


/-!
# Binary descent from the absolute symplectic tensor catalogue

For a faithful irreducible binary representation of the literal derived
subgroup of Sp₄(F), construct positive s,t,a with n = st and binary degree
s(4^a)^t. Here s is the degree of the actual Schur endomorphism field.
Frobenius rotation and catalogue uniqueness make the selected factors
repeat in t blocks, and faithfulness excludes an empty block.

If a = t = 1, genuine field transport and scalar descent identify the
binary representation with the restriction of a basic graph twist. These
are precisely the parameters and intertwiner consumed by the degree and
small-module assembly in `NonbinaryRecognition`.

The absolute catalogue for embeddings into the algebraic closure of the
Schur field remains explicit. Its construction and the unconditional
source recognition theorem are separate from this conditional descent.

Sources: GLS3, Corollary 2.8.6(a), Remark 2.8.8 and Examples 2.8.10(d);
Aschbacher--Smith, G.9.3 proof, printed pp.356–357 of `refs/quasithin.pdf`.
-/

public section

open Representation Representation.FrobeniusTensor
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
noncomputable section
variable {F V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (Derived F) V) [ρ.IsIrreducible]

/-- Construct the source tensor parameters and descend the actual one-factor action,
assuming only the explicit absolute catalogue in addition to the binary action hypotheses. -/
theorem exists_binary_tensor_parameters {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2^n) (hρ : Function.Injective ρ)
    (cat : ∀ e : F →+* Closure ρ, AbsoluteTensorCatalogue F (Closure ρ) e n) :
    ∃ s t a : ℕ, 0 < s ∧ 0 < t ∧ 0 < a ∧ n = s*t ∧
      Module.finrank (ZMod 2) V = s*(4^a)^t ∧
      (a = 1 → t = 1 → ∃ j : Fin (2*n),
        Nonempty (ρ.Equiv (restrictScalars (k := ZMod 2) (basicTwist F j)))) := by
  obtain ⟨e, S, t, a, ht, ha, hnt, hcard, hd, ⟨φ⟩⟩ :=
    exists_schur_tensor_parameters ρ (by omega) hF hρ cat
  refine ⟨Module.finrank (ZMod 2) (SchurField ρ), t, a,
    schurField_finrank_pos ρ, ht, ha, hnt, hd, ?_⟩
  intro ha1 ht1
  apply binary_basicTwist_equiv_of_schur_degree_eq ρ hF
  · simpa only [ht1, mul_one] using hnt.symm
  · rw [φ.toLinearEquiv.finrank_eq, tensorModel_finrank, hcard, ha1, ht1]
    norm_num
  · exact cat

end
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
