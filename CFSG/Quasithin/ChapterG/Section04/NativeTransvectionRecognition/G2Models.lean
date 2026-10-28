module
public import Theory.SpecificGroups.SymplecticFour.NativeG2
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models

/-!
# G₂ rows excluded by the literal degree-four action

The octonion block embedding carries the binary seven-normalizer into every
even G₂ model and into its derived subgroup. Applying the symplectic spectral
obstruction to the supplied carrier equivalence removes both the positive
field and the binary derived row of Theorem C.
Source: Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
open Theory.SpecificGroups.SymplecticFour ClassificationModels
variable {H F : Type*} [Group H] [Field F] [CharP F 2]

/-- Every positive binary G₂ field is excluded by the actual faithful action. -/
theorem not_binary_g2_model {n : ℕ} (_hn : 0<n)
    (j : H →* Sp F) (hj : Function.Injective j) : ¬ IsG2At H (2^n) := by
  rintro ⟨K,_,_,hK,⟨e⟩⟩
  letI := Fintype.ofFinite K
  letI : CharP K 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n) (by
    simpa only [Nat.card_eq_fintype_card] using hK)
  exact NativeG2.model_not_injective (j.comp e.symm.toMonoidHom) (hj.comp e.symm.injective)

/-- The binary derived endpoint is excluded as its literal subgroup carrier. -/
theorem not_binary_derived_g2_model
    (j : H →* Sp F) (hj : Function.Injective j) :
    ¬ Nonempty (H ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  exact NativeG2.derived_not_injective (j.comp e.symm.toMonoidHom) (hj.comp e.symm.injective)
end CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
