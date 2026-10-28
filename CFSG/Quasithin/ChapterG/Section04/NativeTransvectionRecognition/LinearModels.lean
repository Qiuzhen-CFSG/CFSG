module
public import Theory.SpecificGroups.SymplecticFour.NativeBinaryLinear
public import Theory.SpecificGroups.SymplecticFour.NativeEvenLinearSpectral
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models

/-!
# Linear row exclusions for the native G.4.1 action

The actual binary degree-four and degree-five carriers, and all binary
PSL₃ fields, contain a seven-element conjugate to its square. Their faithful
images contradict the four-dimensional symplectic spectrum. Each theorem
applies the intrinsic obstruction to the literal supplied model equivalence.
Source: Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Field F] [CharP F 2]

/-- Neither displayed binary linear row of Theorem C embeds in Sp₄(F). -/
theorem not_binary_linear_model {n : ℕ} (hn : n=4 ∨ n=5)
    (j : H →* Sp F) (hj : Function.Injective j) : ¬ ClassicalGroup.IsPSL H n 2 := by
  rintro ⟨K,_,_,hK,⟨e⟩⟩
  exact NativeBinaryLinear.small_binary_not_injective hn hK
    (j.comp e.symm.toMonoidHom) (hj.comp e.symm.injective)

/-- No positive binary PSL₃ field survives the actual faithful action. -/
theorem not_binary_linear_three_model {n : ℕ} (_hn : 0<n)
    (j : H →* Sp F) (hj : Function.Injective j) : ¬ ClassicalGroup.IsPSL H 3 (2^n) := by
  rintro ⟨K,_,_,hK,⟨e⟩⟩
  letI := Fintype.ofFinite K
  letI : CharP K 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n) (by
    simpa only [Nat.card_eq_fintype_card] using hK)
  exact NativeEvenLinearSpectral.pslThree_not_injective
    (j.comp e.symm.toMonoidHom) (hj.comp e.symm.injective)
end CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
