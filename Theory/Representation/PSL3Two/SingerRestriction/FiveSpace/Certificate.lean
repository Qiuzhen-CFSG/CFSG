module

public import Theory.Representation.PSL3Two.SingerRestriction
/-!
# Finite certificates for the Singer five-space restriction

The seven displayed matrices are the actual powers of the published Singer
matrix. The normalizer consists of their products with the powers of one
explicit cubic matrix. A second calculation says that if `v + singer(v)`
is in the Singer orbit of a trace-zero matrix v, then its cubic image is in
that same orbit. Transitivity on a moving three-space supplies this condition.
`Normalizer` connects these matrix calculations to the actual Steinberg action.

Using tables avoids repeatedly reducing matrix powers inside the finite tests.
The two kernel certificates were benchmarked together: 268 seconds wall time,
89 seconds user CPU and 5.3 GiB peak memory, including import preparation.

Source: Aschbacher–Smith, Lemma J.2.3, printed pp.433–434
(PDF pp.444–445), combined manuscript of 1 March 2004.
-/

@[expose] public section

open Matrix
open scoped Matrix
namespace BinaryLinearThree.SingerRestriction.FiveSpace.Certificate
open Matrix.PSL3Two.OuterInvolutionSinger
abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 2)
def powerMatrix : Fin 7 → Mat :=
  ![!![1,0,0; 0,1,0; 0,0,1],
    !![0,0,1; 0,1,1; 1,1,0],
    !![1,1,0; 1,0,1; 0,1,0],
    !![0,1,0; 1,1,1; 0,1,1],
    !![0,1,1; 1,0,0; 1,0,1],
    !![1,0,1; 0,0,1; 1,1,1],
    !![1,1,1; 1,1,0; 1,0,0]]
def inverseMatrix : Fin 7 → Mat :=
  ![!![1,0,0; 0,1,0; 0,0,1],
    !![1,1,1; 1,1,0; 1,0,0],
    !![1,0,1; 0,0,1; 1,1,1],
    !![0,1,1; 1,0,0; 1,0,1],
    !![0,1,0; 1,1,1; 0,1,1],
    !![1,1,0; 1,0,1; 0,1,0],
    !![0,0,1; 0,1,1; 1,1,0]]
def cubic : Group := ⟨!![0,0,1; 1,1,1; 1,0,1], by decide⟩
def cubicMatrix : Fin 3 → Mat :=
  ![!![1,0,0; 0,1,0; 0,0,1],
    !![0,0,1; 1,1,1; 1,0,1],
    !![1,0,1; 0,1,1; 1,0,0]]

def power (i : Fin 7) : Group := ⟨powerMatrix i, by fin_cases i <;> decide⟩
def cubicPower (i : Fin 3) : Group := ⟨cubicMatrix i, by fin_cases i <;> decide⟩
def act (i : Fin 7) (v : Mat) : Mat := powerMatrix i * v * inverseMatrix i

theorem power_eq (i : Fin 7) : power i = singer ^ (i : ℕ) := by fin_cases i <;> decide
theorem cubicPower_eq (i : Fin 3) : cubicPower i = cubic ^ (i : ℕ) := by fin_cases i <;> decide
theorem inverseMatrix_eq (i : Fin 7) : inverseMatrix i = ((power i)⁻¹).val := by fin_cases i <;> decide

set_option maxRecDepth 3000 in
theorem normalizer_certificate : ∀ g : Group,
    (∃ i : Fin 7, g * singer = power i * g) →
    ∃ i : Fin 7, ∃ j : Fin 3, g = power i * cubicPower j := by
  decide +kernel

set_option maxRecDepth 3000 in
theorem vector_certificate : ∀ v : Mat, v.trace = 0 →
    (∃ i : Fin 7, act i v = v + act 1 v) →
    ∃ j : Fin 7, cubic.val * v * (cubicMatrix 2) = act j v := by
  decide +kernel
end BinaryLinearThree.SingerRestriction.FiveSpace.Certificate
