module

public import Theory.Representation.FirstCohomologySymplecticFour.Quadratic
import Mathlib.Tactic.FinCases

/-!
# Three binary generators in the derived symplectic four-group

These are the three commutators used to detect nonprincipality of the
quadratic-defect cocycle. Their explicit matrices give a finite coordinate
interface for the binary-field cocycle calculation. Generation of the derived
group and the resulting cocycle relations are established in separate modules.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408 (PDF p.419).
-/

@[expose] public section

open Matrix
open scoped commutatorElement

namespace Representation.OneCohomology.SymplecticFour.BinaryField

def transvection (v : (Fin 2 ⊕ Fin 2) → ZMod 2) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  1 + Matrix.of (fun i j => v i * (Sum.elim (fun k => v (Sum.inr k))
    (fun k => v (Sum.inl k)) j))

def symplecticTransvection (v : (Fin 2 ⊕ Fin 2) → ZMod 2) :
    Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  ⟨transvection v, by
    have h : ∀ v : (Fin 2 ⊕ Fin 2) → ZMod 2,
      transvection v * Matrix.J (Fin 2) (ZMod 2) * (transvection v)ᵀ =
        Matrix.J (Fin 2) (ZMod 2) := by decide
    exact h v⟩

/-- Three explicit commutators in the actual derived symplectic group. -/
def generator (j : Fin 3) :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) :=
  let u : (Fin 2 ⊕ Fin 2) → ZMod 2 :=
    if j = 1 then Sum.elim ![0, 0] ![1, 0] else Sum.elim ![0, 0] ![0, 1]
  let v : (Fin 2 ⊕ Fin 2) → ZMod 2 :=
    if j = 0 then Sum.elim ![0, 1] ![0, 0]
    else if j = 1 then Sum.elim ![1, 0] ![0, 0]
    else Sum.elim ![0, 1] ![1, 0]
  ⟨⁅symplecticTransvection u, symplecticTransvection v⁆, by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩

/-- Binary matrix coordinates for the three commutators. -/
def generatorMatrix (j : Fin 3) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ![Matrix.fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1]
      !![0, 0; 0, 1] !![1, 0; 0, 1],
    Matrix.fromBlocks !![0, 0; 0, 1] !![1, 0; 0, 0]
      !![1, 0; 0, 0] !![1, 0; 0, 1],
    Matrix.fromBlocks !![1, 0; 1, 0] !![0, 0; 0, 1]
      !![1, 1; 0, 1] !![1, 1; 0, 1]] j

/-- The finite matrix certificate for the three selected commutators. -/
theorem generator_val (j : Fin 3) : (generator j).val.val = generatorMatrix j := by
  have h : ∀ j, (generator j).val.val = generatorMatrix j := by decide
  exact h j

end Representation.OneCohomology.SymplecticFour.BinaryField
