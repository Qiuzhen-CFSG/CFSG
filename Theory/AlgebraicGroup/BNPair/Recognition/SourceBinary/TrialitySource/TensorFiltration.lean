module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorCoordinates

/-!
# The first layer of the cubic tensor filtration

If every upper unipotent displaces a vector only along the highest axis,
its four coordinates with at least two lower factors vanish. Independence
of the three field embeddings proves this also over the cubic field over F₂.
The source application uses the literal commutator containment [D,A] ≤ E
from 6E(b), not an assumed root-coordinate formula.

Source: Fong--Seitz II, printed pp.218--219, the matrix calculations leading
to (9.27). TensorMiddleRoots applies this to the original radical quotient.
-/

@[expose] public noncomputable section
open scoped MatrixGroups TensorProduct MonoidAlgebra
open Representation Representation.SL2 Representation.SL2.BinarySmall
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorFiltration
open TensorCoordinates
variable {F C : Type*} [Field F] [Field C]

theorem upper_displacement_top (κ : F →+* C) (σ : F ≃+* F)
    (hcube : ∀ a, σ (σ (σ a)) = a) (hne : ∃ a, σ a ≠ a)
    (v : TripleSpace C)
    (h : ∀ a, ∃ c : C, TensorAction.cubicTensor κ σ (uni a) v =
      v + c • basis ((0,0),0)) :
    coordinates v ((1,1),1) = 0 ∧ coordinates v ((1,1),0) = 0 ∧
      coordinates v ((1,0),1) = 0 ∧ coordinates v ((0,1),1) = 0 := by
  have he (a : F) (r : Index) (hr : r ≠ ((0,0),0)) :
      upper κ σ a (coordinates v) r = coordinates v r := by
    obtain ⟨c,hc⟩ := h a
    have hh := congrArg (fun z => coordinates z r) hc
    rw [action] at hh
    simpa [upper,coordinates,hr] using hh
  have h111 : coordinates v ((1,1),1) = 0 := by
    have hh := he 1 ((1,1),0) (by decide)
    simpa only [upper_110,map_one,one_mul,add_eq_left] using hh
  have hp : coordinates v ((1,1),0) = 0 ∧ coordinates v ((1,0),1) = 0 := by
    have hh (a : F) := he a ((1,0),0) (by decide)
    simp only [upper_100,h111,mul_zero,add_zero,add_assoc,add_eq_left] at hh
    exact (separate κ σ hcube hne 0 (coordinates v ((1,1),0))
      (coordinates v ((1,0),1)) (by
        intro a
        simpa only [zero_mul,zero_add,mul_comm,add_comm] using hh a)).2
  have h011 : coordinates v ((0,1),1) = 0 := by
    have hh := he 1 ((0,1),0) (by decide)
    simpa only [upper_010,h111,hp.1,map_one,one_mul,add_zero,add_eq_left] using hh
  exact ⟨h111,hp.1,hp.2,h011⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorFiltration
