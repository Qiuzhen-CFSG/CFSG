module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeModel
public import Theory.Mathieu.LargeInvolutionGeneration.Generators
/-!
# Generation by the native M23 pair

The native point tables are checked through their M24 extensions. Three
short words recover the relabelled M22 pair and the standard 23-cycle,
so the existing point-stabilizer maximality argument proves generation.
All word and table identities are kernel checked; GAP only finds witnesses.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, M23 paragraph. See `source/README.md` for conventions.
-/

open Sporadic.Mathieu Sporadic.Mathieu.LargeInvolutionGeneration
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
@[expose] public noncomputable section

def generatorPoint : Fin 2 → Fin 23 → Fin 23 :=
![![14, 1, 13, 10, 18, 22, 8, 16, 6, 9, 3, 11, 12, 2, 0, 15, 7, 17, 4, 19, 21, 20, 5],
  ![11, 0, 5, 3, 17, 20, 15, 1, 10, 18, 8, 7, 21, 4, 14, 12, 13, 16, 9, 2, 19, 6, 22]]

theorem generator_apply (k : Fin 2) (x : Fin 23) :
    (actor k).val x = generatorPoint k x := by
  apply m23PointEmbedding.injective
  rw [← m23ExtendHom_apply_embedded]
  have he : m23ExtendHom (actor k) =
      (![m23M24GeneratorA, m23M24GeneratorB] k).val := by
    fin_cases k
    · exact congrArg (fun s : MulAction.stabilizer M24 (24 : Fin 24) => s.val.val)
        m23GeneratorA_extension
    · exact congrArg (fun s : MulAction.stabilizer M24 (24 : Fin 24) => s.val.val)
        m23GeneratorB_extension
  rw [he]
  clear he
  revert k x
  decide +kernel

def letter : Fin 4 → M23 :=
  ![actor 0, actor 1, (actor 0)⁻¹, (actor 1)⁻¹]

def letterPoint : Fin 4 → Fin 23 → Fin 23 :=
![![14, 1, 13, 10, 18, 22, 8, 16, 6, 9, 3, 11, 12, 2, 0, 15, 7, 17, 4, 19, 21, 20, 5],
  ![11, 0, 5, 3, 17, 20, 15, 1, 10, 18, 8, 7, 21, 4, 14, 12, 13, 16, 9, 2, 19, 6, 22],
  ![14, 1, 13, 10, 18, 22, 8, 16, 6, 9, 3, 11, 12, 2, 0, 15, 7, 17, 4, 19, 21, 20, 5],
  ![1, 7, 19, 3, 13, 2, 21, 11, 10, 18, 8, 0, 15, 16, 14, 6, 17, 4, 9, 20, 5, 12, 22]]

theorem letter_apply (k : Fin 4) (x : Fin 23) :
    (letter k).val x = letterPoint k x := by
  fin_cases k
  · exact generator_apply 0 x
  · exact generator_apply 1 x
  · apply (actor 0).val.injective
    change (actor 0).val ((actor 0).val.symm x) = _
    rw [_root_.Equiv.apply_symm_apply, generator_apply]
    revert x
    decide +kernel
  · apply (actor 1).val.injective
    change (actor 1).val ((actor 1).val.symm x) = _
    rw [_root_.Equiv.apply_symm_apply, generator_apply]
    revert x
    decide +kernel

def target : Fin 3 → M23 := ![a23, b23, m23Standard23]

def generationWord : Fin 3 → List (Fin 4) :=
![[2],
  [1, 2, 3, 2, 1, 2, 1],
  [1, 0]]

theorem generation (i : Fin 3) : evalWord letter (generationWord i) = target i := by
  apply Subtype.ext
  apply _root_.Equiv.ext
  intro x
  rw [evalWord_apply _ _ letter_apply]
  revert i x
  decide +kernel

theorem native_generates : Subgroup.closure
    ({m23GeneratorAInM23, m23GeneratorBInM23} : Set M23) = ⊤ := by
  let H := Subgroup.closure ({m23GeneratorAInM23, m23GeneratorBInM23} : Set M23)
  have hl (k : Fin 4) : letter k ∈ H := by
    fin_cases k
    · exact Subgroup.subset_closure (by simp [letter, actor])
    · exact Subgroup.subset_closure (by simp [letter, actor])
    · exact H.inv_mem (Subgroup.subset_closure (by simp [actor]))
    · exact H.inv_mem (Subgroup.subset_closure (by simp [actor]))
  have hw (w : List (Fin 4)) : evalWord letter w ∈ H := by
    induction w with
    | nil => exact H.one_mem
    | cons k w ih => exact H.mul_mem (hl k) ih
  apply m23_eq_top_of_generators
  · have ht := hw (generationWord 0)
    rw [generation] at ht
    exact ht
  · have ht := hw (generationWord 1)
    rw [generation] at ht
    exact ht
  · have ht := hw (generationWord 2)
    rw [generation] at ht
    exact ht
end
end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
