module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.RootQuotient
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# A marked dihedral eight in the seven-point involution centralizer

An explicit rotation and reflection give an injective homomorphism from D8
into C_A7((01)(23)). Its central involution maps to (01)(23). Only the eight
words and their products are checked; the alternating group is not enumerated.
The center calculation supplies the normalizer control used in Held 5.4.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

@[expose] public def sevenCentralInvolution : sevenInvolutionCentralizer :=
  ⟨sevenInvolution, mem_centralizer_singleton_iff.mpr rfl⟩

private def rotation : alternatingGroup (Fin 7) :=
  ⟨swap 0 2 * swap 2 1 * swap 1 3 * swap 4 5, by simp [Perm.sign_mul]⟩

private def reflection : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 4 5, by simp [Perm.sign_mul]⟩

private def word : DihedralGroup 4 → alternatingGroup (Fin 7)
  | .r i => rotation ^ i.val
  | .sr i => reflection * rotation ^ i.val

private theorem word_mem : ∀ x, word x ∈ sevenInvolutionCentralizer := by
  intro x
  apply mem_centralizer_singleton_iff.mpr
  exact (by decide +kernel : ∀ x, word x * sevenInvolution = sevenInvolution * word x) x

public def dihedralEmbedding : DihedralGroup 4 →* sevenInvolutionCentralizer where
  toFun x := ⟨word x, word_mem x⟩
  map_one' := by apply Subtype.ext; decide +kernel
  map_mul' x y := by
    apply Subtype.ext
    exact (by decide +kernel : ∀ x y, word (x * y) = word x * word y) x y

public theorem dihedralEmbedding_injective : Function.Injective dihedralEmbedding := by
  have h : Function.Injective (fun x => ((word x : Perm (Fin 7)) 0,
      (word x : Perm (Fin 7)) 2)) := by decide +kernel
  intro x y hxy
  exact h (congrArg (fun c : sevenInvolutionCentralizer =>
    (((c : alternatingGroup (Fin 7)) : Perm (Fin 7)) 0,
     ((c : alternatingGroup (Fin 7)) : Perm (Fin 7)) 2)) hxy)

public theorem dihedralEmbedding_central :
    dihedralEmbedding (.r 2) = sevenCentralInvolution := by
  apply Subtype.ext
  decide +kernel

public theorem dihedral_center : center (DihedralGroup 4) = zpowers (.r 2) := by
  apply le_antisymm
  · intro x hx
    have h : x = 1 ∨ x = DihedralGroup.r 2 := by
      exact (by decide +kernel : ∀ x : DihedralGroup 4,
        (∀ y, y * x = x * y) → x = 1 ∨ x = DihedralGroup.r 2) x
        (mem_center_iff.mp hx)
    rcases h with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · apply zpowers_le.mpr
    rw [mem_center_iff]
    decide +kernel

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry
