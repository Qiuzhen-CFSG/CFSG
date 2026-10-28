module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates.CoverageTable

/-!
# Explicit fusion of all fifteen outer actors

The determinant-one matrices below use the convention `g * x * g⁻¹`.
On the graph coset this becomes the Gram-matrix operation `g * x * gᵀ`.
Small matrix equalities certify the entire image of each actor, including
the two elementary eight-groups, in one of three suitable rows.

Source: Aschbacher–Smith E.1.14(7), printed p.214; Asc82a Lemma 4.11.
Conjugators were discovered by the supplied ActorWitnesses.g diagnostic;
the kernel checks the matrices and every claimed coordinate image here.
-/

public section
set_option maxRecDepth 10000
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates

open Matrix.PSL3Three
open Matrix.PSL3.OuterSolvable
@[expose] def conjugatorMatrix : Fin 15 → SL :=
  ![⟨!![1,0,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![2,0,1; 2,0,2; 1,1,0], by decide⟩,
    ⟨!![1,2,1; 1,1,2; 2,2,0], by decide⟩,
    ⟨!![0,2,2; 1,0,0; 2,2,0], by decide⟩,
    ⟨!![0,0,1; 0,2,0; 1,1,0], by decide⟩,
    ⟨!![0,2,1; 0,1,0; 2,2,0], by decide⟩,
    ⟨!![1,0,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![1,0,0; 0,0,1; 0,2,0], by decide⟩,
    ⟨!![2,0,0; 0,2,1; 0,1,0], by decide⟩,
    ⟨!![0,2,0; 0,1,1; 2,2,2], by decide⟩,
    ⟨!![0,1,1; 0,1,0; 2,2,0], by decide⟩,
    ⟨!![0,2,0; 2,0,0; 1,2,2], by decide⟩,
    ⟨!![0,0,2; 2,0,0; 1,1,2], by decide⟩,
    ⟨!![1,0,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![1,0,0; 0,0,1; 0,2,0], by decide⟩]

@[expose] def target : Fin 15 → Fin 15 := ![0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 0, 6, 6, 13, 13]

@[expose] def fusionTable : Fin 15 → Bool → Fin 16 → Fin 16 :=
  ![(fun b => if b then ![0, 0, 0, 0, 0, 0, 0, 7, 0, 9, 0, 0, 0, 0, 0, 0] else ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0]),
    (fun b => if b then ![0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0] else ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0]),
    (fun b => if b then ![0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0] else ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0]),
    (fun b => if b then ![0, 0, 0, 7, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0] else ![0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0]),
    (fun b => if b then ![9, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else ![0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (fun b => if b then ![0, 0, 9, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0] else ![0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (fun b => if b then ![0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 13, 0, 0] else ![0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]),
    (fun b => if b then ![0, 0, 0, 0, 0, 7, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0] else ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0]),
    (fun b => if b then ![0, 7, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0] else ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0]),
    (fun b => if b then ![0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0] else ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0]),
    (fun b => if b then ![0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 7, 0, 0] else ![0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (fun b => if b then ![0, 0, 0, 13, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0] else ![0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (fun b => if b then ![0, 13, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] else ![0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    (fun b => if b then ![0, 0, 0, 3, 0, 0, 0, 7, 0, 9, 0, 0, 0, 13, 0, 0] else ![0, 0, 0, 0, 4, 0, 0, 0, 8, 0, 0, 0, 12, 0, 0, 0]),
    (fun b => if b then ![0, 3, 0, 0, 0, 7, 0, 0, 0, 13, 0, 0, 0, 9, 0, 0] else ![0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 8, 0, 0, 0, 12, 0])]

@[expose] def fuse (n : Fin 15) (i : Index) : Index :=
  (fusionTable n i.2 i.1, i.2)

theorem fuse_image : ∀ n : Fin 15, (actor n).image (fuse n) = actor (target n) := by
  decide +kernel

theorem fusion_matrix : ∀ (n : Fin 15) (i : Index), i ∈ actor n →
    (conjugatorMatrix n * twoElement i.1 *
      (if i.2 then Matrix.SpecialLinearGroup.transpose (conjugatorMatrix n)
       else (conjugatorMatrix n)⁻¹)).val = (twoElement (fuse n i).1).val := by
  decide +kernel

private theorem graph_inverse (x : SL) :
    graphSL (ZMod 3) x⁻¹ = Matrix.SpecialLinearGroup.transpose x := by
  change (Matrix.SpecialLinearGroup.transpose x⁻¹)⁻¹ = Matrix.SpecialLinearGroup.transpose x
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change x.val.transpose * (x⁻¹).val.transpose = (1 : SL).val
  rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]

theorem conjugate_pair (g x : SL) (b : Bool) :
    (MulAut.conj (inner g)) (pair x b) =
      pair (g * x * if b then Matrix.SpecialLinearGroup.transpose g else g⁻¹) b := by
  calc
    _ = pair g false * pair x b * pair g⁻¹ false := by
      simp [pair, MulAut.conj_apply]
    _ = _ := by
      rw [pair_mul, pair_mul]
      cases b <;> simp [graph_inverse]

/-- Each matrix conjugates every element of its whole actor to the indicated row. -/
theorem conjugate_element (n : Fin 15) (i : Index) (hi : i ∈ actor n) :
    (MulAut.conj (inner (conjugatorMatrix n))) (element i) = element (fuse n i) := by
  rw [element, conjugate_pair]
  have hm := Subtype.ext (fusion_matrix n i hi)
  rw [hm]
  rfl

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates
