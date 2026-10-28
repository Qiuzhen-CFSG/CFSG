module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.UniversalBound.FlagPresentation
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases

/-!
# A checked rank certificate for the binary flag relations

Forty-three explicit sums of the defining relations have distinct pivot
coordinates. Evaluation at those coordinates is a left inverse to their
column map, so the relation space has dimension at least 43. The coordinate
space has dimension 64; rank-nullity gives a quotient of dimension at most 21.

The script `source/generate_rank.py` reconstructs the three private tables.
Every column identity and every pivot identity is checked by Lean's kernel.
The largest certificate uses sixteen relators. Splitting checks by column
keeps the reduction memory bounded; no group enumeration is needed.

Source application: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3), pp.27–28. This is a finite binary highest-vector calculation,
not an invocation of an absolute highest-weight classification.
-/

@[expose] public section

open scoped Matrix
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl.FlagPresentation

private def pivot : Fin 43 → Fin 16 × Fin 4 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 1), (3, 0), (3, 1), (4, 2), (5, 0), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0), (7, 1), (7, 2), (8, 3), (9, 0), (9, 3), (10, 0), (10, 1), (10, 3), (11, 0), (11, 1), (11, 2), (11, 3), (12, 0), (12, 1), (12, 2), (12, 3), (13, 0), (13, 1), (13, 2), (13, 3), (14, 0), (14, 1), (14, 2), (14, 3), (15, 0), (15, 1), (15, 2), (15, 3)]

private def columns : Matrix (Fin 16 × Fin 4) (Fin 43) (ZMod 2) :=
  fun p j => if (![1, 2, 4, 8, 16, 512, 4384, 8480, 262144, 1114176, 4259904, 19088736, 33686528, 67240960, 270746880, 538969344, 1073954816, 34359738368, 73014444160, 554050781312, 1249835518368, 2207613192192, 8804682958848, 17742509934848, 35321811044608, 75061139131584, 140750373289984, 281771338432704, 567373904612352, 1125917087236096, 2251816994078720, 4503895989092352, 9011754078078112, 18014673387978752, 36028818502189056, 72058038703572352, 144119612027043840, 288234774198878208, 576460778207444992, 1152921949272491360, 2305847564037032352, 4611690710822014144, 9223372069067030528] : Fin 43 → Nat) j |>.testBit (4 * p.1.val + p.2.val) then 1 else 0

private def certificate : Fin 43 → List Relation :=
  ![[.inl 0],
    [.inl 1],
    [.inl 2],
    [.inl 3],
    [.inr (.inl 1)],
    [.inr (.inl 2)],
    [.inr (.inl 3), .inr (.inr (1, 2))],
    [.inr (.inr (1, 2))],
    [.inr (.inl 4)],
    [.inr (.inl 5), .inr (.inr (1, 4))],
    [.inr (.inr (1, 4))],
    [.inr (.inl 7), .inr (.inr (1, 6)), .inr (.inr (2, 5)), .inr (.inr (3, 4))],
    [.inr (.inl 6), .inr (.inr (2, 4))],
    [.inr (.inr (2, 4))],
    [.inr (.inr (2, 5)), .inr (.inr (3, 4))],
    [.inr (.inl 7), .inr (.inr (2, 5))],
    [.inr (.inr (3, 4))],
    [.inr (.inl 8)],
    [.inr (.inl 9), .inr (.inr (1, 8))],
    [.inr (.inr (1, 8))],
    [.inr (.inl 11), .inr (.inr (1, 10)), .inr (.inr (2, 9)), .inr (.inr (3, 8))],
    [.inr (.inl 10), .inr (.inr (2, 8))],
    [.inr (.inr (2, 8))],
    [.inr (.inr (2, 9)), .inr (.inr (3, 8))],
    [.inr (.inl 11), .inr (.inr (2, 9))],
    [.inr (.inl 13), .inr (.inl 14), .inr (.inl 15), .inr (.inr (1, 12)), .inr (.inr (2, 12)), .inr (.inr (3, 12)), .inr (.inr (4, 9)), .inr (.inr (4, 10)), .inr (.inr (4, 11)), .inr (.inr (5, 8)), .inr (.inr (6, 8)), .inr (.inr (7, 8))],
    [.inr (.inr (3, 8))],
    [.inr (.inl 13), .inr (.inr (1, 12)), .inr (.inr (4, 9)), .inr (.inr (5, 8))],
    [.inr (.inl 14), .inr (.inr (2, 12)), .inr (.inr (4, 10)), .inr (.inr (6, 8))],
    [.inr (.inl 12), .inr (.inr (4, 8))],
    [.inr (.inr (4, 8))],
    [.inr (.inr (4, 9)), .inr (.inr (5, 8))],
    [.inr (.inl 11), .inr (.inl 15), .inr (.inr (1, 10)), .inr (.inr (2, 9)), .inr (.inr (2, 13)), .inr (.inr (3, 8)), .inr (.inr (5, 10)), .inr (.inr (7, 8))],
    [.inr (.inl 13), .inr (.inr (4, 9))],
    [.inr (.inr (5, 8))],
    [.inr (.inl 11), .inr (.inl 13), .inr (.inl 14), .inr (.inr (1, 10)), .inr (.inr (1, 12)), .inr (.inr (1, 14)), .inr (.inr (2, 9)), .inr (.inr (2, 12)), .inr (.inr (3, 8)), .inr (.inr (3, 12)), .inr (.inr (4, 9)), .inr (.inr (4, 10)), .inr (.inr (5, 8)), .inr (.inr (5, 10)), .inr (.inr (6, 8)), .inr (.inr (7, 8))],
    [.inr (.inr (4, 10)), .inr (.inr (6, 8))],
    [.inr (.inl 14), .inr (.inr (4, 10))],
    [.inr (.inr (6, 8))],
    [.inr (.inl 11), .inr (.inl 13), .inr (.inl 14), .inr (.inl 15), .inr (.inr (1, 10)), .inr (.inr (1, 12)), .inr (.inr (2, 9)), .inr (.inr (2, 12)), .inr (.inr (3, 8)), .inr (.inr (3, 12)), .inr (.inr (4, 9)), .inr (.inr (4, 10)), .inr (.inr (5, 8)), .inr (.inr (5, 10)), .inr (.inr (6, 8)), .inr (.inr (7, 8))],
    [.inr (.inl 11), .inr (.inr (1, 10)), .inr (.inr (2, 9)), .inr (.inr (3, 8)), .inr (.inr (5, 10)), .inr (.inr (7, 8))],
    [.inr (.inl 13), .inr (.inl 14), .inr (.inr (1, 12)), .inr (.inr (2, 12)), .inr (.inr (3, 12)), .inr (.inr (4, 9)), .inr (.inr (4, 10)), .inr (.inr (5, 8)), .inr (.inr (6, 8)), .inr (.inr (7, 8))],
    [.inr (.inr (7, 8))]]

set_option Elab.async false in
private theorem certificate_correct : ∀ j p,
    columns p j = ((certificate j).map relator).sum p := by
  intro j
  fin_cases j <;> decide +kernel

set_option Elab.async false in
private theorem pivot_correct : ∀ i j, columns (pivot i) j = if i = j then 1 else 0 := by
  intro i
  fin_cases i <;> decide +kernel

private theorem columns_mem (j : Fin 43) : columnsᵀ j ∈ relationSpace := by
  have he : columnsᵀ j = ((certificate j).map relator).sum := funext (certificate_correct j)
  rw [he]
  have hl (l : List Relation) : (l.map relator).sum ∈ relationSpace := by
    induction l with
    | nil => exact relationSpace.zero_mem
    | cons a l ih =>
      exact relationSpace.add_mem (Submodule.subset_span ⟨a, rfl⟩) ih
  exact hl _

private theorem columns_mulVec_mem (v : Fin 43 → ZMod 2) :
    columns.toLin' v ∈ relationSpace := by
  have he : columns.toLin' v = ∑ j, v j • columnsᵀ j := by
    ext p
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [he]
  exact relationSpace.sum_mem fun j _ => relationSpace.smul_mem (v j) (columns_mem j)

private theorem finrank_relationSpace_ge : 43 ≤ Module.finrank (ZMod 2) relationSpace := by
  let f : (Fin 43 → ZMod 2) →ₗ[ZMod 2] relationSpace :=
    columns.toLin'.codRestrict relationSpace columns_mulVec_mem
  have hf : Function.Injective f := by
    intro x y h
    have h' := congrArg (fun z : relationSpace => (z : Coordinates)) h
    change columns.mulVec x = columns.mulVec y at h'
    ext i
    have hi := congrFun h' (pivot i)
    simpa [Matrix.mulVec, dotProduct, pivot_correct] using hi
  simpa using LinearMap.finrank_le_finrank_of_injective (f := f) hf

/-- The geometric flag presentation has dimension at most twenty-one. -/
theorem flagQuotient_finrank_le_twenty_one : Module.finrank (ZMod 2) FlagQuotient ≤ 21 := by
  have hr := relationSpace.finrank_quotient_add_finrank
  have hd : Module.finrank (ZMod 2) Coordinates = 64 := by simp [Coordinates]
  have hl := finrank_relationSpace_ge
  change Module.finrank (ZMod 2) FlagQuotient + Module.finrank (ZMod 2) relationSpace = _ at hr
  omega
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl.FlagPresentation
