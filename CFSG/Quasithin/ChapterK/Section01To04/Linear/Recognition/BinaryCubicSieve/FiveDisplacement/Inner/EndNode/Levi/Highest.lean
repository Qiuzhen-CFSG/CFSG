module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Coordinates

/-!
# Restriction of a binary SL₅ local highest vector to the end-node Levi

The relative two-core has identity diagonal blocks and is a product of four
positive root transvections. Thus every upper-fixed vector lies in its fixed
space. The marked quotient preserves the literal remaining root operators,
so the three rank-one alternatives restrict without any field extension.

Source: Guralnick–Malle, Classification of 2F-modules II, Theorem 3.1,
the restricted highest-weight assertion in Proposition 4.7(2).
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition

namespace Levi

/-- The relative two-core fixes both diagonal blocks pointwise. -/
theorem radical_diagonal (e : Fin 2) (g : parabolic e) (hg : g ∈ radical e)
    (i j : Fin 5) (hij : label e j = label e i) :
    g.val.val i j = if i = j then 1 else 0 := by
  have hm : parabolicEquiv e g ∈ pCore 2 (triangularGroup (label e)) := by
    rw [← pCore_map_iso 2 (parabolicEquiv e)]
    exact Subgroup.mem_map_of_mem (parabolicEquiv e).toMonoidHom hg
  rw [← ker_diagonalAction_eq_twoCore (label e) (label_monotone e)] at hm
  have he := congrFun (congrFun (blockMatrix_eq_one_of_mem_ker (label e)
    (parabolicEquiv e g) hm (label e i)) ⟨i, rfl⟩) ⟨j, hij⟩
  simpa only [blockMatrix, Matrix.submatrix_apply, parabolicEquiv_coe, matrix,
    MulEquiv.symm_apply_apply, Matrix.one_apply, Subtype.mk.injEq] using he

private def radicalRow (e : Fin 2) (i : Fin 4) : Fin 5 :=
  if e = 0 then 0 else i.castSucc
private def radicalColumn (e : Fin 2) (i : Fin 4) : Fin 5 :=
  if e = 0 then i.succ else 4
private theorem radical_lt (e : Fin 2) (i : Fin 4) :
    radicalRow e i < radicalColumn e i := by revert e i; decide
private def radicalRoot (e : Fin 2) (i : Fin 4) (c : ZMod 2) : SL5TenDimensional.Group :=
  Matrix.SpecialLinearGroup.transvection (ne_of_lt (radical_lt e i)) c
private def radicalWord (e : Fin 2) (c : Fin 4 → ZMod 2) : SL5TenDimensional.Group :=
  radicalRoot e 0 (c 0) * radicalRoot e 1 (c 1) *
    radicalRoot e 2 (c 2) * radicalRoot e 3 (c 3)

private theorem radicalWord_apply (e : Fin 2) (c : Fin 4 → ZMod 2) (i j : Fin 5) :
    (radicalWord e c).val i j =
      if label e i < label e j then
        if e = 0 then c ⟨j.val - 1, by have := j.isLt; omega⟩
        else c ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
      else if i = j then 1 else 0 := by
  fin_cases e <;> fin_cases i <;> fin_cases j <;>
    simp [radicalWord, radicalRoot, radicalRow, radicalColumn, label, node,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single,
      Matrix.one_apply]

private theorem radical_eq_word (e : Fin 2) (g : parabolic e) (hg : g ∈ radical e) :
    g.val = radicalWord e (fun i => g.val.val (radicalRow e i) (radicalColumn e i)) := by
  apply Subtype.ext
  ext i j
  rw [radicalWord_apply]
  have hd := radical_diagonal e g hg
  have hz := (mem_parabolic_iff e g).mp g.property
  fin_cases e <;> fin_cases i <;> fin_cases j <;>
    simp [label, node, radicalRow, radicalColumn] <;>
    first | exact hd _ _ (by decide) | exact hz _ _ (by decide) (by decide)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- Upper-root fixedness already puts the original vector in the literal radical fixed space. -/
theorem mem_fixedSpace_of_upperFixed (e : Fin 2) {v : V}
    (hv : SL5TenDimensional.Classification.UpperFixed σ v) : v ∈ FixedSpace σ e := by
  have hroot (i : Fin 4) (c : ZMod 2) : σ (radicalRoot e i c) v = v := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp [radicalRoot, Matrix.SpecialLinearGroup.transvection_coeff_zero]
    · exact hv _ _ (radical_lt e i)
  intro g
  change σ g.val.val v = v
  rw [radical_eq_word e g.val g.property]
  simp only [radicalWord, map_mul, Module.End.mul_apply, hroot]

/-- The adjacent lower-root action retains the prescribed `includedRoot` marking. -/
theorem action_simpleLower (e : Fin 2) (i : Fin 3) (v : FixedSpace σ e) :
    (action σ e (FourSmallModules.simpleLower i) v : V) =
      σ (SL5TenDimensional.Classification.simpleLower (includedRoot e i)) v := by
  rw [FourSmallModules.simpleLower, action_root]
  congr 2
  fin_cases e <;> fin_cases i <;> rfl

/-- The adjacent upper-root action has the same marking. -/
theorem action_simpleUpper (e : Fin 2) (i : Fin 3) (v : FixedSpace σ e) :
    (action σ e (FourSmallModules.simpleUpper i) v : V) =
      σ (SL5TenDimensional.Classification.simpleUpper (includedRoot e i)) v := by
  rw [FourSmallModules.simpleUpper, action_root]
  congr 2
  fin_cases e <;> fin_cases i <;> rfl

/-- The Weyl generators are the same products of the marked root operators. -/
theorem action_simpleSwap (e : Fin 2) (i : Fin 3) (v : FixedSpace σ e) :
    (action σ e (FourSmallModules.simpleSwap i) v : V) =
      σ (SL5TenDimensional.Classification.simpleSwap (includedRoot e i)) v := by
  simp only [FourSmallModules.simpleSwap, map_mul, Module.End.mul_apply]
  rw [action_simpleLower, action_simpleUpper, action_simpleLower]
  simp only [SL5TenDimensional.Classification.simpleSwap, map_mul, Module.End.mul_apply]

/-- Restriction of the given highest vector, on the actual radical fixed-space carrier. -/
theorem localHighestVector_restrict (e : Fin 2) {J : Finset (Fin 4)} {v : V}
    (h : SL5TenDimensional.Classification.LocalHighestVector σ J v) :
    FourSmallModules.LocalHighestVector (action σ e) (restrictedSupport e J)
      ⟨v, mem_fixedSpace_of_upperFixed σ e h.upper_fixed⟩ := by
  constructor
  · intro i j hij
    apply Subtype.ext
    rw [action_root]
    have hij' : includedCoordinate e i < includedCoordinate e j := by
      fin_cases e <;> simpa [includedCoordinate] using hij
    exact h.upper_fixed _ _ hij'
  · intro i hi
    apply Subtype.ext
    rw [action_simpleSwap]
    exact h.inactive_fixed _ (by simpa [restrictedSupport] using hi)
  · intro i hi
    apply Subtype.ext
    change v + (action σ e (FourSmallModules.simpleSwap i) _ : V) +
      (action σ e (FourSmallModules.simpleLower i) _ : V) = 0
    rw [action_simpleSwap, action_simpleLower]
    exact h.active_relation _ (by simpa [restrictedSupport] using hi)

end Levi
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
