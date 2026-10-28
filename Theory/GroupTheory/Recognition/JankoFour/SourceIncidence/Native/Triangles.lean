module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.HexadOrbits
public import Theory.Mathieu.M22.Properties.Design

/-!
# Triangle transpositions in the full hexad design group

Fix the standard hexad and an adjacent hexad. Among the old 77 hexads,
47 are adjacent to both. Short words in the two published hexad-stabilizer
generators and the published odd design involution interchange the second
hexad and each possible third one. The Lean kernel checks their actions on
the original point sets. The established rank-three action transports the
first two hexads, so the same literal full design group interchanges any
two triangle vertices while fixing the third.

The full design group is essential: the inner M22 stabilizer splits one
of these interchange configurations. The source plane projection is onto
the full design group, so this uses precisely the available source group.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.6)(2), p.601.
The full finite probe took 56.05 s including import preparation and used
2,268,592 KiB peak RSS. Existing hexads and generators are reused unchanged.
-/

@[expose] public section
open Sporadic.Mathieu
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeTriangles
open SourceCycleBase NativeHexads
private noncomputable def gen : Fin 3 → m22DesignAut :=
  ![M22ValueBound.Concrete.inclusion (generator 0),
    M22ValueBound.Concrete.inclusion (generator 1),
    ⟨m22OddPairSwap,m22OddPairSwap_mem_designAut⟩]
private def genTable : Fin 3 → Fin 22 → Fin 22 :=
  ![table 0,table 1,fun x => m22OddPairSwap x]
private theorem gen_apply (i : Fin 3) (x : Fin 22) : (gen i).val x = genTable i x := by
  fin_cases i
  · exact generator_apply 0 x
  · exact generator_apply 1 x
  · rfl
private theorem gen_fixes (i : Fin 3) : gen i • m22Hexad123 = m22Hexad123 := by
  fin_cases i
  · exact generator_fixes 0
  · exact generator_fixes 1
  · change m22OddPairSwap • m22Hexad123 = m22Hexad123
    decide +kernel

private def words : Fin 77 → List (Fin 3) :=
  ![[],
    [],
    [1,1,1,2,1,1,1],
    [1,1,1],
    [2,1,1,1,2],
    [1,1,2,1,1,1,1],
    [2,0,1,1,0,1,0],
    [0,1,1,1,1,1,0,1,0],
    [0,1,1,0,1,0,2],
    [0,1,1,0,2,1,2],
    [1,1,1,1,1,2,0,2,1],
    [0,2,0,1,1,0,1],
    [1,1,0,1,0,2,0],
    [1,1,2,0,2,1,2],
    [1,1,0,1,1,1,1],
    [2,1,1,0,1,1,1,1,2],
    [2,1,1,0,1,2,0,2,0],
    [1,1,2,0,2,1,1,1,1],
    [1,1,0,2,1,2,0],
    [1,1,1,1,1,0,1],
    [2,1,1,1,1,1,0,1,2],
    [1,1,1,1,0,1,1],
    [2,1,2,0,1,1,0],
    [1,0,1,0,2,0,1],
    [1,2,0,1,1,0,2],
    [1,0,1,1,1,2,1,1,0],
    [0,2,1,1,2,0,1,0,1,0],
    [0,1,2,1,1,1,1,1,0],
    [0,1,2,1,0,2,0,1,2],
    [1,2,1,1,1,1,1],
    [1,1,1,1,2,1,1],
    [2,1,1,2,0,1,0,1],
    [1,1,2,0,1,0,1,2],
    [0,2,1,2,0,1,1],
    [0,1,1,1,1,2,1,1,0],
    [1,2,1,1,2,1,1,1],
    [1,1,2,1,2,1,0,1],
    [0,1,0,1,0,1,1,0,1],
    [1,2,1,0,1,2,0,1],
    [2,1,0,1,0,2,1,0],
    [],
    [],
    [0,1,1,2,0,1,1,0],
    [],
    [2,0,1,2,1,0,1],
    [1,1,2,1,1,2,0],
    [],
    [],
    [],
    [],
    [],
    [1,1,2,0,1,1],
    [],
    [],
    [],
    [2,0,1,1,2,1,1],
    [1,2,1,0,1,2,0],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [1,0,1,0,1,1,0,1,0],
    [],
    [],
    [],
    [],
    [2,0,1,2,1,1,1,0,1],
    [1,0,2,1,2,0,1],
    [],
    [],
    [],
    [],
    [],
    []]
private noncomputable def wordElement : List (Fin 3) → m22DesignAut
  | [] => 1
  | k::w => gen k * wordElement w
private def wordApply : List (Fin 3) → Fin 22 → Fin 22
  | [] => id
  | k::w => fun x => genTable k (wordApply w x)
private theorem word_apply (w : List (Fin 3)) (x : Fin 22) :
    (wordElement w).val x = wordApply w x := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change (gen k).val ((wordElement w).val x) = _
    rw [gen_apply,ih]
    rfl
private theorem word_fixes (w : List (Fin 3)) : wordElement w • m22Hexad123 = m22Hexad123 := by
  induction w with
  | nil => exact one_smul _ _
  | cons k w ih =>
    change (gen k * wordElement w) • m22Hexad123 = _
    rw [mul_smul,ih,gen_fixes]

private theorem swap_check (i : Fin 77)
    (h0 : (m22BlockAt i ∩ m22Hexad123).card = 2)
    (h1 : (m22BlockAt i ∩ m22BlockAt 1).card = 2) :
    (m22BlockAt 1).image (wordApply (words i)) = m22BlockAt i ∧
    (m22BlockAt i).image (wordApply (words i)) = m22BlockAt 1 := by
  revert i; decide +kernel

private theorem standard_swap (C : Hexad)
    (h0 : (C.val ∩ m22Hexad123).card = 2)
    (h1 : (C.val ∩ m22BlockAt 1).card = 2) :
    ∃ g : m22DesignAut, g • m22Hexad123 = m22Hexad123 ∧
      g • m22BlockAt 1 = C.val ∧ g • C.val = m22BlockAt 1 := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp C.property
  rw [←hi] at h0 h1 ⊢
  refine ⟨wordElement (words i),word_fixes _,?_,?_⟩
  all_goals
    change Finset.image (wordElement (words i)).val _ = _
    rw [show (wordElement (words i)).val = wordApply (words i) from funext (word_apply _)]
  · exact (swap_check i h0 h1).1
  · exact (swap_check i h0 h1).2

/-- A literal full-design element fixes the first hexad and interchanges the other
two vertices of any triangle in the hexad adjacency graph. -/
theorem swap (A B C : Hexad)
    (hAB : (B.val ∩ A.val).card = 2) (hAC : (C.val ∩ A.val).card = 2)
    (hBC : (C.val ∩ B.val).card = 2) :
    ∃ g : m22DesignAut, g • A.val = A.val ∧ g • B.val = C.val ∧ g • C.val = B.val := by
  obtain ⟨k,hk⟩ := exists_smul_m22Hexad123_eq A.property
  let B' := smulHexad k⁻¹ B
  let C' := smulHexad k⁻¹ C
  have b : (B'.val ∩ m22Hexad123).card = 2 := by
    change ((k⁻¹ • B.val) ∩ m22Hexad123).card = 2
    rw [←inv_smul_eq_iff.mpr hk.symm,inter_card_smul,hAB]
  have c : (C'.val ∩ m22Hexad123).card = 2 := by
    change ((k⁻¹ • C.val) ∩ m22Hexad123).card = 2
    rw [←inv_smul_eq_iff.mpr hk.symm,inter_card_smul,hAC]
  let B₁ : Hexad := ⟨m22BlockAt 1,Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨s,hs,hsB⟩ := standard_transitive B' B₁ (by
    rw [b]; exact (by decide +kernel : (m22BlockAt 1 ∩ m22Hexad123).card = 2).symm)
  have c0 : ((smulHexad s C').val ∩ m22Hexad123).card = 2 := by
    change ((s • C'.val) ∩ m22Hexad123).card = 2
    rw [←hs,inter_card_smul]
    exact c
  have c1 : ((smulHexad s C').val ∩ m22BlockAt 1).card = 2 := by
    change ((s • C'.val) ∩ B₁.val).card = 2
    rw [←hsB,inter_card_smul]
    exact (inter_card_smul k⁻¹ C.val B.val).trans hBC
  obtain ⟨t,ht,htB,htC⟩ := standard_swap (smulHexad s C') c0 c1
  let k' := M22ValueBound.Concrete.inclusion k
  let s' := M22ValueBound.Concrete.inclusion s
  let g := k'*s'⁻¹*t*s'*k'⁻¹
  have hk' : k' • m22Hexad123 = A.val := hk
  have hs' : s' • m22Hexad123 = m22Hexad123 := hs
  have hsB' : s' • (k'⁻¹ • B.val) = m22BlockAt 1 := hsB
  have htB' : t • m22BlockAt 1 = s' • (k'⁻¹ • C.val) := htB
  have htC' : t • (s' • (k'⁻¹ • C.val)) = m22BlockAt 1 := htC
  refine ⟨g,?_,?_,?_⟩
  · change (k'*s'⁻¹*t*s'*k'⁻¹) • A.val = A.val
    rw [←hk',mul_smul,mul_smul,mul_smul,mul_smul,inv_smul_smul,hs',ht,
      inv_smul_eq_iff.mpr hs'.symm]
  · change (k'*s'⁻¹*t*s'*k'⁻¹) • B.val = C.val
    rw [mul_smul,mul_smul,mul_smul,mul_smul,hsB',htB',inv_smul_smul,smul_inv_smul]
  · change (k'*s'⁻¹*t*s'*k'⁻¹) • C.val = B.val
    rw [mul_smul,mul_smul,mul_smul,mul_smul,htC',←hsB',inv_smul_smul,smul_inv_smul]
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeTriangles
