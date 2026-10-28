module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetCocycle.Certificate
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetResidual
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Cocycles detected by the native perfect sextet residual

The finite certificate controls generator values after subtracting a principal
cocycle from the sextet vector. The certified generator words contain an actual
Sylow two-subgroup. Averaging over its odd number of cosets then makes the
remaining cocycle principal. The two constraint words have odd order and lie
in the full perfect residual, including the cubic center of 3.A6.

This proves precisely the extension-detection input needed for the full-core
fixed-point bound in source 8.2.12, printed p.722, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad.Involutions MathieuCode.QuadraticActors
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
namespace Cocycle
set_option backward.isDefEq.respectTransparency false
def pack (c : cocycles cocodeRepresentation) : Slots → ZMod 2 :=
  fun i => coordinates (c.val (letter i.1)) i.2

private theorem action_coordinates (g : M24) (v : Cocode) :
    (pointMatrix g.val + 1).mulVecLin (coordinates v) = coordinates (cocodeRepresentation g v) := by
  rw [←displacementMatrix_point,Matrix.mulVecLin_add,LinearMap.add_apply,displacementMatrix_eq]
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    Matrix.mulVecLin_one]
  have hs : sectionMap (coordinates v) = v := LinearMap.congr_fun sectionMap_coordinates v
  rw [hs,map_sub]
  abel

private theorem head_rows (a : Fin 2) (p : M24) (c : cocycles cocodeRepresentation) :
    (Matrix.mulVec (fun (i : Fin 11) (j : Slots) => if j.1 = a then
      (pointMatrix p.val + 1) i j.2 else 0) (pack c)) =
      coordinates (cocodeRepresentation p (c.val (letter a))) := by
  funext i
  have h := congrFun (action_coordinates p (c.val (letter a))) i
  simpa only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,pack] using h

private theorem word_rows (p : M24) (w : List (Fin 2)) (c : cocycles cocodeRepresentation) :
    (wordRows p.val w).mulVec (pack c) =
      coordinates (cocodeRepresentation p (c.val (Sporadic.Mathieu.evalWord letter w))) := by
  induction w generalizing p with
  | nil =>
    have hzero : c.val 1 = 0 := by simpa using (c.property 1 1).symm
    simp [wordRows,Sporadic.Mathieu.evalWord,hzero]
  | cons a w ih =>
    have hp : (fun x => p.val (letterPoint a x)) = (p * letter a).val := by
      funext x
      rw [←letter_apply]
      rfl
    let A : Matrix (Fin 11) Slots (ZMod 2) := fun i j => if j.1 = a then (pointMatrix p.val + 1) i j.2 else 0
    change (A + wordRows (fun x => p.val (letterPoint a x)) w).mulVec (pack c) = _
    rw [Matrix.add_mulVec,hp,ih]
    have hh : A.mulVec (pack c) = _ := head_rows a p c
    rw [hh]
    change _ = coordinates (cocodeRepresentation p (c.val (letter a * Sporadic.Mathieu.evalWord letter w)))
    rw [c.property,map_add,map_add,map_mul,Module.End.mul_apply]
    exact add_comm _ _

theorem zero_of_word_values (c : cocycles cocodeRepresentation)
    (hc : ∀ i, c.val (Sporadic.Mathieu.evalWord letter (word i)) = 0)
    (hzero : coordinates (c.val (letter 0)) 0 = 0) :
    ∀ i, c.val (letter i) = 0 := by
  have ht : testMatrix.mulVecLin (pack c) = 0 := by
    ext i
    by_cases hi : (flat i).val < 21
    · have hh := congrFun (word_rows 1 (word (selected ⟨(flat i).val,hi⟩).1) c)
        (selected ⟨(flat i).val,hi⟩).2
      rw [hc] at hh
      change (wordRows id _).mulVec (pack c) _ = _ at hh
      simpa only [map_zero,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,
        testMatrix,hi,dif_pos,Pi.zero_apply] using hh
    · simp [Matrix.mulVec,dotProduct,testMatrix,hi,pack,hzero]
  have he : pack c = 0 := by
    have hh := congrArg inverseMatrix.mulVecLin ht
    rw [matrix_check,←LinearMap.comp_apply,←Matrix.mulVecLin_mul,inverse_check,
      Matrix.mulVecLin_one,LinearMap.id_apply,map_zero] at hh
    exact hh
  intro i
  apply coordinateEquiv.injective
  change coordinates (c.val (letter i)) = coordinates 0
  rw [map_zero]
  funext j
  exact congrFun he (i,j)

private theorem residual_eq_sign_kernel (S : Sextet) :
    solvableResidual (sextetStabilizer S) =
      (Atlas.Codes.hexSign.comp (SextetLayers.CoordinateTransport.nativeQuotient S)).ker := by
  let f := SextetLayers.CoordinateTransport.nativeQuotient S
  have he : solvableResidual Atlas.Codes.HexAutomorphisms = Atlas.Codes.hexSign.ker := by
    let : Group.IsPerfect Atlas.Codes.HexEvenAutomorphisms := Representation.Hexacode.even_isPerfect
    apply le_antisymm
    · intro x hx
      have hm := map_solvableResidual_le Atlas.Codes.hexSign (mem_map_of_mem Atlas.Codes.hexSign hx)
      rw [solvableResidual_eq_bot] at hm
      exact hm
    · exact le_solvableResidual_of_isPerfect Atlas.Codes.hexSign.ker
  have hk : f.ker ≤ solvableResidual (sextetStabilizer S) := by
    rw [←native_core_kernel]
    exact native_core_le_residual S
  have hm := map_solvableResidual_eq f (SextetLayers.CoordinateTransport.nativeQuotient_surjective S)
  rw [he] at hm
  change _ = Atlas.Codes.hexSign.ker.comap f
  rw [←hm,comap_map_eq_self hk]

private theorem odd_word_mem_residual (g : sextetStabilizer standardSextet) (hg : g^15=1) :
    g ∈ solvableResidual (sextetStabilizer standardSextet) := by
  rw [residual_eq_sign_kernel]
  let f := Atlas.Codes.hexSign.comp (SextetLayers.CoordinateTransport.nativeQuotient standardSextet)
  change f g = 1
  have hp : (f g)^15=1 := by rw [←map_pow,hg,map_one]
  rcases Int.units_eq_one_or (f g) with hh | hh
  · exact hh
  · norm_num [hh] at hp

private theorem eval_eq (w : List (Fin 2)) :
    (Sporadic.Mathieu.evalWord letter w).val = SylowNormalizer.standardWord w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (letter i).val * (Sporadic.Mathieu.evalWord letter w).val = _
    rw [ih]
    fin_cases i <;> rfl

set_option maxRecDepth 4096 in
private theorem word_stabilizes : ∀ i : Fin 4,
    standardSextet.parts.image (fun A => A.image (SylowNormalizer.standardWord (word i))) = standardSextet.parts := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem word_odd : ∀ i : Fin 4,
    (SylowNormalizer.standardWord (word i)) ^ 15 = 1 := by
  decide +kernel

private theorem words_mem : ∀ i, Sporadic.Mathieu.evalWord letter (word i) ∈
    (solvableResidual (sextetStabilizer standardSextet)).map (sextetStabilizer standardSextet).subtype := by
  intro i
  have hs : Sporadic.Mathieu.evalWord letter (word i) ∈ sextetStabilizer standardSextet := by
    change standardSextet.parts.image (fun A => A.image (Sporadic.Mathieu.evalWord letter (word i)).val) = standardSextet.parts
    rw [eval_eq]
    exact word_stabilizes i
  let g : sextetStabilizer standardSextet := ⟨Sporadic.Mathieu.evalWord letter (word i),hs⟩
  refine ⟨g,odd_word_mem_residual g ?_,rfl⟩
  apply Subtype.ext
  apply Subtype.ext
  change (Sporadic.Mathieu.evalWord letter (word i)).val ^ 15 = 1
  rw [eval_eq]
  exact word_odd i

private theorem normalization_coordinate :
    coordinates (cocodeRepresentation (letter 0) (sextetVector standardSextet) -
      sextetVector standardSextet) 0 = 1 := by
  have hv : coordinates (sextetVector standardSextet) = fun i : Fin 11 => bit 1041 i.val := by
    rw [sextetVector_eq standardSextet (show standardTetrad 0 ∈ standardSextet.parts from by decide)]
    change reduce (wordOfSet (standardTetrad 0)) = _
    decide +kernel
  have hh := congrFun (action_coordinates (letter 0) (sextetVector standardSextet)) 0
  rw [hv] at hh
  rw [map_sub,Pi.sub_apply,←hh,hv]
  decide +kernel

private def zeroSubgroup (c : cocycles cocodeRepresentation) : Subgroup M24 where
  carrier := {g | c.val g = 0}
  one_mem' := by simpa using (c.property 1 1).symm
  mul_mem' {a b} ha hb := by
    change c.val a = 0 at ha
    change c.val b = 0 at hb
    change c.val (a*b) = 0
    rw [c.property,hb,ha,map_zero,add_zero]
  inv_mem' {g} hg := by
    change c.val g = 0 at hg
    change c.val g⁻¹ = 0
    have h1 : c.val 1 = 0 := by simpa using (c.property 1 1).symm
    have hh := c.property g⁻¹ g
    simpa only [inv_mul_cancel,h1,hg,map_zero,zero_add] using hh.symm

private theorem sylow_zero_of_letters (c : cocycles cocodeRepresentation)
    (h : ∀ i, c.val (letter i) = 0) : ∀ g ∈ SextetCore.nativeSylow, c.val g = 0 := by
  have hw (w : List (Fin 2)) : Sporadic.Mathieu.evalWord letter w ∈ zeroSubgroup c := by
    induction w with
    | nil => exact (zeroSubgroup c).one_mem
    | cons i w ih => exact (zeroSubgroup c).mul_mem (h i) ih
  have hle : SylowNormalizer.candidate ≤ zeroSubgroup c := by
    apply (closure_le _).2
    rintro _ ⟨i,rfl⟩
    have he : SylowNormalizer.generator i =
        Sporadic.Mathieu.evalWord letter (SylowNormalizer.generatorWord i) := by
      apply Subtype.ext
      exact (SylowNormalizer.generatorPerm_eq_word i).trans (eval_eq _).symm
    rw [he]
    exact hw _
  exact fun g hg => hle hg

private theorem principal_of_sylow_zero (c : cocycles cocodeRepresentation)
    (P : Sylow 2 M24) (hP : ∀ g ∈ P, c.val g = 0) :
    ∃ v, principal cocodeRepresentation v = c := by
  classical
  let _ := Fintype.ofFinite (M24 ⧸ (P : Subgroup M24))
  let f : M24 ⧸ (P : Subgroup M24) → Cocode := Quotient.lift c.val (by
    intro a b hab
    have hp : a⁻¹*b ∈ P := QuotientGroup.leftRel_apply.mp hab
    have hh := c.property a (a⁻¹*b)
    simpa only [mul_inv_cancel_left,hP _ hp,map_zero,zero_add] using hh.symm)
  have hf (a : M24) (q : M24 ⧸ (P : Subgroup M24)) :
      f (a • q) = cocodeRepresentation a (f q) + c.val a := by
    induction q using Quotient.inductionOn with
    | h b => exact c.property a b
  have hn : Odd (Fintype.card (M24 ⧸ (P : Subgroup M24))) := by
    have hh := P.not_dvd_index
    rw [Subgroup.index,Nat.card_eq_fintype_card] at hh
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hh)
  let v := ∑ q, f q
  have hv (a : M24) : v = cocodeRepresentation a v + c.val a := by
    calc
      v = ∑ q, f (a • q) := (Equiv.sum_comp (MulAction.toPerm a) f).symm
      _ = cocodeRepresentation a v + c.val a := by
        simp only [hf,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,←map_sum,v]
        rw [←Nat.cast_smul_eq_nsmul (ZMod 2),hn.natCast_zmod_two,one_smul]
  refine ⟨-v,?_⟩
  apply Subtype.ext
  funext a
  change cocodeRepresentation a (-v) - -v = c.val a
  rw [map_neg,neg_sub_neg]
  exact sub_eq_iff_eq_add.mpr ((hv a).trans (add_comm _ _))

/-- A cocycle vanishing on the actual perfect sextet residual is principal.
No module-extension classification or splitting hypothesis is assumed. -/
theorem principal_of_standard_residual (c : cocycles cocodeRepresentation)
    (hc : ∀ g ∈ (solvableResidual (sextetStabilizer standardSextet)).map
      (sextetStabilizer standardSextet).subtype, c.val g = 0) :
    ∃ v, principal cocodeRepresentation v = c := by
  let v := coordinates (c.val (letter 0)) 0 • sextetVector standardSextet
  let d := c - principal cocodeRepresentation v
  have hdword (i : Fin 4) : d.val (Sporadic.Mathieu.evalWord letter (word i)) = 0 := by
    have hm := words_mem i
    have hfixed : cocodeRepresentation (Sporadic.Mathieu.evalWord letter (word i))
        (sextetVector standardSextet) = sextetVector standardSextet :=
      sextetVector_fixed standardSextet ⟨_,(map_subtype_le _) hm⟩
    change c.val _ - (cocodeRepresentation _ v - v) = 0
    rw [hc _ hm]
    simp only [v,map_smul,hfixed,sub_self]
  have hdzero : coordinates (d.val (letter 0)) 0 = 0 := by
    change coordinates (c.val (letter 0) - (cocodeRepresentation (letter 0) v - v)) 0 = 0
    simp only [v,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply]
    have hh := normalization_coordinate
    rw [map_sub,Pi.sub_apply] at hh
    simp only [smul_eq_mul]
    rw [←mul_sub,hh,mul_one,sub_self]
  obtain ⟨u,hu⟩ := principal_of_sylow_zero d SextetCore.nativeSylow
    (sylow_zero_of_letters d (zero_of_word_values d hdword hdzero))
  refine ⟨u+v,?_⟩
  rw [map_add,hu]
  exact sub_add_cancel c _

end Cocycle
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
