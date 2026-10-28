module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.PointRadicalRoots

/-!
# Unique transvection lifts modulo the central point radical

A nontrivial point-local SL₂ quotient element has at most one b₁ lift in
any coset of the central point radical. Multiplying a lift by a nonzero
central root produces a commuting pair with distinct moved lines, hence
a c₂ product, which cannot be another transvection. The distinction of
moved lines follows from the literal quotient matrix: an element whose
whole displacement lies in the fixed point has trivial quotient.

This is the central-kernel lifting input for the three-center argument in
Aschbacher--Smith G.4.9, printed p.341. The common-centralizer calculation
and existence of the desired same-coset commuting pair are separate steps.
-/

public noncomputable section

open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- The actual quotient is trivial when all displacement lies in its fixed point. -/
theorem pointQuotient_eq_one_of_movedSpace_le_point (t : pointLocal (F:=F))
    (ht : movedSpace t.val≤point F) : pointQuotient t=1 := by
  apply Subtype.ext
  ext i j
  have hm : t.val • (Pi.single (middleIndex j) (1:F) : Vector F)-Pi.single (middleIndex j) 1∈point F :=
    ht ⟨Pi.single (middleIndex j) 1,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  have he := congrFun hc (middleIndex i)
  fin_cases i <;> fin_cases j <;>
    simp [pointQuotient,pointQuotientMatrix,middleIndex,Matrix.submatrix,
      smul_eq_mulVec,Matrix.mulVec_single,e] at he ⊢ <;>
    first | exact sub_eq_zero.mp he.symm | exact he.symm

/-- In a central point-radical coset, a nontrivial quotient has at most one B1 lift. -/
theorem eq_of_isB1_of_central_radical_difference (a b : pointLocal (F:=F))
    (ha : IsB1 a.val) (hb : IsB1 b.val) (haq : pointQuotient a≠1)
    (hzQ : a⁻¹*b∈pointRadical) (hzc : a⁻¹*b∈Subgroup.center (pointLocal (F:=F))) : a=b := by
  let z := a⁻¹*b
  by_cases hz : z=1
  · have h := congrArg (fun t : pointLocal (F:=F) => a*t) hz
    simpa only [z,mul_inv_cancel_left,mul_one] using h.symm
  have hztype : IsB1 z.val := by
    obtain ⟨c,hc⟩ := (pointRadical_mem_center_iff (⟨z,hzQ⟩ : pointRadical (F:=F))).mp hzc
    change z=pointRadicalElement 0 0 c at hc
    have hc0 : c≠0 := by
      intro he
      apply hz
      rw [hc,he,pointRadicalElement_zero]
    rw [hc]
    exact pointRadicalElement_isB1 hc0
  have hzm : movedSpace z.val=point F := pointRadical_movedSpace_of_isB1 z hzQ hztype
  have hne : movedSpace a.val≠movedSpace z.val := by
    intro he
    apply haq
    exact pointQuotient_eq_one_of_movedSpace_le_point a (le_of_eq (he.trans hzm))
  have hcomm : Commute a z := (Subgroup.mem_center_iff.mp hzc a)
  have hc2 : IsC2 (a.val*z.val) :=
    isC2_product_of_commute_distinct_movedSpace (F:=F) a.val z.val ha hztype
      (hcomm.map (pointLocal (F:=F)).subtype) hne
  have he : a.val*z.val=b.val := by change (a*z).val=b.val; simp [z]
  rw [he] at hc2
  have h1 := hb.2
  have h2 := hc2.2.1
  omega

/-- Exact quotient formulation retaining the central-kernel condition. -/
theorem eq_of_isB1_same_pointQuotient (a b : pointLocal (F:=F))
    (ha : IsB1 a.val) (hb : IsB1 b.val) (haq : pointQuotient a≠1)
    (he : pointQuotient a=pointQuotient b)
    (hzc : a⁻¹*b∈Subgroup.center (pointLocal (F:=F))) : a=b := by
  apply eq_of_isB1_of_central_radical_difference a b ha hb haq ?_ hzc
  change pointQuotient (a⁻¹*b)=1
  rw [map_mul,map_inv,he,inv_mul_cancel]

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
