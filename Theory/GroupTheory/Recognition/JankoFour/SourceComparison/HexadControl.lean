module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.HexadOrbits
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Data

/-!
# Fixed hexads of a neighboring-pair stabilizer

Two words in the actual M22 generators fix the standard neighboring hexads.
A moving-bit witness for each other hexad proves that these are their only
common fixed hexads. Rank-three transitivity transports this statement to
any neighboring pair. Product-table lemmas keep the long words out of the
later finite and geometric reductions.

This is the plane fixed-point calculation used for the normalizer condition
in Aschbacher--Segev, Invent. Math. 105 (1991), (8.2), p.606.
-/
@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
open scoped Pointwise
namespace EdgeControl
open SourceIncidence.NativeHexads
private noncomputable def k : M22 := M22RepresentativeKernel.wordElement [0,1,0,1,0,2,0,2,0,2,0,1,0,1,0,1,0,2,0,2,0,2,0,1,1,0,1]
private noncomputable def first : M22 := k * generator 1 * generator 1 * generator 0 * generator 1 * k
private noncomputable def second : M22 := generator 1 * generator 0 * generator 1 * generator 0 * k
private def firstTable : Fin 22 → Fin 22 := ![5,2,1,3,21,9,0,4,19,6,20,12,13,16,8,7,11,14,18,17,10,15]
private def secondTable : Fin 22 → Fin 22 := ![14,1,2,18,15,16,11,4,6,5,3,8,17,0,13,7,9,19,10,12,20,21]
private def kTable : Fin 22 → Fin 22 := ![0,3,10,1,7,21,14,4,16,13,2,11,12,9,6,19,8,17,18,15,20,5]
private theorem k_apply (x : Fin 22) : k.val x=kTable x := by
  rw [k,M22RepresentativeKernel.wordElement_apply]
  revert x
  decide +kernel
attribute [local irreducible] k generator
private theorem product_table (u v : M22) (U V : Fin 22 → Fin 22)
    (hu : ∀ x, u.val x=U x) (hv : ∀ x, v.val x=V x) (x : Fin 22) :
    (u*v).val x=U (V x) :=
  (hu (v.val x)).trans (congrArg U (hv x))
private theorem first_apply (x : Fin 22) : first.val x=firstTable x := by
  have hc : ∀ y : Fin 22, kTable (table 1 (table 1 (table 0 (table 1 (kTable y)))))=firstTable y := by
    decide +kernel
  have h1 := product_table k (generator 1) _ _ k_apply (generator_apply 1)
  have h2 := product_table (k*generator 1) (generator 1) _ _ h1 (generator_apply 1)
  have h3 := product_table (k*generator 1*generator 1) (generator 0) _ _ h2 (generator_apply 0)
  have h4 := product_table (k*generator 1*generator 1*generator 0) (generator 1) _ _ h3 (generator_apply 1)
  have h5 := product_table (k*generator 1*generator 1*generator 0*generator 1) k _ _ h4 k_apply
  exact (h5 x).trans (hc x)
private theorem second_apply (x : Fin 22) : second.val x=secondTable x := by
  have hc : ∀ y : Fin 22, table 1 (table 0 (table 1 (table 0 (kTable y))))=secondTable y := by
    decide +kernel
  have h1 := product_table (generator 1) (generator 0) _ _ (generator_apply 1) (generator_apply 0)
  have h2 := product_table (generator 1*generator 0) (generator 1) _ _ h1 (generator_apply 1)
  have h3 := product_table (generator 1*generator 0*generator 1) (generator 0) _ _ h2 (generator_apply 0)
  have h4 := product_table (generator 1*generator 0*generator 1*generator 0) k _ _ h3 k_apply
  exact (h4 x).trans (hc x)
attribute [irreducible] first second
private theorem first_fixes : first • m22Hexad123=m22Hexad123 ∧ first • m22BlockAt 1=m22BlockAt 1 := by
  have h0 : m22BlockAt 0=m22Hexad123 := by decide +kernel
  rw [←h0]
  constructor <;> apply m22Perm_smul_blockAt_of_bits
  · intro x
    obtain ⟨y,rfl⟩ := first.val.surjective x
    rw [first.val.symm_apply_apply,first_apply]
    revert y
    decide +kernel
  · intro x
    obtain ⟨y,rfl⟩ := first.val.surjective x
    rw [first.val.symm_apply_apply,first_apply]
    revert y
    decide +kernel
private theorem second_fixes : second • m22Hexad123=m22Hexad123 ∧ second • m22BlockAt 1=m22BlockAt 1 := by
  have h0 : m22BlockAt 0=m22Hexad123 := by decide +kernel
  rw [←h0]
  constructor <;> apply m22Perm_smul_blockAt_of_bits
  · intro x
    obtain ⟨y,rfl⟩ := second.val.surjective x
    rw [second.val.symm_apply_apply,second_apply]
    revert y
    decide +kernel
  · intro x
    obtain ⟨y,rfl⟩ := second.val.surjective x
    rw [second.val.symm_apply_apply,second_apply]
    revert y
    decide +kernel
private def witness : Fin 77 → Fin 22 := ![0,0,0,0,5,1,1,1,1,0,1,0,0,0,1,0,1,0,1,1,1,0,0,1,1,0,1,1,1,0,1,1,1,1,1,0,0,0,5,4,0,0,4,6,0,4,5,0,0,0,4,4,4,4,0,0,4,7,0,0,0,5,0,0,0,0,0,5,6,5,4,7,5,0,4,0,0]
private def which : Fin 77 → Bool := ![false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false]
private theorem witness_moves : ∀ i : Fin 77, i=0 ∨ i=1 ∨
    (m22BlockMask i).testBit (witness i).val ≠ (m22BlockMask i).testBit
      ((if which i then secondTable else firstTable) (witness i)).val := by
  decide +kernel
private theorem common_fixed (i : Fin 77)
    (hf : ∀ x : Fin 22, (m22BlockMask i).testBit x.val=(m22BlockMask i).testBit (firstTable x).val)
    (hs : ∀ x : Fin 22, (m22BlockMask i).testBit x.val=(m22BlockMask i).testBit (secondTable x).val) :
      i=0 ∨ i=1 := by
  rcases witness_moves i with h0 | h1 | hm
  · exact Or.inl h0
  · exact Or.inr h1
  · have he : (m22BlockMask i).testBit (witness i).val = (m22BlockMask i).testBit
        ((if which i then secondTable else firstTable) (witness i)).val := by
      split <;> first | exact hs _ | exact hf _
    exact (hm he).elim

private theorem fixed_bits (g : M22) (T : Fin 22 → Fin 22)
    (hg : ∀ x, g.val x=T x) (i : Fin 77)
    (hfix : g • m22BlockAt i=m22BlockAt i) (x : Fin 22) :
    (m22BlockMask i).testBit x.val=(m22BlockMask i).testBit (T x).val := by
  have he : (x ∈ m22BlockAt i) ↔ (g.val x ∈ m22BlockAt i) := by
    change (m22BlockAt i).image g.val=m22BlockAt i at hfix
    constructor
    · intro hx
      rw [←hfix]
      exact Finset.mem_image_of_mem g.val hx
    · intro hx
      rw [←hfix] at hx
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hx
      exact g.val.injective he ▸ hu
  rw [hg x] at he
  apply Bool.eq_iff_iff.mpr
  simpa only [m22BlockAt,m22MaskBlock,Finset.mem_filter,Finset.mem_univ,true_and] using he

private theorem standard_fixed (C : Hexad)
    (hfix : ∀ g : M22, g • m22Hexad123=m22Hexad123 → g • m22BlockAt 1=m22BlockAt 1 →
      g • C.val=C.val) : C.val=m22Hexad123 ∨ C.val=m22BlockAt 1 := by
  obtain ⟨i,rfl⟩ := indexEquiv.surjective C
  have hf := hfix first first_fixes.1 first_fixes.2
  have hs := hfix second second_fixes.1 second_fixes.2
  rw [indexEquiv_val] at hf hs
  rcases common_fixed i (fixed_bits first firstTable first_apply i hf)
      (fixed_bits second secondTable second_apply i hs) with rfl | rfl
  · exact Or.inl (by rw [indexEquiv_val]; decide +kernel)
  · exact Or.inr (indexEquiv_val _)

/-- The simultaneous stabilizer of two neighboring hexads fixes exactly
those two hexads. Only two explicitly certified stabilizer words are needed. -/
theorem neighbor_fixed (A B C : Hexad) (hab : (B.val ∩ A.val).card=2)
    (hfix : ∀ g : M22, g • A.val=A.val → g • B.val=B.val → g • C.val=C.val) :
    C=A ∨ C=B := by
  obtain ⟨u,hu⟩ := exists_smul_m22Hexad123_eq A.property
  let B₀ := smulHexad u⁻¹ B
  have hb₀ : (B₀.val ∩ m22Hexad123).card=2 := by
    change ((u⁻¹ • B.val) ∩ m22Hexad123).card=2
    rw [←inv_smul_eq_iff.mpr hu.symm,inter_card_smul,hab]
  obtain ⟨v,hv,hvB⟩ := standard_transitive (indexEquiv 1) B₀ (by
    rw [indexEquiv_val,hb₀]; decide +kernel)
  let q := u*v
  have hqA : q • m22Hexad123=A.val := by rw [mul_smul,hv,hu]
  have hqB : q • m22BlockAt 1=B.val := by
    rw [indexEquiv_val] at hvB
    change v • m22BlockAt 1=u⁻¹ • B.val at hvB
    rw [mul_smul,hvB,smul_inv_smul]
  have hc := standard_fixed (smulHexad q⁻¹ C) (by
    intro g hgA hgB
    have hQA : (q*g*q⁻¹) • A.val=A.val := by
      rw [mul_smul,mul_smul,←hqA,inv_smul_smul,hgA]
    have hQB : (q*g*q⁻¹) • B.val=B.val := by
      rw [mul_smul,mul_smul,←hqB,inv_smul_smul,hgB]
    have hh := hfix (q*g*q⁻¹) hQA hQB
    have he := congrArg (q⁻¹ • ·) hh
    simpa only [smulHexad,mul_smul,inv_smul_smul] using he)
  rcases hc with hc | hc
  · left
    apply Subtype.ext
    have he := congrArg (q • ·) hc
    exact (smul_inv_smul q C.val).symm.trans (he.trans hqA)
  · right
    apply Subtype.ext
    have he := congrArg (q • ·) hc
    exact (smul_inv_smul q C.val).symm.trans (he.trans hqB)
end EdgeControl
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
