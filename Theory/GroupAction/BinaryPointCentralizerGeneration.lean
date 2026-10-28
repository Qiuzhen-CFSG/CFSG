module
public import Theory.LinearAlgebra.BinaryTwoTransitivity
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.OddInvolutionFrattini

/-!
# Point-centralizer generation in a binary linear action

Let K induce the full linear group on an elementary abelian two-group E.
If a subgroup B of E properly contains a point P of order two, the K-elements
centralizing P generate all of E from B. Two-transitivity on the nonzero
binary vectors fixes the point generator and moves a second vector to each
remaining nonzero vector. The resulting conjugates belong to the literal
ambient subgroup span.

Source: the natural-module exclusion in Aschbacher--Smith, 14.7.37(2),
printed p.1059 of refs/quasithin.pdf. The proof works in every dimension.
-/

public noncomputable section
open Subgroup OddInvolutionFrattini
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]
/-- In a full binary linear action, the point centralizer's orbit of any
plane containing that point generates the entire module. -/
theorem conjugateSpan_eq_of_full_binary_point_centralizer
    (E B P K : Subgroup G) [IsElementaryAbelian 2 E]
    (hBE : B ≤ E) (hPB : P < B) (hP : Nat.card P = 2)
    (hKE : K ≤ normalizer (E : Set G))
    (hfull : Function.Surjective (conjugation K E hKE)) :
    conjugateSpanBy B (K ⊓ centralizer (P : Set G)) = E := by
  let S := conjugateSpanBy B (K ⊓ centralizer (P : Set G))
  have hBS : B ≤ S := le_conjugateSpanBy _ _
  obtain ⟨p,hp,hall⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hP
  obtain ⟨b,hb,hbP⟩ := SetLike.not_le_iff_exists.mp hPB.not_ge
  let pE : E := ⟨p,hBE (hPB.le p.property)⟩
  let bE : E := ⟨b,hBE hb⟩
  have hp0 : Additive.ofMul pE ≠ 0 := by
    intro he
    apply hp
    exact Subtype.ext (congrArg (fun x : Additive E => (x.toMul : G)) he)
  have hb0 : Additive.ofMul bE ≠ 0 := by
    intro he
    apply hbP
    have hh : b=1 := congrArg (fun x : Additive E => (x.toMul : G)) he
    rw [hh]; exact P.one_mem
  have hpb : Additive.ofMul pE ≠ Additive.ofMul bE := by
    intro he
    have hh : (p:G)=b := congrArg (fun x : Additive E => (x.toMul : G)) he
    exact hbP (hh ▸ p.property)
  apply le_antisymm (conjugateSpanBy_le hBE (inf_le_left.trans hKE))
  intro x hx
  by_cases hx0 : x=1
  · rw [hx0]; exact S.one_mem
  by_cases hxp : x=(p:G)
  · rw [hxp]; exact hBS (hPB.le p.property)
  let xE : E := ⟨x,hx⟩
  have hx' : Additive.ofMul xE ≠ 0 :=
    fun he => hx0 (congrArg (fun x : Additive E => (x.toMul : G)) he)
  have hpx : Additive.ofMul pE ≠ Additive.ofMul xE :=
    fun he => hxp (congrArg (fun x : Additive E => (x.toMul : G)) he).symm
  obtain ⟨f,hfp,hfb⟩ := BinaryLinear.exists_linearEquiv_pair
    (Additive.ofMul pE) (Additive.ofMul bE) (Additive.ofMul pE) (Additive.ofMul xE)
    hp0 hb0 hp0 hx' hpb hpx
  let a : MulAut E := f.toAddEquiv.toMultiplicative
  obtain ⟨k,hk⟩ := hfull a
  have hfix : (k:G)*(p:G)*(k:G)⁻¹ = p := by
    have hh := congrArg (fun r : MulAut E => (r pE : G)) hk
    change (k:G)*(p:G)*(k:G)⁻¹ = (f (Additive.ofMul pE)).toMul at hh
    exact hh.trans (congrArg (fun x : Additive E => (x.toMul : G)) hfp)
  have hkc : (k:G) ∈ centralizer (P:Set G) := by
    intro y hy
    by_cases hy0 : y=1
    · simp [hy0]
    have hyp : (⟨y,hy⟩ : P)=p := hall _ (fun he => hy0 (congrArg Subtype.val he))
    have hy' : y=(p:G) := congrArg Subtype.val hyp
    rw [hy']
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hm : (k:G)*b*(k:G)⁻¹ ∈ S :=
    (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy B (K ⊓ centralizer (P : Set G)) ⟨k.property,hkc⟩) b).mp (hBS hb)
  have hmove : (k:G)*b*(k:G)⁻¹=x := by
    have hh := congrArg (fun r : MulAut E => (r bE : G)) hk
    change (k:G)*b*(k:G)⁻¹ = (f (Additive.ofMul bE)).toMul at hh
    exact hh.trans (congrArg (fun x : Additive E => (x.toMul : G)) hfb)
  rwa [hmove] at hm
end Subgroup
