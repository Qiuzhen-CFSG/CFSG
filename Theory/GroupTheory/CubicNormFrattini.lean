module
public import Theory.GroupTheory.CyclicNormRetraction
public import Theory.Frattini.Intersection
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Tactic

/-!
# A cubic norm and an elementary Frattini four-group

Let B be an abelian two-group whose Frattini subgroup is an elementary
four-group V. An element r of order three normalizes B and moves a nontrivial
square z = j². An r-invariant character of exponent two detects j.

The cubic norm a of j is a nonidentity involution centralized by r. For
k = j⁻¹(rjr⁻¹), let X be the span of the r-conjugates of k. Its squares
contain z and its second r-conjugate, so Φ(X) = V. The odd-order element r
belongs to the two-residual of C_G(a); normality then puts k and X in that
same residual.

This gives the terminal Frattini witness needed in the original S₆-extension
branch of Aschbacher–Smith, Proposition 13.5.16, printed p.922. The source
consumer supplies B, r, j, and the character using its literal subgroup and
quotient maps.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup.CubicNormFrattini

private theorem cubic_four_orbit {A : Type*} [Group A] [IsKleinFour A]
    (α : MulAut A) (hα : α^3=1) (z : A) (hz : z≠1) (hm : α z≠z) :
    α (α z) = z * α z ∧ α (α z) ≠ z := by
  have hc (x : A) : α (α (α x)) = x := by
    have hh := congrArg (fun β : MulAut A => β x) hα
    exact hh
  have hz1 : α z≠1 := fun he => hz (α.injective (he.trans α.map_one.symm))
  have hz2 : α (α z)≠1 := fun he => hz1 (α.injective (he.trans α.map_one.symm))
  have h20 : α (α z)≠z := by
    intro he
    have hh := congrArg α he
    rw [hc] at hh
    exact hm hh.symm
  have h21 : α (α z)≠α z := fun he => hm (α.injective he)
  exact ⟨IsKleinFour.eq_mul_of_ne_all hz hz1 hm.symm hz2 h20 h21,h20⟩

variable {G : Type*} [Group G] [Finite G]

/-- A moved square in an elementary Frattini four produces the required
involution and two-subgroup inside its centralizer's two-residual. -/
theorem exists_involution_residual_frattini
    (B V : Subgroup G) [IsMulCommutative B] [IsElementaryAbelian 2 V]
    (hB : IsPGroup 2 B) (hPhi : (frattini B).map B.subtype = V)
    (hV : Nat.card V = 4) (r : G) (hr : orderOf r=3)
    (hrB : r∈normalizer (B:Set G)) (j : B) (hj : j^2≠1)
    (hm : r*(j:G)^2*r⁻¹≠(j:G)^2)
    {K : Type*} [Group K] (χ : B→*K) (hχ2 : ∀ k:K,k^2=1)
    (hχ : ∀ x:B,χ (B.normalizerMonoidHom ⟨r,hrB⟩ x)=χ x)
    (hχj : χ j≠1) :
    ∃ a:G,∃ X:Subgroup G, orderOf a=2 ∧ IsPGroup 2 X ∧
      X≤(pResidual 2 (centralizer ({a}:Set G))).map (centralizer ({a}:Set G)).subtype ∧
      (frattini X).map X.subtype=V := by
  let α : MulAut B := B.normalizerMonoidHom ⟨r,hrB⟩
  have hr3 : r^3=1 := hr ▸ pow_orderOf_eq_one r
  have hα : α^3=1 := by
    change (B.normalizerMonoidHom ⟨r,hrB⟩)^3=1
    rw [←map_pow,show (⟨r,hrB⟩ : normalizer (B:Set G))^3=1 from Subtype.ext hr3,map_one]
  have hrV : r∈normalizer (V:Set G) := by
    rw [←hPhi]
    exact normalizer_le_normalizer_characteristic_image B (frattini B) hrB
  let β : MulAut V := V.normalizerMonoidHom ⟨r,hrV⟩
  have hβ : β^3=1 := by
    change (V.normalizerMonoidHom ⟨r,hrV⟩)^3=1
    rw [←map_pow,show (⟨r,hrV⟩ : normalizer (V:Set G))^3=1 from Subtype.ext hr3,map_one]
  let : Fact (IsPGroup 2 B) := ⟨hB⟩
  have hzV : (j:G)^2∈V := by
    rw [←hPhi]
    exact mem_map_of_mem B.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) j)
  let z : V := ⟨(j:G)^2,hzV⟩
  have hz : z≠1 := by intro he; exact hj (Subtype.ext (congrArg (fun x:V => (x:G)) he))
  have hm' : β z≠z := fun he => hm (congrArg Subtype.val he)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour V := ⟨hV,IsElementaryAbelian.exponent_eq_prime⟩
  have horb := cubic_four_orbit β hβ z hz hm'
  have horbB : α (α (j^2)) = j^2 * α (j^2) :=
    Subtype.ext (congrArg (fun x:V => (x:G)) horb.1)
  let aB : B := MulAut.cyclicNorm α 3 j
  have ha2 : aB^2=1 := by
    change (MulAut.cyclicNorm α 3 j)^2=1
    rw [←map_pow]
    have hn : MulAut.cyclicNorm α 3 (j^2)=j^2*α (j^2)*α (α (j^2)) := by
      simp [MulAut.cyclicNorm_apply,Finset.prod_range_succ,pow_two]
    rw [hn,horbB]
    have hzsq' : (j^2)^2=1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (G:=G) (A:=V) _ hzV
    calc
      j^2*α (j^2)*(j^2*α (j^2))=(j^2)^2*(α (j^2))^2 := by rw [←pow_two,mul_pow]
      _=1 := by rw [←map_pow,hzsq',map_one,mul_one]
  have hχa : χ aB=χ j := by
    have hn : aB=j*α j*α (α j) := by simp [aB,MulAut.cyclicNorm_apply,Finset.prod_range_succ,pow_two]
    rw [hn,map_mul,map_mul,hχ,hχ,hχ]
    calc
      χ j*χ j*χ j=(χ j)^2*χ j := by rw [pow_two]
      _=χ j := by rw [hχ2,one_mul]
  have ha1 : aB≠1 := fun he => hχj (by rw [←hχa,he,map_one])
  have haFix : α aB=aB := MulAut.cyclicNorm_fixed α hα j
  let a:G := aB
  let k:B := j⁻¹*α j
  let X:Subgroup G := conjugateSpanBy (zpowers (k:G)) (zpowers r)
  have hXB : X≤B := conjugateSpanBy_le (zpowers_le.mpr k.property) (zpowers_le.mpr hrB)
  have hXtwo : IsPGroup 2 X := hB.to_le hXB
  let : Fact (IsPGroup 2 X) := ⟨hXtwo⟩
  have hkX : (k:G)∈X := le_conjugateSpanBy _ _ (mem_zpowers _)
  have hrkX : r*(k:G)*r⁻¹∈X := subset_closure ⟨r,mem_zpowers r,k,mem_zpowers _,rfl⟩
  have hk2 : (k:G)^2=(β (β z):G) := by
    have hi : (j^2)⁻¹=j^2 := by
      have hh : (j^2)^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) (G:=G) (A:=V) _ hzV)
      exact inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hh)
    have he : k^2=α (α (j^2)) := by
      rw [horbB]
      change (j⁻¹*α j)^2=j^2*α (j^2)
      rw [mul_pow,inv_pow,←map_pow,hi]
    exact congrArg Subtype.val he
  have hrk2 : (r*(k:G)*r⁻¹)^2=(z:G) := by
    calc
      (r*(k:G)*r⁻¹)^2=r*(k:G)^2*r⁻¹ := by simp [pow_two,mul_assoc]
      _ = (β (β (β z)):G) := by rw [hk2]; rfl
      _ = (z:G) := congrArg Subtype.val (congrArg (fun f:MulAut V=>f z) hβ)
  have hPhiX : (frattini X).map X.subtype=V := by
    apply le_antisymm
    · exact (frattini_image_le_of_le hXB hB).trans_eq hPhi
    · have hzΦ : (z:G)∈(frattini X).map X.subtype := by
        rw [←hrk2]
        exact mem_map_of_mem X.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨_,hrkX⟩:X))
      have hz2Φ : (β (β z):G)∈(frattini X).map X.subtype := by
        rw [←hk2]
        exact mem_map_of_mem X.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨_,hkX⟩:X))
      intro v hv
      classical
      let := Fintype.ofFinite V
      have hcases := IsKleinFour.eq_finset_univ hz
        (fun he=>hz (β.injective ((β.injective (he.trans β.map_one.symm)).trans β.map_one.symm))) horb.2.symm
      have hv' : (⟨v,hv⟩:V)∈({z*β (β z),z,β (β z),1}:Finset V) := hcases.symm ▸ Finset.mem_univ _
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
      rcases hv' with he|he|he|he
      · have hh : v=(z:G)*(β (β z):G) := congrArg (fun w:V => (w:G)) he
        rw [hh]
        exact ((frattini X).map X.subtype).mul_mem hzΦ hz2Φ
      · have hh : v=(z:G) := congrArg (fun w:V => (w:G)) he
        rw [hh]
        exact hzΦ
      · have hh : v=(β (β z):G) := congrArg (fun w:V => (w:G)) he
        rw [hh]
        exact hz2Φ
      · have hh : v=1 := congrArg (fun w:V => (w:G)) he
        rw [hh]
        exact ((frattini X).map X.subtype).one_mem
  let C:=centralizer ({a}:Set G)
  have hBC : B≤C := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨x,hx⟩:B) aB)
  have hrC : r∈C := by
    apply mem_centralizer_singleton_iff.mpr
    have hh:=congrArg (fun x:B=>(x:G)*r) haFix
    change (r*(aB:G)*r⁻¹)*r=(aB:G)*r at hh
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  let E:Subgroup G:=(pResidual 2 C).map C.subtype
  have hrE : r∈E := by
    refine ⟨⟨r,hrC⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    rw [Subgroup.orderOf_mk,hr]
    decide
  have hCE : C≤normalizer (E:Set G) := by
    exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hkE : (k:G)∈E := by
    have hh:=mem_normalizer_iff.mp (hCE (C.inv_mem (hBC j.property))) r
    have hc:=hh.mp hrE
    have he := E.mul_mem hc (E.inv_mem hrE)
    change (j:G)⁻¹*(r*(j:G)*r⁻¹)∈E
    simpa only [inv_inv,mul_assoc] using he
  refine ⟨a,X,?_,hXtwo,conjugateSpanBy_le (zpowers_le.mpr hkE) (zpowers_le.mpr (hCE hrC)),hPhiX⟩
  exact orderOf_eq_prime (congrArg Subtype.val ha2) (fun he=>ha1 (Subtype.ext he))
end Subgroup.CubicNormFrattini
