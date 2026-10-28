module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenPointTransvections

/-!
# Correcting the original point transvection lifts inside the same kernel

The point-core lift has square x. An element y of the original sixteen
outside the fixed eight satisfies c y c⁻¹=x y, so y c is an involution.
This correction belongs to the original kernel, hence preserves both the
literal normalizer quotient and every conjugation operator on that kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Original source point-core actors have involutory representatives in
their same normalizer/kernel coset, preserving their full action on A. -/
theorem TypeAt.sixteen_involutory_transvection (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A=16)
    (hCA : centralizer (A:Set G)=A)
    (hpure : ∀ x∈A,x≠1 → IsConj x z)
    (hpoints : ∀ x∈A,x≠1 →
      Nat.card (A⊓(involutionCentralizer x).pCoreIn 2:Subgroup G)=8)
    (x : G) (hx : x∈A) (hx1 : x≠1) :
    ∃ c y s : G, orderOf c=4 ∧ c^2=x ∧
      c∈(involutionCentralizer x).pCoreIn 2 ∧
      y∈A ∧ y∉(involutionCentralizer x).pCoreIn 2 ∧ s=y*c ∧ orderOf s=2 ∧
      ∃ (hcN : c∈normalizer (A:Set G)) (hsN : s∈normalizer (A:Set G)),
        (QuotientGroup.mk (⟨s,hsN⟩:normalizer (A:Set G)) :
          normalizer (A:Set G) ⧸ A.subgroupOf (normalizer (A:Set G)))=
          QuotientGroup.mk (⟨c,hcN⟩:normalizer (A:Set G)) ∧
        (∀ a∈A,s*a*s⁻¹=c*a*c⁻¹) ∧
        A⊓involutionCentralizer s=A⊓(involutionCentralizer x).pCoreIn 2 ∧
        (∀ a∈A⊓(involutionCentralizer x).pCoreIn 2,s*a*s⁻¹=a) ∧
        (∀ a∈A,a∉(involutionCentralizer x).pCoreIn 2 → s*a*s⁻¹=x*a) := by
  obtain ⟨c,hc4,hc2,hcQ,hcN,hfixed,hfix,hmove⟩ :=
    h.sixteen_point_transvection A hA hCA hpure hpoints x hx hx1
  obtain ⟨y,hy,hyQ⟩ : ∃ y∈A,y∉(involutionCentralizer x).pCoreIn 2 := by
    by_contra! hn
    have he : A⊓(involutionCentralizer x).pCoreIn 2=A := inf_eq_left.mpr hn
    have hh := hpoints x hx hx1
    rw [he,hA] at hh
    contradiction
  let s := y*c
  have hsN : s∈normalizer (A:Set G) :=
    (normalizer (A:Set G)).mul_mem (A.le_normalizer hy) hcN
  have hact (a : G) (ha : a∈A) : s*a*s⁻¹=c*a*c⁻¹ := by
    have hm : c*a*c⁻¹∈A := (mem_normalizer_iff.mp hcN a).mp ha
    calc
      s*a*s⁻¹=y*(c*a*c⁻¹)*y⁻¹ := by dsimp [s]; group
      _=(c*a*c⁻¹)*y*y⁻¹ := by rw [setLike_mul_comm hy hm]
      _=c*a*c⁻¹ := mul_inv_cancel_right _ _
  have hs2 : s^2=1 := by
    have hy2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) y hy
    have hx2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx
    calc
      s^2=y*(c*y*c⁻¹)*c^2 := by dsimp [s]; simp only [pow_two]; group
      _=y*(x*y)*x := by rw [hc2,hmove y hy hyQ]
      _=x*x := by rw [←mul_assoc y x y,setLike_mul_comm hy hx,mul_assoc x y y,←pow_two,hy2,mul_one]
      _=1 := by simpa only [pow_two] using hx2
  have hs1 : s≠1 := by
    intro hs
    have he := hact y hy
    rw [hs,one_mul,inv_one,mul_one,hmove y hy hyQ] at he
    exact hx1 (mul_right_cancel (show x*y=1*y by simpa using he.symm))
  refine ⟨c,y,s,hc4,hc2,hcQ,hy,hyQ,rfl,orderOf_eq_prime hs2 hs1,hcN,hsN,?_,hact,?_,?_,?_⟩
  · let q := QuotientGroup.mk' (A.subgroupOf (normalizer (A:Set G)))
    have hyN : y∈normalizer (A:Set G) := A.le_normalizer hy
    have hqy : q ⟨y,hyN⟩=1 := (QuotientGroup.eq_one_iff _).mpr hy
    change q ((⟨y,hyN⟩:normalizer (A:Set G))*⟨c,hcN⟩)=q ⟨c,hcN⟩
    rw [map_mul,hqy,one_mul]
  · rw [←hfixed]
    ext a
    constructor
    · intro ha
      refine ⟨ha.1,mem_centralizer_singleton_iff.mpr ?_⟩
      have hh : s*a*s⁻¹=a := by
        rw [←mem_centralizer_singleton_iff.mp ha.2,mul_inv_cancel_right]
      exact (mul_inv_eq_iff_eq_mul.mp ((hact a ha.1).symm.trans hh)).symm
    · intro ha
      refine ⟨ha.1,mem_centralizer_singleton_iff.mpr ?_⟩
      have hh := mem_centralizer_singleton_iff.mp ha.2
      have he : c*a*c⁻¹=a := by rw [←hh,mul_inv_cancel_right]
      exact (mul_inv_eq_iff_eq_mul.mp ((hact a ha.1).trans he)).symm
  · intro a ha
    rw [hact a ha.1,hfix a ha]
  · intro a ha hn
    rw [hact a ha,hmove a ha hn]

end CFSG.Quasithin.HigmanSims
