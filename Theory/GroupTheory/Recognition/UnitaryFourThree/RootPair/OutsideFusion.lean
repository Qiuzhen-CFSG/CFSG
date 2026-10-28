module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.OutsideFusion.Reflection
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneFusion

/-!
# Outside-root involution fusion in the actual Sylow subgroup

A genuine involution in the original core outside the root product has
trivial cocycles on that product. Since the root product has index two
in the original Sylow subgroup, all involutions in its other coset are
conjugate by the root product to this core involution. The root product
normalizes the core, so every Sylow involution belongs to the root product
or the core. Their already established fusion, followed by Sylow
conjugacy, proves ambient involution fusion from the original IsType data.

Source: Aschbacher, *Sporadic Groups*, Lemma45.5(4), printed p.244,
using Exercise 2.8 and the earlier45.3(4).
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

theorem outside_R_conjugate_reflection (h : IsType z) (s : G)
    (hs : s∈core z) (hsA : s∉P.leftCore) (hs2 : s^2=1)
    (v : G) (hvT : v∈P.T) (hv2 : v^2=1) (hvR : v∉P.R) :
    ∃ r∈P.R, r*v*r⁻¹=s := by
  have hsR : s∉P.R := fun hsr => hsA ((P.R_inf_core h).le ⟨hsr,hs⟩)
  let V : P.T := ⟨v,hvT⟩
  let S : P.T := ⟨s,mem_sup_right hs⟩
  let A := P.R.subgroupOf P.T
  have hi : A.index=2 := by
    have hh := A.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show P.R≤P.T from le_sup_left)).toEquiv,
      P.R_card h,P.T_card h] at hh
    omega
  have hcoset : v*s⁻¹∈P.R := by
    exact (show V*S⁻¹∈A from (A.mul_mem_iff_of_index_two hi).mpr
      (by
        change v∈P.R ↔ s⁻¹∈P.R
        simpa only [inv_mem_iff] using iff_of_false hvR hsR))
  let x : P.R := ⟨v*s⁻¹,hcoset⟩
  have hx : x * P.coreReflection h s hs x = 1 := by
    apply Subtype.ext
    change (v*s⁻¹)*(s*(v*s⁻¹)*s⁻¹)=1
    calc
      _ = v^2*(s^2)⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hs2,hv2]; simp
  obtain ⟨y,hy⟩ := P.coreReflection_cocycle h s hs hsA hs2 x hx
  have he := congrArg (fun a : P.R => (a:G)) hy
  change v*s⁻¹ = (y:G)*(s*(y:G)⁻¹*s⁻¹) at he
  have hv : v=(y:G)*s*(y:G)⁻¹ := by
    calc
      v = (v*s⁻¹)*s := by group
      _ = ((y:G)*(s*(y:G)⁻¹*s⁻¹))*s := congrArg (fun a:G=>a*s) he
      _ = (y:G)*s*(y:G)⁻¹ := by group
  refine ⟨(y:G)⁻¹,P.R.inv_mem y.property,?_⟩
  rw [hv]
  group

theorem outside_R_involution_conjugate_core (h : IsType z) (v : G)
    (hvT : v∈P.T) (hv2 : orderOf v=2) (hvR : v∉P.R) :
    ∃ r∈P.R, r*v*r⁻¹∈core z := by
  obtain ⟨s,hs,hs2,hsA⟩ := P.exists_core_reflection h
  obtain ⟨r,hr,he⟩ := P.outside_R_conjugate_reflection h s hs hsA
    (hs2 ▸ pow_orderOf_eq_one s) v hvT (hv2 ▸ pow_orderOf_eq_one v) hvR
  exact ⟨r,hr,he ▸ hs⟩

theorem involution_mem_R_or_core (h : IsType z) (v : G)
    (hvT : v∈P.T) (hv2 : orderOf v=2) : v∈P.R ∨ v∈core z := by
  by_cases hvR : v∈P.R
  · exact Or.inl hvR
  · obtain ⟨r,hr,he⟩ := P.outside_R_involution_conjugate_core h v hvT hv2 hvR
    have hrN : r∈normalizer (core z:Set G) :=
      CentralizerHypothesis.centralizer_normalizes_core (P.R_le_double_centralizer hr).1
    exact Or.inr ((mem_normalizer_iff.mp hrN v).mpr he)

theorem T_involution_fused (h : IsType z) (v : G)
    (hvT : v∈P.T) (hv2 : orderOf v=2) : IsConj z v := by
  rcases P.involution_mem_R_or_core h v hvT hv2 with hvR | hvQ
  · exact P.R_involution_fused h v hvR hv2
  · exact h.toCentralizerHypothesis.core_involution_fused_all v hvQ hv2
end RootPair

namespace IsType
variable (h : IsType z)
include h in
theorem involution_fused (v : G) (hv : orderOf v=2) : IsConj z v := by
  obtain ⟨P⟩ := h.exists_rootPair
  obtain ⟨T,hT⟩ := P.exists_sylow_T h
  have hxp : IsPGroup 2 (zpowers v) := IsPGroup.of_card (n:=1) (by
    rw [Nat.card_zpowers,hv,pow_one])
  obtain ⟨S,hS⟩ := hxp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S T
  have hm : MulAut.conj g v ∈ P.T := by
    rw [← hT,← hg,Sylow.smul_def,Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul v (MulAut.conj g) (S:Subgroup G) (hS (mem_zpowers v))
  have ho := (MulAut.conj g).orderOf_eq v |>.trans hv
  have hc := P.T_involution_fused h (MulAut.conj g v) hm ho
  exact hc.trans (isConj_iff.mpr ⟨g,rfl⟩).symm
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
