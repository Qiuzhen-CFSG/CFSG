module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Restricting a self-centralizing elementary central factor

Suppose the normal elementary two-group Q is U joined with the ambient
center, and Q is self-centralizing. If a subgroup L contains U and is
disjoint from the ambient center, then U viewed inside L is elementary
abelian and self-centralizing in L. No finiteness or generation G=Z(G)L
hypothesis is needed for this transfer.

Elementary abelianness restricts from Q. An element of L centralizing U
also centralizes the ambient center, hence Q, so lies in Q. Its decomposition
as u*z has both the element and u in L, forcing z into L∩Z(G)=1. Thus that
element belongs to U. The theorem uses the ordinary subgroup restriction,
with no auxiliary action or quotient instance.

This supplies the intrinsic centralizer hypothesis for the order-twenty-four
factor in the group identification of Stellmacher (8.2), journal p.38.
Source: `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative

public theorem elementary_central_factor_selfCentralizing_subgroupOf
    {G : Type*} [Group G] (Q U L : Subgroup G) [Q.Normal] [U.Normal]
    [IsElementaryAbelian 2 Q]
    (hQ : Q = U ⊔ Subgroup.center G)
    (hcent : Subgroup.centralizer (Q : Set G) ≤ Q)
    (hUL : U ≤ L) (hLZ : Disjoint L (Subgroup.center G)) :
    IsElementaryAbelian 2 (U.subgroupOf L) ∧
      Subgroup.centralizer (U.subgroupOf L : Set L) ≤ U.subgroupOf L := by
  have hUQ : U ≤ Q := hQ ▸ le_sup_left
  let _ : IsElementaryAbelian 2 U := {
    toIsMulCommutative := ⟨⟨fun u v => Subtype.ext (congrArg (fun q : Q => (q : G))
      (IsMulCommutative.is_comm.comm (⟨u, hUQ u.property⟩ : Q) (⟨v, hUQ v.property⟩ : Q)))⟩⟩
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro u
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (A := Q) u (hUQ u.property) }
  refine ⟨IsElementaryAbelian.subgroupOf hUL, ?_⟩
  intro l hl
  have hlU : (l : G) ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hl (⟨u, hUL hu⟩ : L) hu)
  have hlQ : (l : G) ∈ Q := by
    apply hcent
    rw [hQ]
    have hjoin : U ⊔ Subgroup.center G ≤ Subgroup.centralizer ({(l : G)} : Set G) := by
      apply sup_le
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : x = (l : G) := Set.mem_singleton_iff.mp hx
        subst x
        exact (Subgroup.mem_centralizer_iff.mp hlU u hu).symm
      · exact Subgroup.center_le_centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hjoin hq) l (Set.mem_singleton _)).symm
  rw [hQ] at hlQ
  obtain ⟨u, hu, z, hz, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hlQ
  have hzL : z ∈ L := by
    have heqz : z = u⁻¹ * (l : G) := by rw [← heq]; simp
    rw [heqz]
    exact L.mul_mem (L.inv_mem (hUL hu)) l.property
  have hz1 : z = 1 := hLZ.le_bot ⟨hzL, hz⟩
  have hul : u = (l : G) := by simpa only [hz1, mul_one] using heq
  change (l : G) ∈ U
  exact hul ▸ hu

