module
public import Theory.GroupTheory.MarkedInnerStrongClosure
public import Theory.GroupTheory.DisjointConjugateCenter
/-! # Central inner projections in a normalized centerless subgroup
An inner implementer of a central element is fixed by the entire actor group:
its conjugates induce the same automorphism, and centerlessness gives uniqueness.
Consequently inner central actions split the ambient center into its component
and centralizing factors. Source application: Aschbacher--Smith 2.5.8(4), p.557.
-/
public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G]
theorem inner_projection_central_of_centerless
    (S K:Subgroup G) (hSK:S≤normalizer (K:Set G)) (hK:center K=⊥)
    (z:G) (hz:z∈centerIn S) (u:K) (hu:(u:G)∈S)
    (ha:∀k:K,((u*k*u⁻¹:K):G)=z*(k:G)*z⁻¹) : (u:G)∈centerIn S := by
  refine ⟨hu,?_⟩
  intro s hs
  let v:K:=⟨s*(u:G)*s⁻¹,(hSK hs u).mp u.property⟩
  have hv:v=u:=by
    apply MulAut.conj_injective_of_center_eq_bot hK
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    change (v:G)*(k:G)*(v:G)⁻¹=(u:G)*(k:G)*(u:G)⁻¹
    let b:K:=⟨s⁻¹*(k:G)*s,by
      have hh: s⁻¹*(k:G)*s⁻¹⁻¹∈K:=(hSK (S.inv_mem hs) k).mp k.property
      rwa [inv_inv] at hh⟩
    calc
      _ = s*((u:G)*(b:G)*(u:G)⁻¹)*s⁻¹ := by dsimp [v,b];group
      _ = s*(z*(b:G)*z⁻¹)*s⁻¹ := by rw [show (u:G)*(b:G)*(u:G)⁻¹=z*(b:G)*z⁻¹ from ha b]
      _ = z*(k:G)*z⁻¹ := by
        dsimp [b]
        calc
          _ = (s*z)*(s⁻¹*(k:G)*s)*(s*z)⁻¹ := by group
          _ = z*(k:G)*z⁻¹ := by rw [hz.2 s hs];group
      _ = (u:G)*(k:G)*(u:G)⁻¹ := (ha k).symm
  have hh:=congrArg Subtype.val hv
  exact (mul_inv_eq_iff_eq_mul.mp hh)

theorem center_split_of_inner_pointwise_actions
    (S K:Subgroup G) (hSK:S≤normalizer (K:Set G)) (hK:center K=⊥)
    (hi:∀z∈centerIn S,∃u:K,(u:G)∈S ∧
      ∀k:K,((u*k*u⁻¹:K):G)=z*(k:G)*z⁻¹) :
    centerIn S=(centerIn S⊓K)⊔(centerIn S⊓centralizer (K:Set G)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨u,hu,ha⟩:=hi z hz
    have huZ:=inner_projection_central_of_centerless S K hSK hK z hz u hu ha
    have hvZ:(u:G)⁻¹*z∈centerIn S:=(centerIn S).mul_mem ((centerIn S).inv_mem huZ) hz
    have hvC:(u:G)⁻¹*z∈centralizer (K:Set G):=by
      intro k hk
      have he:((u:G)⁻¹*z)*k*((u:G)⁻¹*z)⁻¹=k:=by
        calc
          _ = (u:G)⁻¹*(z*k*z⁻¹)*u := by group
          _ = k := by rw [←ha ⟨k,hk⟩];change (u:G)⁻¹*((u:G)*k*(u:G)⁻¹)*u=k;group
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hh:=((centerIn S⊓K)⊔(centerIn S⊓centralizer (K:Set G))).mul_mem
      (mem_sup_left ⟨huZ,u.property⟩) (mem_sup_right ⟨hvZ,hvC⟩)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le inf_le_left inf_le_left

end Subgroup
