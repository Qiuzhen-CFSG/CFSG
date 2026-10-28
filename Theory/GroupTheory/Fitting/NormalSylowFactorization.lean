module
public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
/-!
# Normal subgroup factorization from a prime-group image

If the image of a normal subgroup K in G/N is a p-group, intersecting the
supplied Sylow subgroup with K gives K=(K∩N)(K∩S). The proof applies the
first isomorphism theorem and Sylow supplementation inside the literal K.
We also record that K∩F(G), restricted to K, lies in F(K).

These are the finite-group inputs to the original fixed-seed reduction in
Aschbacher–Smith 15.1.2, printed p.1084.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The literal normal intersection is supplemented by the marked Sylow intersection. -/
theorem eq_inf_sup_inf_sylow_of_quotient_image_isPGroup
    (K N : Subgroup G) [K.Normal] [N.Normal] (S : Sylow p G)
    (himage : IsPGroup p (K.map (QuotientGroup.mk' N))) :
    K = (K ⊓ N) ⊔ (K ⊓ (S : Subgroup G)) := by
  let f := (QuotientGroup.mk' N).comp K.subtype
  have hk : f.ker = N.subgroupOf K := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hr : f.range = K.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hq : IsPGroup p (K ⧸ f.ker) :=
    (hr.symm ▸ himage).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  obtain ⟨Q,hQ⟩ := S.exists_subgroupOf_eq_of_normal K
  have he := congrArg (Subgroup.map K.subtype) (Q.sup_eq_top_of_quotient_isPGroup f.ker hq)
  rw [map_sup, hk, hQ, subgroupOf_map_subtype, subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, range_subtype] at he
  simpa only [inf_comm, sup_comm] using he.symm

/-- Restriction of the ambient Fitting subgroup lies in the intrinsic Fitting subgroup. -/
theorem inf_fitting_subgroupOf_le (K : Subgroup G) :
    (K ⊓ fittingSubgroup G).subgroupOf K ≤ fittingSubgroup K := by
  let N := fittingSubgroup G
  let P := K ⊓ N
  have he : P.subgroupOf K = N.subgroupOf K := by
    ext x
    exact and_iff_right x.property
  rw [he]
  let e : N.subgroupOf K ≃* K.subgroupOf N :=
    { toFun := fun x => ⟨⟨x,x.property⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x,x.property⟩,x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let : Group.IsNilpotent (N.subgroupOf K) := Group.nilpotent_of_mulEquiv e.symm
  exact le_sSup ⟨inferInstance,inferInstance⟩
end Subgroup
