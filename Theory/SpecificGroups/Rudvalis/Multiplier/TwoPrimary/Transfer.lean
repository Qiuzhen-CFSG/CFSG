module

public import Theory.GroupTheory.PerfectCentralCoverLocalBound
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Restriction of a perfect central cover at prime-to-p index

If a perfect subgroup P has index prime to p, its full preimage in a finite
perfect central extension with p-group kernel is perfect. Transfer puts the
whole kernel in the preimage's derived subgroup, which already maps onto P.
The kernel equivalence below retains the literal restricted projection.

The proof uses transfer to the abelianization of a subgroup. The Rudvalis
application is Aschbacher--Smith I.1.3(1), printed p.407.
-/

namespace PerfectCentralCovering
open Subgroup

/-- Restriction to a perfect subgroup of prime-to-p index preserves perfectness. -/
public theorem perfect_preimage_of_central_pGroup_kernel
    {E G : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p f.ker)
    (P : Subgroup G) [Group.IsPerfect P] (hi : ¬ p ∣ P.index) :
    Group.IsPerfect (P.comap f) := by
  let R := P.comap f
  let H := ⁅R,R⁆
  have hR : R.map f = P := P.map_comap_eq_self_of_surjective hf
  have hH : H.map f = P := by
    rw [show H = ⁅R,R⁆ from rfl, map_commutator, hR,
      Subgroup.isPerfect_iff.mp (inferInstance : Group.IsPerfect P)]
  let c : Cover E G := ⟨f, hf, inferInstance, hc⟩
  have hk : f.ker ≤ H := c.central_pSubgroup_le_local_lift H P hH hi f.ker le_rfl hp
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (by simpa only [sup_idem] using commutator_le_sup R R)
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp (hH.symm ▸ hx)
  have hxyk : x * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  simpa using H.mul_mem (hk hxyk) hy

/-- Restricting a surjection to a full subgroup preimage leaves its kernel
unchanged as a group. Surjectivity is not needed for this identification. -/
public noncomputable def subgroupComapKernelEquiv
    {E G : Type*} [Group E] [Group G] (f : E →* G) (P : Subgroup G) :
    (f.subgroupComap P).ker ≃* f.ker := by
  let k : (f.subgroupComap P).ker →* f.ker := {
    toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  apply MulEquiv.ofBijective k
  constructor
  · intro x y h
    have he : (x.val : E) = y.val := congrArg (fun z : f.ker => (z : E)) h
    exact Subtype.ext (Subtype.ext he)
  · intro y
    let x : P.comap f := ⟨y.val, by
      change f y.val ∈ P
      rw [y.property]
      exact P.one_mem⟩
    refine ⟨⟨x, ?_⟩, rfl⟩
    exact Subtype.ext y.property

end PerfectCentralCovering
