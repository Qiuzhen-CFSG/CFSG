module
public import Theory.GroupTheory.InvertedOddLift

/-!
# Lifting an odd-order image by an odd-order power

Extracting the odd part preserves the generated image subgroup. A further
integral power therefore recovers the original image exactly. No condition
on the kernel is needed. The unitary cubic-intersection argument in
Aschbacher--Smith 13.3.14(b), p.891, uses this to lift its marked cubic.
-/

namespace MonoidHom

/-- An odd-order image has an odd-order lift in the original cyclic subgroup. -/
public theorem exists_odd_power_with_image
    {G K : Type*} [Group G] [Finite G] [Group K]
    (f : G →* K) (x : G) (ho : Odd (orderOf (f x))) :
    ∃ r : G, r ∈ Subgroup.zpowers x ∧ Odd (orderOf r) ∧ f r = f x := by
  obtain ⟨r,hr,ho,he⟩ := f.exists_odd_power_preserving_zpowers_image x ho
  have hx : f x ∈ Subgroup.zpowers (f r) := he.symm ▸ Subgroup.mem_zpowers (f x)
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨r ^ n, (Subgroup.zpowers x).zpow_mem hr n, ?_, ?_⟩
  · exact ho.of_dvd_nat (orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers r n))
  · rw [map_zpow,hn]

end MonoidHom
