module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Lifting normalizers of prime-perfect subgroups

If a p-group kernel normalizes a p-perfect subgroup A, then A is the
p-residual of A ker(f). The latter is the full preimage of f(A).
Its characteristic residual therefore recovers A and lifts the whole
normalizer of f(A), without requiring A to be perfect or the kernel central.

Source application: Aschbacher--Smith, proof of 12.6.26, printed p.832,
for the original point residual in the two-core quotient.
-/

public section
open Subgroup
namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

/-- A p-perfect subgroup normalized by a p-group kernel is recovered from
its image, so every lift of an image normalizer normalizes it. -/
theorem normalizer_comap_map_le_of_pGroup_kernel {p : ℕ} (f : G →* K)
    (A : Subgroup G) (hA : IsPPerfect p A) (hk : IsPGroup p f.ker)
    (hn : f.ker ≤ normalizer (A : Set G)) :
    (normalizer (A.map f : Set K)).comap f ≤ normalizer (A : Set G) := by
  let U := A ⊔ f.ker
  have he : (pResidual p U).map U.subtype = A := by
    let B := A.subgroupOf U
    let C := f.ker.subgroupOf U
    let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
    have hBC : B ⊔ C = ⊤ := by
      rw [← subgroupOf_sup (show A ≤ U from le_sup_left)
        (show f.ker ≤ U from le_sup_right),subgroupOf_self]
    let e := subgroupOfEquivOfLe (show A ≤ U from le_sup_left)
    rw [pResidual_eq_of_isPPerfect_sup B C
      (hA.of_surjective e.symm.toMonoidHom e.symm.surjective) hk.comap_subtype hBC,
      map_subgroupOf_eq_of_le le_sup_left]
  have hN : (normalizer (A.map f : Set K)).comap f ≤ normalizer (U : Set G) := by
    simpa only [U,comap_map_eq] using (A.map f).le_normalizer_comap f
  simpa only [he] using hN.trans (normalizer_le_normalizer_characteristic_image U (pResidual p U))

end Subgroup

