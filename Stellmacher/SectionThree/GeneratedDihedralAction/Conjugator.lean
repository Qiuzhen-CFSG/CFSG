module

public import Stellmacher.SectionThree.PrimitiveDihedralExtraction

/-!
# A self-containing reflection conjugator

The primitive extraction chooses a rotation lift inside its generated
subgroup. Multiplying it on the right by the distinguished actor preserves
the conjugate actor subgroup and keeps the conjugator in the generated
subgroup. The new conjugator has square in the ambient two-core, since its
image is a rotation times an inverting involution. This supplies the
conjugator assertions of Stellmacher (7.8)(a), Journal of Algebra 190
(1997), p. 36, without claiming an actual involution lift.
-/

namespace Stellmacher.SectionThree

private theorem conjBy_actor_mem
    {G : Type*} [Group G] (A : Subgroup G) (a : G) (ha : a ∈ A) :
    A.conjBy a = A := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact A.mul_mem (A.mul_mem ha hc) (A.inv_mem ha)
  · intro hb
    refine ⟨a⁻¹ * b * a, A.mul_mem (A.mul_mem (A.inv_mem ha) hb) ha, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

public theorem extracted_self_containing_reflection_conjugator
    {G : Type*} [Group G] [Finite G]
    (P T A : Subgroup G) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A)
    (d : PrimitiveDihedralExtractionData P T A hAP a haA) :
    ∃ y : P, (y : G) ∈ A ⊔ A.conjBy (y : G) ∧
      (y : G) ^ 2 ∈ twoCoreAmbient P ∧
      A.conjBy (y : G) = A.conjBy (d.x : G) := by
  let aP : P := ⟨a, hAP haA⟩
  let y : P := d.x * aP
  have hconj : A.conjBy (y : G) = A.conjBy (d.x : G) := by
    change A.conjBy ((d.x : G) * a) = _
    rw [Subgroup.conjBy_mul, conjBy_actor_mem A a haA]
  refine ⟨y, ?_, ?_, hconj⟩
  · rw [hconj]
    exact (A ⊔ A.conjBy (d.x : G)).mul_mem d.x_mem_generated
      ((show A ≤ A ⊔ A.conjBy (d.x : G) from le_sup_left) haA)
  · let q := QuotientGroup.mk' (pCore 2 P)
    have hrot : q d.x ∈ (d.F₀.subgroupOf P).map q := by
      rw [d.rotation_eq]
      exact Subgroup.mem_zpowers _
    have hinv := d.reflected (q d.x) hrot
    have ha2 : (q aP) ^ 2 = 1 := d.reflection_involution.2
    have hsq : q (y ^ 2) = 1 := by
      change q ((d.x * aP) ^ 2) = 1
      rw [map_pow, map_mul]
      calc
        (q d.x * q aP) ^ 2 =
            q d.x * (q aP * q d.x * (q aP)⁻¹) * (q aP) ^ 2 := by
          simp [pow_two, mul_assoc]
        _ = 1 := by rw [hinv, ha2]; simp
    have hycore : y ^ 2 ∈ pCore 2 P :=
      (QuotientGroup.eq_one_iff (y ^ 2)).mp hsq
    exact Subgroup.mem_map_of_mem P.subtype hycore

end Stellmacher.SectionThree
