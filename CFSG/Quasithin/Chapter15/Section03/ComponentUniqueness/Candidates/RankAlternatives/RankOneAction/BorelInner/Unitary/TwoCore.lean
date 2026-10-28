module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.ActionKernel

/-!
# Prime-to-three displacements in the invariant Borel

Mutual normalization puts each displacement in both the Borel and Y₊.
Its image modulo the Borel two-core has three-power order: a three-power
of the displacement lies in O₂(Y₊), whose intersection with the Borel is
normal and a two-group. In the abelian Borel quotient the displacement
also has order dividing the order of the original element. Coprimality
therefore makes that image trivial.

This is the two-by-three input to the rank-one paragraph of
Aschbacher--Smith 15.3.37, printed p.1135, using 15.3.11(4)--(5).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.BorelInner.Unitary

theorem coprime_displacement_mem_twoCore
    {G : Type*} [Group G] [Finite G] {Y B : Subgroup G}
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hYB : Y ≤ normalizer (B : Set G))
    (hBY : B ≤ normalizer (Y : Set G))
    [IsMulCommutative (B ⧸ pCore 2 B)]
    {y : G} (hy : y ∈ Y) (b : B) (hb : Nat.Coprime 3 (orderOf b)) :
    y * (b : G) * y⁻¹ * (b : G)⁻¹ ∈ B.pCoreIn 2 := by
  let α := B.normalizerMonoidHom ⟨y, hYB hy⟩
  let c : B := α b * b⁻¹
  have hc : (c : G) ∈ Y := by
    change y * (b : G) * y⁻¹ * (b : G)⁻¹ ∈ Y
    have hc' := (mem_normalizer_iff.mp (hBY b.property) y⁻¹).mp (Y.inv_mem hy)
    simpa only [mul_assoc] using Y.mul_mem hy hc'
  have hQB : Y.pCoreIn 2 ⊓ B ≤ B.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 Y).to_le inf_le_left)
      inf_le_right
    exact le_normalizer_inf
      (hBY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
      B.le_normalizer
  let q := QuotientGroup.mk' (pCore 2 B)
  obtain ⟨k, hk⟩ := hY (QuotientGroup.mk' (pCore 2 Y) ⟨c, hc⟩)
  have hcp : (c : G) ^ (3 ^ k) ∈ Y.pCoreIn 2 := by
    refine ⟨(⟨c, hc⟩ : Y) ^ (3 ^ k), ?_, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 Y) ((⟨c, hc⟩ : Y) ^ (3 ^ k)) = 1
    rwa [map_pow]
  have hthree : q c ^ (3 ^ k) = 1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨z, hz, he⟩ := hQB ⟨hcp, B.pow_mem c.property _⟩
    exact (Subtype.ext he : z = c ^ (3 ^ k)) ▸ hz
  have horder : q c ^ orderOf b = 1 := by
    change (q (α b * b⁻¹)) ^ orderOf b = 1
    have hcomm : Commute (q (α b)) (q b)⁻¹ := mul_comm' _ _
    rw [map_mul, map_inv, hcomm.mul_pow, inv_pow, ← map_pow, ← map_pow,
      ← map_pow, pow_orderOf_eq_one, map_one, map_one, inv_one, mul_one]
  have hc1 : q c = 1 :=
    (pow_eq_one_iff_of_coprime (hb.pow_left k)).mp ⟨hthree, horder⟩
  exact mem_map_of_mem B.subtype ((QuotientGroup.eq_one_iff c).mp hc1)

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.BorelInner.Unitary
