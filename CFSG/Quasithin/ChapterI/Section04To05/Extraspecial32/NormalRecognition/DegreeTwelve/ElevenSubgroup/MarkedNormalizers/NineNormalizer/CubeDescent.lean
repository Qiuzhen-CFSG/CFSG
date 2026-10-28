module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Normality.Centralizer

/-!
# Identifying the cube in the involution centralizer

If w has order three modulo Q_b, then w³ belongs to Q_b and three divides
the order of w. A noncentral element of Q_b has common centralizer with b
of order prime to three, by the already proved Sylow-conjugacy consequence
of C_Q(X) = ⟨z⟩. Applying this to w³ gives w³ = 1 or b.

For the actual marked elements, rQ_b = zQ_b identifies the images of vr and
vz. The latter still has order three after quotienting by the two-core of
order 32. This proves the exact cube alternative, including the marked value
b in the order-six case. The construction of v and the Q_b coset identity
are separate premises, not conclusions of this module.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), the local calculation in Lemma 4.10, p.42.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer

open Subgroup

variable {G : Type*} [Group G] [Finite G] {b z : G}

private theorem cube_eq_of_core_mem (hb : Hypotheses b) (w : G)
    (hw : w ∈ Centralizer b) (hcube : w ^ 3 ∈ coreInG b)
    (hthree : 3 ∣ orderOf w) : w ^ 3 = 1 ∨ w ^ 3 = b := by
  by_contra! hne
  apply NonnormalRecognition.core_commonCentralizer_not_three_dvd
    hb (w ^ 3) hcube hne.1 hne.2
  have hwC : w ∈ (Centralizer b ⊓ Centralizer (w ^ 3) : Subgroup G) :=
    ⟨hw, mem_centralizer_singleton_iff.mpr ((Commute.refl w).pow_right 3).eq⟩
  exact hthree.trans
    ((Centralizer b ⊓ Centralizer (w ^ 3) : Subgroup G).orderOf_dvd_natCard hwC)

/-- The cube is the distinguished involution if it is not the identity.
The hypothesis is on the literal generalized-Fitting quotient. -/
public theorem cube_eq_one_or_distinguished_of_quotient_order (hb : Hypotheses b)
    (w : Centralizer b) (ho : orderOf (QuotientGroup.mk' (Core b) w) = 3) :
    (w : G) ^ 3 = 1 ∨ (w : G) ^ 3 = b := by
  apply cube_eq_of_core_mem hb (w : G) w.property
  · have he : QuotientGroup.mk' (Core b) (w ^ 3) = 1 := by
      rw [map_pow, ← ho, pow_orderOf_eq_one]
    exact mem_map_of_mem (Centralizer b).subtype ((QuotientGroup.eq_one_iff _).mp he)
  · rw [Subgroup.orderOf_coe w, ← ho]
    exact orderOf_map_dvd _ _

private theorem quotient_order_three (hb : Hypotheses b) (w : Centralizer b)
    (ho : orderOf (w : G) = 3) :
    orderOf (QuotientGroup.mk' (Core b) w) = 3 := by
  have how : orderOf w = 3 := (Subgroup.orderOf_coe w).symm.trans ho
  apply orderOf_eq_prime
  · rw [← map_pow, ← how, pow_orderOf_eq_one, map_one]
  · intro he
    have hm : w ∈ Core b := (QuotientGroup.eq_one_iff w).mp he
    have hd := (Core b).orderOf_dvd_natCard hm
    rw [how, hb.core_card] at hd
    norm_num at hd

variable {h : Hypotheses z} {a : SourceGeometry h} {s : SymmetricSixData h a}

/-- Application of the quotient calculation to the unchanged r of the
marked M₁₀ geometry. No adjustment of r or assumption on the cube is used. -/
public theorem CoreData.vr_cube {m : M10NormalizerGeometry s} (q : CoreData s m)
    (v : G) (hvb : Commute (s.u * z) v) (hvz : orderOf (v * z) = 3) :
    (v * m.r) ^ 3 = 1 ∨ (v * m.r) ^ 3 = s.u * z := by
  let b := s.u * z
  have hvH : v ∈ Centralizer b := mem_centralizer_singleton_iff.mpr hvb.symm.eq
  have hrH : m.r ∈ Centralizer b :=
    normalizer_le_centralizer_of_characteristic_involution
      m.P (center m.P) b s.uz_order m.center_P m.r_normalizes_P
  have hzH : z ∈ Centralizer b :=
    mem_centralizer_singleton_iff.mpr
      ((s.u_commutes_z.symm).mul_right (Commute.refl z)).eq
  let vH : Centralizer b := ⟨v, hvH⟩
  let rH : Centralizer b := ⟨m.r, hrH⟩
  let zH : Centralizer b := ⟨z, hzH⟩
  let π := QuotientGroup.mk' (Core b)
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two, h.involution] using pow_orderOf_eq_one z)
  have he : π rH = π zH := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [← coreInG_subgroupOf]
    change m.r / z ∈ coreInG b
    simpa only [div_eq_mul_inv, hz_inv] using q.rz_mem
  apply cube_eq_one_or_distinguished_of_quotient_order q.hypotheses (vH * rH)
  change orderOf (π (vH * rH)) = 3
  rw [map_mul, he, ← map_mul]
  exact quotient_order_three q.hypotheses (vH * zH) hvz

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer
