module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.Contracts

/-!
# The inversion and local contracts for the nine-group normalizer

The marked element b = uz inverts both cubic factors and therefore their
literal direct product D. Consequently its centralizer intersects D trivially.
The remaining source arguments have distinct outputs: the ambient normalizer
supplies an involution with |vz| = 3 and relative normality of K, while the
involution-centralizer calculation supplies rQ_b = zQ_b. These contracts do
not assert the existence of either output or the cube alternative.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.9 and the local calculation in 4.10, pp.41–42.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- The simultaneous inversion uses the two original embedded cubic factors. -/
public theorem SymmetricSixData.uz_inverts_markedNine (s : SymmetricSixData h a)
    (w : G) (hw : w ∈ s.markedNine) :
    (s.u * z) * w * (s.u * z)⁻¹ = w⁻¹ := by
  have hX (x : G) (hx : x ∈ cubicInG h) :
      (s.u * z) * x * (s.u * z)⁻¹ = x⁻¹ := by
    have hzx : z * x = x * z :=
      (mem_centralizer_singleton_iff.mp ((map_subtype_le _) hx)).symm
    calc
      (s.u * z) * x * (s.u * z)⁻¹ = s.u * (z * x * z⁻¹) * s.u⁻¹ := by group
      _ = s.u * x * s.u⁻¹ := by rw [hzx, mul_inv_cancel_right]
      _ = x⁻¹ := s.u_inverts_cubicInG x hx
  have hX1 (x : G) (hx : x ∈ s.X1) :
      (s.u * z) * x * (s.u * z)⁻¹ = x⁻¹ := by
    have hu : Commute s.u x := s.u_centralizes_X1 x hx
    calc
      (s.u * z) * x * (s.u * z)⁻¹ = s.u * (z * x * z⁻¹) * s.u⁻¹ := by group
      _ = s.u * x⁻¹ * s.u⁻¹ := by rw [s.z_inverts_X1 x hx]
      _ = x⁻¹ := mul_inv_eq_iff_eq_mul.mpr hu.inv_right.eq
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (cubicInG h) s.X1 s.cubic_disjoint (le_centralizer_iff.mp s.X1_centralizes_X)
  obtain ⟨⟨x, y⟩, hxy⟩ := e.surjective ⟨w, hw⟩
  have hwxy : w = (x : G) * (y : G) :=
    (congrArg Subtype.val hxy).symm.trans (he x y)
  have hc : Commute (x : G) (y : G) := s.X1_centralizes_X y.property x x.property
  rw [hwxy]
  calc
    (s.u * z) * ((x : G) * y) * (s.u * z)⁻¹ =
        ((s.u * z) * x * (s.u * z)⁻¹) * ((s.u * z) * y * (s.u * z)⁻¹) := by group
    _ = (x : G)⁻¹ * (y : G)⁻¹ := by rw [hX x x.property, hX1 y y.property]
    _ = ((x : G) * y)⁻¹ := by rw [mul_inv_rev]; exact hc.inv_inv.eq

/-- The odd nine-group has no nonidentity fixed point under b. -/
public theorem SymmetricSixData.markedNine_inf_centralizer_uz
    (s : SymmetricSixData h a) : s.markedNine ⊓ Centralizer (s.u * z) = ⊥ := by
  apply bot_unique
  intro x hx
  have hc := mem_centralizer_singleton_iff.mp hx.2
  have hi : x = x⁻¹ := by
    calc
      x = (s.u * z) * x * (s.u * z)⁻¹ :=
        (mul_inv_eq_iff_eq_mul.mpr hc.symm).symm
      _ = x⁻¹ := s.uz_inverts_markedNine x hx.1
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    conv_lhs => lhs; rw [hi]
    exact inv_mul_cancel x
  have hx9 : orderOf x ∣ 9 := s.card_markedNine ▸ s.markedNine.orderOf_dvd_natCard hx.1
  exact mem_bot.mpr (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 9)
      (orderOf_dvd_of_pow_eq_one hx2) hx9))

namespace NineNormalizer

/-- The consequences of the ambient nine-group normalizer calculation.
Normality is explicitly relative to N_G(D). The product vz has order three,
which is needed to retain nontrivial order in the two-core quotient. -/
public structure AmbientData (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) where
  normal_K : ((s.markedK m.L).subgroupOf (normalizer (s.markedNine : Set G))).Normal
  v : G
  v_mem : v ∈ normalizer (s.markedNine : Set G)
  v_sq : v * v = 1
  v_commutes_b : Commute (s.u * z) v
  vz_order : orderOf (v * z) = 3

/-- The separate local calculation at b, with the intrinsic core and the
original element r. Its producer must establish the conjugacy and the coset
identity; neither follows just from the orders of P and P ∩ L. -/
public structure CoreData (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) where
  fused : IsConj z (s.u * z)
  hypotheses : Hypotheses (s.u * z)
  rz_mem : m.r * z ∈ coreInG (s.u * z)

/-- Relative normality supplies normalization by the chosen ambient element. -/
public theorem AmbientData.v_normalizes {s : SymmetricSixData h a}
    {m : M10NormalizerGeometry s} (c : AmbientData s m) :
    c.v ∈ normalizer (s.markedK m.L : Set G) := by
  exact (normal_subgroupOf_iff_le_normalizer
    (show s.markedK m.L ≤ normalizer (s.markedNine : Set G) from inf_le_right)).mp
      c.normal_K c.v_mem

end NineNormalizer
end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
