module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.Nonabelian
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCosetFusion
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Element fusion in the extraspecial cubic Sylow subgroup

The original T_R action is transitive on the nonzero cosets of R/B.
In the nonabelian branch B is the center, and inner conjugacy in each
noncentral central coset lifts that transitivity to elements of R.
The marked involution f inverts B, so C_R(f) meets B trivially. The
constructed conjugator from C_R(f) to B then joins the central and
noncentral classes. Sylow conjugacy extends this to all order-three
elements of G, with actual ambient conjugators.

Noncommutativity is the sole remaining branch premise here; OrbitIndex
proves it, and Assembly supplies the constructed local-action data.

Source: Aschbacher–Smith, J.2.7(11), printed p.437 (PDF p.448).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup LocalAction LocalAction.PointOrbits
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
variable {hB : Nat.card c.B = 3}
variable {e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))}
variable (D : LocalAction.Data c hB e)

/-- The intrinsic center is the restriction of the original B. -/
theorem center_eq_base
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (hn : ¬ IsMulCommutative (ambient c D.R)) :
    center (ambient c D.R) = c.B.subgroupOf (ambient c D.R) := by
  have h := (nonabelian_structure c hB e hM D.R hn).2.1
  apply map_injective (ambient c D.R).subtype_injective
  rw [h, map_subgroupOf_eq_of_le D.base_le]

/-- Transitivity on R/B lifts to ambient conjugacy of noncentral elements. -/
theorem noncentral_isConj
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (hn : ¬ IsMulCommutative (ambient c D.R))
    (x y : ambient c D.R) (hx : (x : G) ∉ c.B) (hy : (y : G) ∉ c.B) :
    IsConj (x : G) (y : G) := by
  let := (nonabelian_structure c hB e hM D.R hn).1
  let q := QuotientGroup.mk' (c.B.subgroupOf (ambient c D.R))
  have hxq : q x ≠ 1 := fun h => hx ((QuotientGroup.eq_one_iff (N := c.B.subgroupOf (ambient c D.R)) x).mp h)
  have hyq : q y ≠ 1 := fun h => hy ((QuotientGroup.eq_one_iff (N := c.B.subgroupOf (ambient c D.R)) y).mp h)
  obtain ⟨t, ht⟩ := D.quotient_transitive (q x) (q y) hxq hyq
  have htq : q (action c D.R D.Tplus t x) = q y := ht
  have htc : action c D.R D.Tplus t x ∉ center (ambient c D.R) := by
    rw [center_eq_base c D hM hn]
    intro hm
    exact hyq (htq.symm.trans ((QuotientGroup.eq_one_iff _).mpr hm))
  have hcoset : QuotientGroup.mk' (center (ambient c D.R)) (action c D.R D.Tplus t x) =
      QuotientGroup.mk' (center (ambient c D.R)) y := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [center_eq_base c D hM hn]
    exact QuotientGroup.eq_iff_div_mem.mp htq
  have hi := IsExtraspecial.isConj_of_center_quotient_eq_prime (p := 3) htc hcoset
  exact (isConj_iff.mpr ⟨(t : G), rfl⟩).trans ((ambient c D.R).subtype.map_isConj hi)

/-- No nonidentity element of C_R(f) lies in B: f fixes it and also inverts B. -/
theorem fixed_nonidentity_not_mem_base
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (x : fixed c D.R (D.f : G)) (hx : (x : G) ≠ 1) : (x : G) ∉ c.B := by
  intro hb
  have hinv := marked_inverts_B c hB e hM
    (inclusion (TR_le_NB c D.R D.Tplus) D.f)
    (by rw [← map_pow, show D.f ^ 2 = 1 from D.flip_order ▸ pow_orderOf_eq_one D.f, map_one])
    D.marked_flip (x : G) hb
  have hfix : (D.f : G) * (x : G) * (D.f : G)⁻¹ = (x : G) := by
    rw [← mem_centralizer_singleton_iff.mp x.property.2, mul_inv_cancel_right]
  have hinvself : (x : G)⁻¹ = (x : G) := hinv.symm.trans hfix
  have htwo : (x : G) ^ 2 = 1 := by calc
    (x : G) ^ 2 = (x : G)⁻¹ * (x : G) := by rw [pow_two, hinvself]
    _ = 1 := inv_mul_cancel _
  have hthree : (x : G) ^ 3 = 1 := congrArg Subtype.val (D.cube_eq_one ⟨x, x.property.1⟩)
  have : (x : G) = 1 := by simpa only [pow_succ, htwo, one_mul] using hthree
  exact hx this

/-- Every nonidentity element of B has a noncentral ambient conjugate in R. -/
theorem base_isConj_noncentral
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (b : G) (hb : b ∈ c.B) (hb1 : b ≠ 1) :
    ∃ x : ambient c D.R, (x : G) ∉ c.B ∧ IsConj b (x : G) := by
  obtain ⟨g, hg⟩ := D.fixed_fusion
  rw [← hg] at hb
  obtain ⟨x, hx, he⟩ := hb
  have hx1 : x ≠ 1 := by
    intro h
    apply hb1
    rw [← he, h, map_one]
  exact ⟨⟨x, hx.1⟩, fixed_nonidentity_not_mem_base c D hM ⟨x, hx⟩ hx1,
    (isConj_iff.mpr ⟨g, he⟩).symm⟩

/-- All nonidentity elements of the constructed extraspecial R are G-conjugate. -/
theorem nonidentity_isConj
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (hn : ¬ IsMulCommutative (ambient c D.R))
    (x y : ambient c D.R) (hx : x ≠ 1) (hy : y ≠ 1) :
    IsConj (x : G) (y : G) := by
  classical
  have move (v : ambient c D.R) (hv : v ≠ 1) :
      ∃ w : ambient c D.R, (w : G) ∉ c.B ∧ IsConj (v : G) (w : G) := by
    by_cases hb : (v : G) ∈ c.B
    · exact base_isConj_noncentral c D hM v hb (fun h => hv (Subtype.ext h))
    · exact ⟨v, hb, IsConj.refl _⟩
  obtain ⟨x', hx', hxx⟩ := move x hx
  obtain ⟨y', hy', hyy⟩ := move y hy
  exact hxx.trans ((noncentral_isConj c D hM hn x' y' hx' hy').trans hyy.symm)

/-- Sylow conjugacy extends local fusion to every order-three element of G,
with an actual conjugating element of G. -/
theorem order_three_fusion_of_noncommutative
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (hn : ¬ IsMulCommutative (ambient c D.R))
    (x y : G) (hx : orderOf x = 3) (hy : orderOf y = 3) :
    ∃ g : G, g * x * g⁻¹ = y := by
  obtain ⟨S, hS⟩ := exists_ambient_sylow_of_noncommutative c hB e hM D.R hn
  obtain ⟨x', hxx⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  obtain ⟨y', hyy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hy)
  have hx1 : (x' : G) ≠ 1 := by
    intro h
    have hxone : x = 1 := by simpa only [h, isConj_one_left] using hxx
    simp [hxone] at hx
  have hy1 : (y' : G) ≠ 1 := by
    intro h
    have hyone : y = 1 := by simpa only [h, isConj_one_left] using hyy
    simp [hyone] at hy
  let u : ambient c D.R := ⟨x', hS ▸ x'.property⟩
  let v : ambient c D.R := ⟨y', hS ▸ y'.property⟩
  exact isConj_iff.mp (hxx.trans ((nonidentity_isConj c D hM hn u v
    (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h))).trans hyy.symm))

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
