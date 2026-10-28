module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.Geometry

/-!
# Left conjugation of the two source four-groups

The root placement makes b and zb ambient conjugates of z and makes w an
order-four element. For a quaternion conjugator, the two possible images
of u differ by b. Direct multiplication proves that both choices exchange
⟨b, uwz⟩ and ⟨b, uz⟩. This proof does not assume that the conjugator
normalizes S or its marked alternating subgroup.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.8, p.41.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h} {s : SymmetricSixData h a}

omit [Finite G] in
private theorem sup_zpowers_mul_right (b v : G) :
    zpowers b ⊔ zpowers (v * b) = zpowers b ⊔ zpowers v := by
  apply le_antisymm
  · exact sup_le le_sup_left (zpowers_le.mpr
      ((zpowers b ⊔ zpowers v).mul_mem (mem_sup_right (mem_zpowers v))
        (mem_sup_left (mem_zpowers b))))
  · apply sup_le le_sup_left
    apply zpowers_le.mpr
    have hh := (zpowers b ⊔ zpowers (v * b)).mul_mem
      (mem_sup_right (mem_zpowers (v * b)))
      ((zpowers b ⊔ zpowers (v * b)).inv_mem (mem_sup_left (mem_zpowers b)))
    simpa only [mul_inv_cancel_right] using hh

theorem RootData.b_sq (r : RootData s) (d : FusionEightData z) : r.b ^ 2 = 1 := by
  let := d.elementary
  exact elemPow_eq_one_of_isElementaryAbelian r.b r.b_mem

theorem RootData.b_order (r : RootData s) (d : FusionEightData z) : orderOf r.b = 2 :=
  orderOf_eq_prime (r.b_sq d) r.b_ne_one

theorem RootData.b_fused (r : RootData s) (d : FusionEightData z) : IsConj z r.b :=
  d.fusion r.b r.b_mem r.b_ne_one

theorem RootData.t_mem_fusion (r : RootData s) : z * r.b ∈ fusionCore z :=
  (fusionCore z).mul_mem h.involution_mem_fusionCore r.b_mem

theorem RootData.t_ne_one (r : RootData s) (d : FusionEightData z) : z * r.b ≠ 1 := by
  intro hh
  have hi : r.b⁻¹ = r.b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using r.b_sq d)
  exact r.z_ne_b ((eq_inv_of_mul_eq_one_left hh).trans hi)

theorem RootData.t_fused (r : RootData s) (d : FusionEightData z) : IsConj z (z * r.b) :=
  d.fusion _ r.t_mem_fusion (r.t_ne_one d)

theorem RootData.w_order (r : RootData s) (d : FusionEightData z) : orderOf r.w = 4 := by
  have hnot : r.w ^ 2 ≠ 1 := by rw [r.w_sq]; exact r.b_ne_one
  have hfin : r.w ^ 4 = 1 := by
    calc
      r.w ^ 4 = (r.w ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [r.w_sq, r.b_sq d]
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin

theorem RootData.b_commutes_z (r : RootData s) : Commute r.b z :=
  mem_centralizer_singleton_iff.mp (coreInG_le z (fusionCore_le z r.b_mem))

theorem RootData.b_commutes_w (r : RootData s) : Commute r.b r.w := by
  rw [← r.w_sq]
  exact (Commute.refl r.w).pow_left 2

theorem RootConjugator.fixes_b {r : RootData s} (c : RootConjugator r) :
    c.y * r.b * c.y⁻¹ = r.b := by
  exact mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp (coreInG_le r.b c.y_mem))

theorem RootConjugator.conjugates_t {r : RootData s} (c : RootConjugator r)
    (d : FusionEightData z) : c.y * (z * r.b) * c.y⁻¹ = z := by
  calc
    c.y * (z * r.b) * c.y⁻¹ =
        (c.y * z * c.y⁻¹) * (c.y * r.b * c.y⁻¹) := by group
    _ = (z * r.b) * r.b := by rw [c.conjugates_z, c.fixes_b]
    _ = z := by rw [mul_assoc, ← pow_two, r.b_sq d, mul_one]

theorem RootConjugator.exchanges_generated {r : RootData s} (c : RootConjugator r)
    (d : FusionEightData z) :
    (zpowers r.b ⊔ zpowers (s.u * r.w * z)).map (MulAut.conj c.y).toMonoidHom =
        zpowers r.b ⊔ zpowers (s.u * z) ∧
    (zpowers r.b ⊔ zpowers (s.u * z)).map (MulAut.conj c.y).toMonoidHom =
        zpowers r.b ⊔ zpowers (s.u * r.w * z) := by
  let f := (MulAut.conj c.y).toMonoidHom
  have hb : f r.b = r.b := c.fixes_b
  have hw : f r.w = r.w⁻¹ := c.inverts_w
  have hz : f z = z * r.b := c.conjugates_z
  have cancel_b (v : G) : v * r.b * z * r.b = v * z := by
    calc
      v * r.b * z * r.b = v * (r.b * z) * r.b := by group
      _ = v * (z * r.b) * r.b := by rw [r.b_commutes_z.eq]
      _ = v * z := by rw [mul_assoc, mul_assoc, ← pow_two, r.b_sq d, mul_one]
  have hfirst : f (s.u * r.w * z) = (s.u * z) * r.b ∨
      f (s.u * r.w * z) = s.u * z := by
    rw [map_mul, map_mul, hw, hz]
    rcases c.conjugates_u with hu | hu
    · left
      change f s.u = s.u * r.w at hu
      rw [hu]
      group
    · right
      change f s.u = s.u * r.w * r.b at hu
      rw [hu]
      calc
        (s.u * r.w * r.b) * r.w⁻¹ * (z * r.b) =
            s.u * (r.w * r.b) * r.w⁻¹ * (z * r.b) := by group
        _ = s.u * (r.b * r.w) * r.w⁻¹ * (z * r.b) := by
          rw [r.b_commutes_w.eq]
        _ = s.u * r.b * z * r.b := by group
        _ = s.u * z := cancel_b s.u
  have hsecond : f (s.u * z) = (s.u * r.w * z) * r.b ∨
      f (s.u * z) = s.u * r.w * z := by
    rw [map_mul, hz]
    rcases c.conjugates_u with hu | hu
    · left
      change f s.u = s.u * r.w at hu
      rw [hu]
      group
    · right
      change f s.u = s.u * r.w * r.b at hu
      rw [hu, ← mul_assoc]
      exact cancel_b (s.u * r.w)
  change (zpowers r.b ⊔ zpowers (s.u * r.w * z)).map f = _ ∧
    (zpowers r.b ⊔ zpowers (s.u * z)).map f = _
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, hb]
  constructor
  · rcases hfirst with hh | hh
    · rw [hh, sup_zpowers_mul_right]
    · rw [hh]
  · rcases hsecond with hh | hh
    · rw [hh, sup_zpowers_mul_right]
    · rw [hh]

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
end
