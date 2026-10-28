module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Conjugation

/-!
# The characteristic involution line in the elementary-core argument

Source: Aschbacher–Smith, Lemma 2.5.13(2), printed p.558, and its use in
2.5.24, p.568. The earlier center data give z = zK or z = t zK.
If x fixes zK, its fixed action on z and nontrivial action on t exclude
the second possibility. Invariance of Φ(Φ(S)) therefore gives the exact
involution identities once that subgroup is calculated as ⟨zK⟩.
The iterated Frattini calculation remains an explicit input here.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

private theorem mem_zpowers_two {z a : G} (hz : orderOf z = 2) :
    a ∈ zpowers z ↔ a = 1 ∨ a = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz]
  constructor
  · intro ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
    · exact Finset.mem_image.mpr ⟨1, by simp, by simp⟩

variable (d : EarlierSetup κ G)

private theorem z_ne_one : d.z ≠ 1 := by
  intro h
  have ho := d.z_order
  simp [h] at ho

private theorem z_ne_t : d.z ≠ d.t := by
  simpa using d.t_not_conjugate_z 1

/-- The two source possibilities for the central involution z. -/
theorem central_involution_cases : d.z = d.zK ∨ d.z = d.t * d.zK := by
  have htS := d.sc_le_s d.t_mem
  have htxS : d.x⁻¹ * d.t * d.x ∈ d.S :=
    d.rightConjugate_le d.sc_le_s (by
      simpa [rightConjugate, MulAut.conj_apply] using
        mem_map_of_mem (MulAut.conj d.x⁻¹).toMonoidHom d.t_mem)
  have hzS : d.z ∈ d.S := by
    have h := d.S.mul_mem (d.S.inv_mem htS) htxS
    rw [d.crossing_t, inv_mul_cancel_left] at h
    exact h
  have hzT : d.z ∈ centerIn (d.T : Subgroup G) := d.center_t ▸ mem_zpowers d.z
  have hz : d.z ∈ centerIn d.S := ⟨hzS, fun s hs => hzT.2 s (d.s_le_t hs)⟩
  have htZ : zpowers d.t ≤ centerIn d.S := d.center_s ▸ le_sup_left
  have hkZ : zpowers d.zK ≤ centerIn d.S := d.center_s ▸ le_sup_right
  have hnorm : zpowers d.t ≤ normalizer (zpowers d.zK : Set G) :=
    (htZ.trans inf_le_right |>.trans (centralizer_le (hkZ.trans inf_le_left))).trans
      (centralizer_le_normalizer _)
  rw [d.center_s] at hz
  have hprod : d.z ∈ (zpowers d.t : Set G) * (zpowers d.zK : Set G) := by
    rwa [← coe_mul_of_left_le_normalizer_right _ _ hnorm]
  obtain ⟨a, ha, b, hb, hab⟩ := hprod
  rcases (mem_zpowers_two d.t_order).mp ha with rfl | rfl <;>
    rcases (mem_zpowers_two d.zK_order).mp hb with rfl | rfl
  · exact (z_ne_one d (by simpa using hab.symm)).elim
  · exact Or.inl (by simpa using hab.symm)
  · exact (z_ne_t d (by simpa using hab.symm)).elim
  · exact Or.inr hab.symm

private theorem crossing_fixes_z : d.x⁻¹ * d.z * d.x = d.z := by
  have hzT : d.z ∈ centerIn (d.T : Subgroup G) := d.center_t ▸ mem_zpowers d.z
  have hc := hzT.2 d.x d.x_mem
  calc
    d.x⁻¹ * d.z * d.x = d.x⁻¹ * (d.z * d.x) := by rw [mul_assoc]
    _ = d.x⁻¹ * (d.x * d.z) := by rw [← hc]
    _ = d.z := inv_mul_cancel_left _ _

/-- Source 2.5.13(2), derived from the earlier center and crossing data. -/
theorem involutions_of_fixed_zK (hfix : d.x⁻¹ * d.zK * d.x = d.zK) :
    d.z = d.zK ∧ d.x⁻¹ * d.t * d.x = d.t * d.zK := by
  have hz : d.z = d.zK := by
    rcases central_involution_cases d with h | h
    · exact h
    · have hmul : d.x⁻¹ * (d.t * d.zK) * d.x = d.t * d.zK :=
        h ▸ crossing_fixes_z d
      have hdist : d.x⁻¹ * (d.t * d.zK) * d.x =
          (d.x⁻¹ * d.t * d.x) * (d.x⁻¹ * d.zK * d.x) := by group
      rw [hdist, d.crossing_t, hfix] at hmul
      have ht : d.t * d.z = d.t := mul_right_cancel hmul
      exact (z_ne_one d (mul_left_cancel (ht.trans (mul_one d.t).symm))).elim
  exact ⟨hz, hz ▸ d.crossing_t⟩

/-- A fixed order-two subgroup fixes its nonidentity element. -/
theorem involutions_of_invariant_zK
    (hline : rightConjugate d.x (zpowers d.zK) = zpowers d.zK) :
    d.z = d.zK ∧ d.x⁻¹ * d.t * d.x = d.t * d.zK := by
  apply involutions_of_fixed_zK d
  have hmem : d.x⁻¹ * d.zK * d.x ∈ zpowers d.zK :=
    by
      rw [← hline]
      simp [rightConjugate]
  rcases (mem_zpowers_two d.zK_order).mp hmem with h | h
  · have hk : d.zK = 1 := (MulAut.conj d.x⁻¹).injective (by simpa [MulAut.conj_apply] using h)
    have ho := d.zK_order
    simp [hk] at ho
  · exact h

/-- The iterated Frattini calculation supplies the characteristic line in
2.5.13(2); it is not an extra involution-identity assumption. -/
theorem involutions_of_double_phi
    (hphi : phi (phi d.S) = zpowers d.zK) :
    d.z = d.zK ∧ d.x⁻¹ * d.t * d.x = d.t * d.zK := by
  apply involutions_of_invariant_zK d
  rw [← hphi, crossing_phi_phi]

/-- At order two the marked involution generates the whole core. -/
theorem core_eq_zpowers_of_card_two (hcard : Nat.card d.SC = 2) : d.SC = zpowers d.t := by
  apply (eq_of_le_of_card_ge (zpowers_le.mpr d.t_mem) _).symm
  rw [Nat.card_zpowers, d.t_order, hcard]

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
