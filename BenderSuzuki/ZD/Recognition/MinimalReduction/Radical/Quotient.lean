module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Basic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Fusion

/-!
# Product disconnection in central quotients

Fusion control turns containment of an involution centralizer into containment
of its transporter into M. Consequently quotient product disconnection follows
once involutive products lift to involutive products of distinguished elements.

For a central kernel, the quotient is injective on the distinguished set:
a collision would give a central involution that is a product of two of its
elements. Applying injectivity to a distinguished element and its conjugate
shows that commuting images already have commuting lifts. This proves all
clauses of product disconnection for the central quotient.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5, assertion (4A), printed
pp. 34–35 (PDF pp. 51–52). The central-quotient argument here works for an
arbitrary central kernel, in particular the source's subgroup of order two.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Membership in M is detected in a quotient whose kernel lies in M. -/
public theorem quotient_mem_map_iff (N : Subgroup G) [N.Normal] (hNM : N ≤ M) (g : G) :
    QuotientGroup.mk' N g ∈ M.map (QuotientGroup.mk' N) ↔ g ∈ M := by
  change g ∈ (M.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) ↔ _
  rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hNM]

omit [Finite G] in
/-- A normal subgroup contained in M contains no distinguished involutions. -/
public theorem distinguished_not_mem_normal (h : IsProductDisconnected Z M)
    (N : Subgroup G) [N.Normal] (hNM : N ≤ M) {z : G} (hz : z ∈ Z) : z ∉ N := by
  intro hzN
  apply h.proper
  apply top_unique
  intro g _
  exact (h.conjugate_mem_iff z hz (hNM hzN) g).mp
    (hNM (Subgroup.Normal.conj_mem (inferInstance : N.Normal) z hzN g))

/-- Product disconnection descends when involutive products have genuine lifts. -/
public theorem productDisconnected_quotient_of_product_lifts (h : IsProductDisconnected Z M)
    (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    (hf : ControlsFusionIn M (S : Subgroup G))
    (N : Subgroup G) [N.Normal] (hNM : N ≤ M)
    (hlift : ∀ x ∈ Z, ∀ y ∈ Z,
      IsInvolution (QuotientGroup.mk' N (x * y)) →
      ∃ a ∈ Z, ∃ b ∈ Z, IsInvolution (a * b) ∧
        QuotientGroup.mk' N (a * b) = QuotientGroup.mk' N (x * y)) :
    IsProductDisconnected ((QuotientGroup.mk' N) '' Z) (M.map (QuotientGroup.mk' N)) := by
  let q := QuotientGroup.mk' N
  have hmem := quotient_mem_map_iff N hNM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, by rw [← map_pow, (h.involutions z hz).sq_eq_one, map_one]⟩
    intro he
    exact distinguished_not_mem_normal h N hNM hz ((QuotientGroup.eq_one_iff z).mp he)
  · intro g z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    obtain ⟨z, hz, rfl⟩ := hz
    refine ⟨MulAut.conj g z, h.invariant g z hz, ?_⟩
    simp only [MulAut.conj_apply, map_mul, map_inv]
  · intro he
    apply h.proper
    apply top_unique
    intro g _
    exact (hmem g).mp (he ▸ Subgroup.mem_top (q g))
  · obtain ⟨z, hz, hzM⟩ := h.nonempty
    exact ⟨q z, ⟨z, hz, rfl⟩, Subgroup.mem_map_of_mem q hzM⟩
  · rintro _ ⟨z, hz, rfl⟩ hzM g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    have he : MulAut.conj (q g) (q z) = q (MulAut.conj g z) := by
      simp only [MulAut.conj_apply, map_mul, map_inv]
    change MulAut.conj (q g) (q z) ∈ M.map q ↔ q g ∈ M.map q
    rw [he, hmem, hmem]
    exact h.conjugate_mem_iff z hz ((hmem z).mp hzM) g
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy hxyM g hg
    obtain ⟨a, ha, b, hb, hab, he⟩ := hlift x hx y hy (by simpa only [map_mul] using hxy)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    have hpM : a * b ∈ M := (hmem _).mp (by simpa only [he, map_mul] using hxyM)
    apply Subgroup.mem_map_of_mem q
    apply involution_transporter_mem S hSM hf hab hpM (h.product_centralizer a ha b hb hab hpM)
    apply (hmem _).mp
    change q (a * b) = q (x * y) at he
    have hcomm : q g * q (a * b) = q (a * b) * q g := by
      rw [he]
      simpa only [map_mul] using Subgroup.mem_centralizer_singleton_iff.mp hg
    have hconj : q (MulAut.conj g (a * b)) = q (a * b) := by
      change q (g * (a * b) * g⁻¹) = q (a * b)
      rw [map_mul, map_mul, map_inv, hcomm]
      group
    rw [hconj]
    exact Subgroup.mem_map_of_mem q hpM

omit [Finite G] in
/-- A central quotient is injective on the distinguished involution set. -/
public theorem quotient_injective_on_distinguished_of_central (h : IsProductDisconnected Z M)
    (N : Subgroup G) [N.Normal] (hNc : N ≤ Subgroup.center G) :
    Set.InjOn (QuotientGroup.mk' N) Z := by
  intro x hx y hy he
  have hxyc : x * y ∈ Subgroup.center G := by
    have ht := hNc (QuotientGroup.eq_iff_div_mem.mp he)
    simpa only [div_eq_mul_inv, (h.involutions y hy).inv_eq_self] using ht
  have hcomm : Commute x y := by
    have hh := Subgroup.mem_center_iff.mp hxyc x
    have hyx : y * x = x * y := by
      apply mul_left_cancel (a := x)
      simpa only [mul_assoc] using hh.symm
    exact hyx.symm
  by_contra hne
  have hinv : IsInvolution (x * y) := by
    refine ⟨?_, ?_⟩
    · intro ht
      have : x = y⁻¹ := eq_inv_iff_mul_eq_one.mpr ht
      exact hne (this.trans (h.involutions y hy).inv_eq_self)
    · rw [hcomm.mul_pow, (h.involutions x hx).sq_eq_one, (h.involutions y hy).sq_eq_one, one_mul]
  exact central_involution_ne_product h hxyc hinv hx hy rfl

/-- Every central quotient inherits product disconnection under fusion control. -/
public theorem productDisconnected_quotient_of_central (h : IsProductDisconnected Z M)
    (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    (hf : ControlsFusionIn M (S : Subgroup G))
    (N : Subgroup G) [N.Normal] (hNc : N ≤ Subgroup.center G) :
    IsProductDisconnected ((QuotientGroup.mk' N) '' Z) (M.map (QuotientGroup.mk' N)) := by
  let q := QuotientGroup.mk' N
  apply productDisconnected_quotient_of_product_lifts h S hSM hf N
    (hNc.trans (center_le_of_productDisconnected h))
  intro x hx y hy hinv
  have hinj := quotient_injective_on_distinguished_of_central h N hNc
  have hcommbar : Commute (q x) (q y) := by
    have hxi : (q x)⁻¹ = q x := by rw [← map_inv, (h.involutions x hx).inv_eq_self]
    have hyi : (q y)⁻¹ = q y := by rw [← map_inv, (h.involutions y hy).inv_eq_self]
    have hh : (q x * q y)⁻¹ = q x * q y := by
      simpa only [map_mul] using hinv.inv_eq_self
    rw [mul_inv_rev, hxi, hyi] at hh
    exact hh.symm
  have hc : MulAut.conj x y = y := by
    apply hinj (h.invariant x y hy) hy
    change q (MulAut.conj x y) = q y
    simp only [MulAut.conj_apply, map_mul, map_inv]
    rw [hcommbar.eq]
    group
  have hcomm : Commute x y := mul_inv_eq_iff_eq_mul.mp hc
  refine ⟨x, hx, y, hy, ⟨?_, ?_⟩, rfl⟩
  · intro he
    exact hinv.ne_one (by rw [he, map_one])
  · rw [hcomm.mul_pow, (h.involutions x hx).sq_eq_one, (h.involutions y hy).sq_eq_one, one_mul]

end BenderSuzuki.ZD
