module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.LocalGluing.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.OutsideProducts.SelectedAction

/-!
# Central square roots lie in the marked extraspecial core

Write H = C_G(z) and Q = F*(H), identified with O₂(H) by
`Hypotheses.core_eq_pCore`. An element whose square is z belongs to H.
If it lies outside Q, its image in H/Q ≅ S₃ is a transposition. Conjugate
inside H to align this image with the selected involutory inverter u,
and write the resulting element as q*u with q in Q.

Relative normality of both quaternion factors, together with u's inversion
of the cubic whose core centralizer is ⟨z⟩, makes u outer on both factors.
For either factor an outer involution has trivial central norms. Decomposing
q across the commuting factors therefore shows that a central norm q*u(q)
is one. But (q*u)² = z, contradicting the order of z.

The proof uses the earlier selected-inverter action theorem and the literal
centralizer quotient. The order alternatives in SourceGeometry are not used.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 2.3(1), pp.33–34, and its application in Lemma 4.6,
p.40: z is not the square of an element of H−Q.
-/

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing

private theorem central_norm_eq_one {Q : Type*} [Group Q] [Finite Q]
    (d : QuaternionCentralProductData Q) (α : MulAut Q) (hα : α ^ 2 = 1)
    (ho : d.BothOuter α) (x : Q) (hx : x * α x ∈ center Q) : x * α x = 1 := by
  have hnorm : d.left ≤ normalizer (d.right : Set Q) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (d.commute b hb c hc).symm
  have hdecomp : x ∈ (d.left : Set Q) * (d.right : Set Q) := by
    rw [← coe_mul_of_left_le_normalizer_right d.left d.right hnorm, d.span]
    trivial
  obtain ⟨b, hb, c, hc, rfl⟩ := hdecomp
  have hαb : α b ∈ d.left := ho.left_map ▸ mem_map_of_mem α.toMonoidHom hb
  have hαc : α c ∈ d.right := ho.right_map ▸ mem_map_of_mem α.toMonoidHom hc
  have he : (b * α b) * (c * α c) = (b * c) * α (b * c) := by
    rw [map_mul, mul_assoc, ← mul_assoc (α b), d.commute _ hαb c hc,
      mul_assoc, ← mul_assoc]
  rw [d.center_eq, ← he] at hx
  have hbC : b * α b ∈ d.right := by
    have hh := d.right.mul_mem hx.2 (d.right.inv_mem (d.right.mul_mem hc hαc))
    simpa only [mul_inv_cancel_right] using hh
  have hcB : c * α c ∈ d.left := by
    have hh := d.left.mul_mem (d.left.inv_mem (d.left.mul_mem hb hαb)) hx.1
    simpa only [inv_mul_cancel_left] using hh
  obtain ⟨y, hy⟩ := (quaternion_outer_involution_factor_data
    d.left d.right d.left_model d.intersection_card α hα ho.left_map ho.left_outer).2
      ⟨b, hb⟩ hbC
  obtain ⟨v, hv⟩ := (quaternion_outer_involution_factor_data
    d.right d.left d.right_model (by simpa only [inf_comm] using d.intersection_card)
      α hα ho.right_map ho.right_outer).2 ⟨c, hc⟩ hcB
  have hαα (q : Q) : α (α q) = q := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hα q
  change b = _ at hy
  change c = _ at hv
  have hbn : b * α b = 1 := by
    rw [hy]
    simp only [map_mul, map_inv, hαα]
    group
  have hcn : c * α c = 1 := by
    rw [hv]
    simp only [map_mul, map_inv, hαα]
    group
  rw [← he, hbn, hcn, one_mul]

private theorem perm_three_involutions_conjugate :
    ∀ v u : Equiv.Perm (Fin 3), v ^ 2 = 1 → v ≠ 1 → u ^ 2 = 1 → u ≠ 1 →
      ∃ t : Equiv.Perm (Fin 3), t * v * t⁻¹ = u := by
  decide +kernel

variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem square_root_mem_of_outer (h : Hypotheses z)
    (d : QuaternionCentralProductData (Core z)) (u : Centralizer z)
    (hu2 : u ^ 2 = 1) (huQ : u ∉ Core z)
    (ho : d.BothOuter (MulAut.conjNormal u)) (w : G) (hw : w ^ 2 = z) :
    w ∈ coreInG z := by
  classical
  have hwH : w ∈ Centralizer z := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hw]
    group
  let wH : Centralizer z := ⟨w, hwH⟩
  have hw2 : wH ^ 2 = distinguished z := Subtype.ext hw
  by_contra hwQ
  let e := h.quotient_model.some
  let π : Centralizer z →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Core z))
  have hπ (v : Centralizer z) : π v = 1 ↔ v ∈ Core z := by
    change e (QuotientGroup.mk' (Core z) v) = 1 ↔ _
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff v
  have hπz : π (distinguished z) = 1 := (hπ _).mpr h.distinguished_mem_core
  have hπw2 : (π wH) ^ 2 = 1 := by rw [← map_pow, hw2, hπz]
  have hπu2 : (π u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hπw1 : π wH ≠ 1 := fun he => hwQ (mem_map_of_mem _ ((hπ wH).mp he))
  have hπu1 : π u ≠ 1 := fun he => huQ ((hπ u).mp he)
  obtain ⟨s, hs⟩ := perm_three_involutions_conjugate (π wH) (π u)
    hπw2 hπw1 hπu2 hπu1
  have hsurj : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Core z))
  obtain ⟨t, rfl⟩ := hsurj s
  let v := t * wH * t⁻¹
  have hv2 : v ^ 2 = distinguished z := by
    change (MulAut.conj t wH) ^ 2 = distinguished z
    rw [← map_pow, hw2]
    apply Subtype.ext
    change (t : G) * z * (t : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp t.property)
  have hq : v * u⁻¹ ∈ Core z := (hπ _).mp (by
    change π ((t * wH * t⁻¹) * u⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hs, mul_inv_cancel])
  let q : Core z := ⟨v * u⁻¹, hq⟩
  let α : MulAut (Core z) := MulAut.conjNormal u
  have hα : α ^ 2 = 1 := by
    change (MulAut.conjNormal u : MulAut (Core z)) ^ 2 = 1
    rw [← map_pow, hu2, map_one]
  have hnormval : ((q * α q : Core z) : Centralizer z) = distinguished z := by
    change (v * u⁻¹) * (u * (v * u⁻¹) * u⁻¹) = distinguished z
    calc
      _ = v ^ 2 * (u ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = distinguished z := by rw [hv2, hu2, inv_one, mul_one]
  have hcentral : q * α q ∈ center (Core z) := by
    apply mem_center_iff.mpr
    intro r
    apply Subtype.ext
    change (r : Centralizer z) * ((q * α q : Core z) : Centralizer z) =
      ((q * α q : Core z) : Centralizer z) * (r : Centralizer z)
    rw [hnormval]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp r.val.property
  have hn := congrArg (fun q : Core z => (q : Centralizer z))
    (central_norm_eq_one d α hα ho q hcentral)
  rw [hnormval] at hn
  have hz1 : z = 1 := congrArg Subtype.val hn
  simpa [hz1] using h.involution

/-- The central involution has no square root outside its extraspecial core. -/
public theorem square_root_mem_coreInG (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (a : SourceGeometry h)
    (w : G) (hw : w ^ 2 = z) : w ∈ coreInG z := by
  let b : SelectedFusionData h := {
    g := a.g
    fused_mem := a.fused_mem
    fused_ne := a.fused_ne
    intersection_elementary := a.intersection_elementary
    intersection_card := a.intersection_card
    intersection_ne_fusion := a.intersection_ne_fusion
    u := a.u
    u_order := a.u_order
    u_centralizes := a.u_centralizes
    u_conjugate_core := a.u_conjugate_core
    u_not_core := a.u_not_core
    u_fused := a.u_fused
    u_inverts_X := a.u_inverts_X }
  obtain ⟨d⟩ := h.quaternionCentralProduct
  exact square_root_mem_of_outer h d ⟨a.u, a.u_centralizes⟩
    (Subtype.ext (a.u_order ▸ pow_orderOf_eq_one a.u))
    (fun hm => a.u_not_core (mem_map_of_mem _ hm))
    (Census.selected_bothOuter h hn b d) w hw

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.LocalGluing
