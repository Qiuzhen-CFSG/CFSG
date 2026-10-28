module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.MarkedCore.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.OutsideProducts.SelectedAction

/-!
# Square roots of the distinguished involution lie in the intrinsic core

Write H = C_G(z) and Q = F*(H). A square root of z centralizes z. If it
were outside Q, its image in H/Q ≃ S₃ would be a nonidentity involution,
hence conjugate to the image of the marked inverter u. Lifting the conjugator
writes the conjugated square root as qu, with q in the literal core Q,
while preserving its square z.

Relative quaternion normality and inversion of the chosen cubic subgroup
supply the existing proof that u acts outerly on both quaternion factors.
For such an action α, a central norm qα(q) is trivial: factor decomposition
makes each factor norm central, and the quaternion norm calculation makes
each factor a coboundary. Thus (qu)² = 1, contradicting z ≠ 1.

This argument uses neither the outside-involution orbit census nor ambient
simplicity or Mathieu recognition. The only exported assertion is the exact
square-root contract consumed by the marked-core assembly.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), the observation in Lemma 4.6, p.40, referring to Lemma 2.3(1).
-/

open Subgroup

private theorem central_norm_eq_one {Q : Type*} [Group Q] [Finite Q]
    (d : QuaternionCentralProductData Q) (α : MulAut Q) (hα : α^2=1)
    (ho : d.BothOuter α) (x : Q) (hx : x * α x ∈ center Q) : x * α x = 1 := by
  have hi (y : Q) : α (α y) = y := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hα y
  have hnorm : d.left ≤ normalizer (d.right : Set Q) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (d.commute b hb c hc).symm
  have hdecomp : x ∈ (↑(d.left ⊔ d.right) : Set Q) := d.span ▸ mem_top x
  rw [coe_mul_of_left_le_normalizer_right d.left d.right hnorm] at hdecomp
  obtain ⟨b, hb, c, hc, rfl⟩ := hdecomp
  have hαb : α b ∈ d.left := ho.left_map.le (mem_map_of_mem _ hb)
  have hαc : α c ∈ d.right := ho.right_map.le (mem_map_of_mem _ hc)
  have he : (b*c) * α (b*c) = (b * α b) * (c * α c) := by
    rw [map_mul, mul_assoc, ← mul_assoc c, ← d.commute _ hαb _ hc]
    group
  rw [he, d.center_eq] at hx
  have hbC : b * α b ∈ d.right := by
    have hh := d.right.mul_mem hx.2 (d.right.inv_mem (d.right.mul_mem hc hαc))
    simpa only [mul_inv_cancel_right] using hh
  have hcB : c * α c ∈ d.left := by
    have hh := d.left.mul_mem (d.left.inv_mem (d.left.mul_mem hb hαb)) hx.1
    simpa only [inv_mul_cancel_left] using hh
  obtain ⟨y, hy⟩ := (quaternion_outer_involution_factor_data d.left d.right
    d.left_model d.intersection_card α hα ho.left_map ho.left_outer).2 ⟨b,hb⟩ hbC
  obtain ⟨w, hw⟩ := (quaternion_outer_involution_factor_data d.right d.left
    d.right_model (by simpa only [inf_comm] using d.intersection_card)
    α hα ho.right_map ho.right_outer).2 ⟨c,hc⟩ hcB
  change b = (y : Q) * α (y : Q)⁻¹ at hy
  change c = (w : Q) * α (w : Q)⁻¹ at hw
  have hbn : b * α b = 1 := by
    rw [hy, map_mul, hi, map_inv]
    group
  have hcn : c * α c = 1 := by
    rw [hw, map_mul, hi, map_inv]
    group
  rw [he, hbn, hcn, one_mul]

private theorem exists_conj_mul_inv_mem {H : Type*} [Group H] (Q : Subgroup H) [Q.Normal]
    (e : (H ⧸ Q) ≃* Equiv.Perm (Fin 3)) (u : H) (hu : u^2=1) (huQ : u ∉ Q)
    (x : H) (hx : x^2 ∈ Q) (hxQ : x ∉ Q) :
    ∃ c : H, (c*x*c⁻¹)*u⁻¹ ∈ Q := by
  let f : H →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf (v : H) : f v = 1 ↔ v ∈ Q := by
    change e (QuotientGroup.mk' Q v) = 1 ↔ v ∈ Q
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff v
  have hx2 : (f x)^2=1 := by rw [← map_pow]; exact (hf _).mpr hx
  have hu2 : (f u)^2=1 := by rw [← map_pow, hu, map_one]
  have table : ∀ x y : Equiv.Perm (Fin 3), x^2=1 → x≠1 → y^2=1 → y≠1 →
      ∃ c : Equiv.Perm (Fin 3), c*x*c⁻¹=y := by decide +kernel
  obtain ⟨c,hc⟩ := table (f x) (f u) hx2 (fun hh => hxQ ((hf x).mp hh))
    hu2 (fun hh => huQ ((hf u).mp hh))
  obtain ⟨b,hb⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective Q)) c
  change f b = c at hb
  refine ⟨b, (hf _).mp ?_⟩
  simp only [map_mul, map_inv, hb, hc, mul_inv_cancel]

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer.MarkedCore
variable {G : Type*} [Group G] [Finite G] {z : G}

private def squareRootsSelected {h : Hypotheses z} (a : SourceGeometry h) : SelectedFusionData h where
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
  u_inverts_X := a.u_inverts_X

/-- Source 4.6's observation: every square root of the distinguished involution
belongs to the intrinsic generalized Fitting subgroup of its centralizer. -/
public theorem squareRootClosed_of_sourceGeometry (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (a : SourceGeometry h) : SquareRootClosed z := by
  intro x hx
  by_contra hxQ
  have hxH : x ∈ Centralizer z := mem_centralizer_singleton_iff.mpr (by
    rw [← hx]
    exact (Commute.self_pow x 2).eq)
  let v : Centralizer z := ⟨x,hxH⟩
  let u : Centralizer z := ⟨a.u,a.u_centralizes⟩
  have hv2 : v^2 = distinguished z := Subtype.ext hx
  have hu2 : u^2 = 1 := Subtype.ext (by
    change a.u^2 = 1
    simpa only [a.u_order] using pow_orderOf_eq_one a.u)
  have hvQ : v ∉ Core z := fun hh => hxQ (mem_map_of_mem (Centralizer z).subtype hh)
  have huQ : u ∉ Core z := fun hh => a.u_not_core (mem_map_of_mem (Centralizer z).subtype hh)
  obtain ⟨c,hc⟩ := exists_conj_mul_inv_mem (Core z) h.quotient_model.some u hu2 huQ v
    (hv2 ▸ h.distinguished_mem_core) hvQ
  let y : Centralizer z := MulAut.conj c v
  have hy2 : y^2 = distinguished z := by
    dsimp only [y]
    rw [← map_pow, hv2]
    apply Subtype.ext
    change (c:G) * z * (c:G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property)
  let q : Core z := ⟨y*u⁻¹,hc⟩
  have hy : y = (q : Centralizer z)*u := by dsimp [q]; group
  let α : MulAut (Core z) := MulAut.conjNormal u
  have hα : α^2=1 := by dsimp [α]; rw [← map_pow,hu2,map_one]
  have hnorm : ((q * α q : Core z) : Centralizer z) = distinguished z := by
    change (q : Centralizer z) * (u * (q : Centralizer z) * u⁻¹) = distinguished z
    have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
    rw [hui]
    calc
      _ = ((q : Centralizer z)*u)^2 := by simp only [pow_two, mul_assoc]
      _ = y^2 := by rw [hy]
      _ = distinguished z := hy2
  have hcentral : q * α q ∈ center (Core z) := by
    apply mem_center_iff.mpr
    intro r
    apply Subtype.ext
    apply Subtype.ext
    change (r:G) * (((q * α q : Core z) : Centralizer z) : G) =
      (((q * α q : Core z) : Centralizer z) : G) * (r:G)
    rw [hnorm]
    exact mem_centralizer_singleton_iff.mp r.val.property
  obtain ⟨d⟩ := h.quaternionCentralProduct
  have ho : d.BothOuter α := Census.selected_bothOuter h hn (squareRootsSelected a) d
  have hn1 := congrArg (fun w : Core z => ((w : Centralizer z) : G))
    (central_norm_eq_one d α hα ho q hcentral)
  have hz1 : z = 1 := (congrArg (fun w : Centralizer z => (w:G)) hnorm).symm.trans hn1
  have hh := h.involution
  simp [hz1] at hh

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer.MarkedCore
