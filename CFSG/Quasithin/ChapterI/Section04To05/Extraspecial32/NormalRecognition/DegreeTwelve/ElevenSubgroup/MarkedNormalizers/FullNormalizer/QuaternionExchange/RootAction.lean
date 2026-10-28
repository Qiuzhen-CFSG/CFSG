module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.Conjugation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.RootAction.FactorAction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.MarkedCore.Transport
public import Theory.GroupTheory.QuaternionCentralProductSingularGrid
public import Theory.GroupTheory.QuaternionCentralProductOuterInvolution

/-!
# The quaternion conjugator at the root pivot

Transport the source local hypotheses and relative quaternion normality from
z to the fused involution b. The order-four root w lies in one quaternion
factor P of Q_b. The outside involution u preserves P and acts outerly there,
by the faithful action on its three axes.

The quaternion coboundary calculation gives y in P with
w = y (u y u⁻¹)⁻¹. Its square is b and it inverts w. Decomposing the
noncentral involution z across the two factors shows that its P component
lies on the w-axis, so y sends z to zb. The same coboundary identity gives
y u y⁻¹ = uwb. Thus y satisfies the exact primitive left-conjugation contract,
and the existing calculation exchanges the two generated four-groups.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.8, p.41. The marked geometry and normalizer assembly
are separate consumers; no exchange element or normalization of S is assumed.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange

private theorem quaternion_squares {D : Type*} [Group D] (e : D ≃* QuaternionGroup 2)
    (x y : D) (h : x ^ 2 = 1 ↔ y ^ 2 = 1) : x ^ 2 = y ^ 2 := by
  have ht : ∀ x y : QuaternionGroup 2, (x ^ 2 = 1 ↔ y ^ 2 = 1) → x ^ 2 = y ^ 2 := by decide
  apply e.injective
  rw [map_pow, map_pow]
  apply ht
  simpa only [← map_pow, EmbeddingLike.map_eq_one_iff] using h

private theorem quaternion_axis {D : Type*} [Group D] (e : D ≃* QuaternionGroup 2)
    (w v y : D) (hw : w ^ 2 ≠ 1) (hv : v ^ 2 ≠ 1) (hc : Commute v w)
    (hy : y * w * y⁻¹ = w⁻¹) : y * v * y⁻¹ = v * w ^ 2 := by
  have ht : ∀ w v y : QuaternionGroup 2, w^2 ≠ 1 → v^2 ≠ 1 →
      v*w=w*v → y*w*y⁻¹=w⁻¹ → y*v*y⁻¹=v*w^2 := by decide
  apply e.injective
  simpa only [map_mul, map_inv, map_pow] using ht (e w) (e v) (e y)
    (by simpa only [← map_pow, EmbeddingLike.map_ne_one_iff] using hw)
    (by simpa only [← map_pow, EmbeddingLike.map_ne_one_iff] using hv)
    (by simpa only [map_mul] using congrArg e hc.eq)
    (by simpa only [map_mul, map_inv] using congrArg e hy)

private theorem quaternion_root_coboundary {D : Type*} [Group D]
    (model : D ≃* QuaternionGroup 2) (a : MulAut D) (ha : a ^ 2 = 1)
    (ho : ¬ ∃ v : D, ∀ x : D, a x = v * x * v⁻¹)
    (w : D) (hw : w ^ 2 ≠ 1) (hi : a w = w⁻¹) :
    ∃ y : D, y ^ 2 = w ^ 2 ∧ y * w * y⁻¹ = w⁻¹ ∧ y * (a y)⁻¹ = w := by
  have hn : (w * a w) ^ 2 = 1 := by rw [hi, mul_inv_cancel, one_pow]
  obtain ⟨y, hy⟩ := (quaternion_outer_involution_fibers model a ha ho).2 w hn
  rw [map_inv] at hy
  have hs : y ^ 2 = (a y) ^ 2 := quaternion_squares model y (a y) (by
    simp only [← map_pow, EmbeddingLike.map_eq_one_iff])
  have ht : ∀ y v : QuaternionGroup 2, y^2=v^2 → (y*v⁻¹)^2 ≠ 1 →
      y^2=(y*v⁻¹)^2 ∧ y*(y*v⁻¹)*y⁻¹=(y*v⁻¹)⁻¹ := by decide
  have hm : model w = model y * (model (a y))⁻¹ := by rw [hy, map_mul, map_inv]
  have ht' := ht (model y) (model (a y))
    (by simpa only [map_pow] using congrArg model hs)
    (by rw [← hm, ← map_pow]; exact model.map_ne_one_iff.mpr hw)
  refine ⟨y, ?_, ?_, hy.symm⟩
  · apply model.injective
    rw [map_pow, map_pow, hm]
    exact ht'.1
  · apply model.injective
    simpa only [map_mul, map_inv, hm] using ht'.2

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem decompose (d : QuaternionCentralProductData Q) (x : Q) :
    ∃ v ∈ d.left, ∃ t ∈ d.right, v * t = x := by
  have hn : d.left ≤ normalizer (d.right : Set Q) :=
    (show d.left ≤ centralizer (d.right : Set Q) from
      fun v hv t ht => (d.commute v hv t ht).symm).trans (centralizer_le_normalizer _)
  have hx : x ∈ (↑(d.left ⊔ d.right) : Set Q) := d.span ▸ mem_top x
  rw [coe_mul_of_left_le_normalizer_right d.left d.right hn] at hx
  exact hx

private theorem root_mem_factor (d : QuaternionCentralProductData Q) (w : Q) (hw : w ^ 2 ≠ 1) :
    w ∈ d.left ∨ w ∈ d.right := by
  obtain ⟨v, hv, t, ht, rfl⟩ := decompose d w
  by_cases hvZ : v ∈ center Q
  · exact Or.inr (d.right.mul_mem (d.center_le_factor _ (Or.inr rfl) hvZ) ht)
  by_cases htZ : t ∈ center Q
  · exact Or.inl (d.left.mul_mem hv (d.center_le_factor _ (Or.inl rfl) htZ))
  exact (hw (d.mixed_square v t hv ht hvZ htZ)).elim

private theorem conjugator_in_left (d : QuaternionCentralProductData Q)
    (a : MulAut Q) (ha : a ^ 2 = 1) (hmap : d.left.map a.toMonoidHom = d.left)
    (ho : ¬ ∃ v : d.left, ∀ x : d.left,
      a (x : Q) = (v : Q) * x * (v : Q)⁻¹)
    (w z : Q) (hwL : w ∈ d.left) (hw : w ^ 2 ≠ 1)
    (hz : z ^ 2 = 1) (hzZ : z ∉ center Q) (hc : Commute z w) (hi : a w = w⁻¹) :
    ∃ y : Q, y ^ 2 = w ^ 2 ∧ y * z * y⁻¹ = z * w ^ 2 ∧
      y * w * y⁻¹ = w⁻¹ ∧ y * (a y)⁻¹ = w := by
  let e : MulAut d.left := (d.left.equivMapOfInjective a.toMonoidHom a.injective).trans
    (MulEquiv.subgroupCongr hmap)
  have he2 : e ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change a (a (x : Q)) = x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun ha (x : Q)
  have heo : ¬ ∃ v : d.left, ∀ x : d.left, e x = v * x * v⁻¹ := by
    rintro ⟨v, hv⟩
    exact ho ⟨v, fun x => congrArg Subtype.val (hv x)⟩
  let ww : d.left := ⟨w, hwL⟩
  obtain ⟨y, hy2, hyw, hyd⟩ := quaternion_root_coboundary d.left_model.some e he2 heo ww
    (fun hh => hw (congrArg Subtype.val hh)) (Subtype.ext hi)
  have hy2' : (y : Q) ^ 2 = w ^ 2 := congrArg Subtype.val hy2
  have hyw' : (y : Q) * w * (y : Q)⁻¹ = w⁻¹ := congrArg Subtype.val hyw
  refine ⟨y, hy2', ?_, hyw', congrArg Subtype.val hyd⟩
  obtain ⟨v, hv, t, ht, rfl⟩ := decompose d z
  have hv2 : v ^ 2 ≠ 1 := by
    intro hv2
    have hvZ := (d.factor_square_eq_one_iff _ (Or.inl rfl) v hv).mp hv2
    have hzt : v * t ∈ d.right :=
      d.right.mul_mem (d.center_le_factor _ (Or.inr rfl) hvZ) ht
    exact hzZ ((d.factor_square_eq_one_iff _ (Or.inr rfl) (v*t) hzt).mp hz)
  have hvc : Commute v w := by
    have htw : Commute t w := (show Commute w t from d.commute w hwL t ht).symm
    have hh : v * t * w = w * (v * t) := hc.eq
    rw [mul_assoc, htw.eq, ← mul_assoc, ← mul_assoc] at hh
    exact mul_right_cancel hh
  have hyv : (y : Q) * v * (y : Q)⁻¹ = v * w ^ 2 := congrArg Subtype.val
    (quaternion_axis d.left_model.some ww ⟨v, hv⟩ y
      (fun hh => hw (congrArg Subtype.val hh))
      (fun hh => hv2 (congrArg Subtype.val hh)) (Subtype.ext hvc.eq) hyw)
  have hyt : (y : Q) * t * (y : Q)⁻¹ = t := by
    rw [d.commute y y.property t ht, mul_inv_cancel_right]
  calc
    (y : Q) * (v * t) * (y : Q)⁻¹ =
        ((y : Q) * v * (y : Q)⁻¹) * ((y : Q) * t * (y : Q)⁻¹) := by group
    _ = (v * w ^ 2) * t := by rw [hyv, hyt]
    _ = (v * t) * w ^ 2 := by
      rw [mul_assoc, (mem_center_iff.mp (d.square_mem_center w) t).symm, ← mul_assoc]
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h} {s : SymmetricSixData h a}

/-- The explicit source root configuration has a quaternion conjugator.
All conjugation formulas use left conjugation. -/
public theorem RootData.nonempty_rootConjugator (r : RootData s)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z) : Nonempty (RootConjugator r) := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp (r.b_fused d)
  let e : G ≃* G := MulAut.conj g
  have he : e z = r.b := hg
  let hb : Hypotheses r.b := he ▸ NineNormalizer.MarkedCore.transport h e
  have hnb : QuaternionSubgroupsNormal r.b := he ▸ NineNormalizer.MarkedCore.normal_transport hn e
  have hu2 : s.u ^ 2 = 1 := s.u_order ▸ pow_orderOf_eq_one s.u
  have hbinv : r.b⁻¹ = r.b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using r.b_sq d)
  have huB : s.u ∈ Centralizer r.b := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    change (MulAut.conj s.u) r.b = r.b
    rw [← r.w_sq, map_pow]
    change (s.u * r.w * s.u⁻¹) ^ 2 = r.w ^ 2
    rw [r.u_inverts_w, inv_pow, r.w_sq, hbinv]
  let u : Centralizer r.b := ⟨s.u, huB⟩
  have huQ : u ∉ Core r.b := fun hu =>
    r.u_not_core (mem_map_of_mem (Centralizer r.b).subtype hu)
  let W : Centralizer r.b := ⟨r.w, coreInG_le _ r.w_mem_core⟩
  let Z : Centralizer r.b := ⟨z, coreInG_le _ r.z_mem_core⟩
  have hW : W ∈ Core r.b := by
    rw [← coreInG_subgroupOf]
    exact r.w_mem_core
  have hZ : Z ∈ Core r.b := by
    rw [← coreInG_subgroupOf]
    exact r.z_mem_core
  let w : Core r.b := ⟨W, hW⟩
  let t : Core r.b := ⟨Z, hZ⟩
  let f : Core r.b →* G := (Centralizer r.b).subtype.comp (Core r.b).subtype
  have hf : Function.Injective f := (Centralizer r.b).subtype_injective.comp (Core r.b).subtype_injective
  have hw : w ^ 2 ≠ 1 := by
    intro hw
    have hw' : r.w ^ 2 = 1 := congrArg f hw
    exact r.b_ne_one (r.w_sq.symm.trans hw')
  have hz2 : t ^ 2 = 1 := by
    apply hf
    exact h.involution ▸ pow_orderOf_eq_one z
  have hzZ : t ∉ center (Core r.b) := by
    intro hzZ
    have hm : Z ∈ zpowers (distinguished r.b) :=
      hb.core_center_image ▸ mem_map_of_mem (Core r.b).subtype hzZ
    have hm' := mem_map_of_mem (Centralizer r.b).subtype hm
    rw [MonoidHom.map_zpowers] at hm'
    change z ∈ zpowers r.b at hm'
    rw [mem_zpowers_iff_mem_range_orderOf, r.b_order d] at hm'
    have hc : z = 1 ∨ z = r.b := by
      obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm'
      have hn' : n < 2 := Finset.mem_range.mp hn
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · exact Or.inl (by simpa only [pow_zero] using he.symm)
      · exact Or.inr (by simpa only [pow_one] using he.symm)
    rcases hc with hc | hc
    · have hh := h.involution
      simp [hc] at hh
    · exact r.z_ne_b hc
  let α : MulAut (Core r.b) := MulAut.conjNormal u
  have hα : α ^ 2 = 1 := by
    change (MulAut.conjNormal u) ^ 2 = 1
    rw [← map_pow, show u ^ 2 = 1 from Subtype.ext hu2, map_one]
  have hcomm : Commute t w := by
    apply hf
    exact r.z_commutes_w.eq
  have hinv : α w = w⁻¹ := by
    apply hf
    exact r.u_inverts_w
  obtain ⟨q⟩ := hb.quaternionCentralProduct
  have hpres := hb.localOrbit_factor_preserved hnb q u
  have hcon : ∃ y : Core r.b, y ^ 2 = w ^ 2 ∧ y * t * y⁻¹ = t * w ^ 2 ∧
      y * w * y⁻¹ = w⁻¹ ∧ y * (α y)⁻¹ = w := by
    rcases root_mem_factor q w hw with hwL | hwR
    · exact conjugator_in_left q α hα hpres.1
        (factor_outer hb hnb q q.left (Or.inl rfl) u huQ) w t hwL hw hz2 hzZ hcomm hinv
    · let q' : QuaternionCentralProductData (Core r.b) := {
        left := q.right
        right := q.left
        left_model := q.right_model
        right_model := q.left_model
        intersection_card := by simpa only [inf_comm] using q.intersection_card
        commute := fun x hx y hy => (q.commute y hy x hx).symm
        span := by rw [sup_comm]; exact q.span }
      exact conjugator_in_left q' α hα hpres.2
        (factor_outer hb hnb q q.right (Or.inr rfl) u huQ) w t hwR hw hz2 hzZ hcomm hinv
  obtain ⟨y, hy2, hyz, hyw, hyd⟩ := hcon
  have hyd' : f y * (s.u * f y * s.u⁻¹)⁻¹ = r.w := congrArg f hyd
  have hyu : f y * s.u * (f y)⁻¹ = r.w * s.u := by
    calc
      f y * s.u * (f y)⁻¹ = (f y * (s.u * f y * s.u⁻¹)⁻¹) * s.u := by group
      _ = r.w * s.u := by rw [hyd']
  have hwu : r.w * s.u = s.u * r.w * r.b := by
    have hrel : s.u * r.w = r.w⁻¹ * s.u := mul_inv_eq_iff_eq_mul.mp r.u_inverts_w
    have hrel' : r.w * s.u = s.u * r.w⁻¹ := by
      calc
        r.w * s.u = r.w * (s.u * r.w) * r.w⁻¹ := by group
        _ = r.w * (r.w⁻¹ * s.u) * r.w⁻¹ := by rw [hrel]
        _ = s.u * r.w⁻¹ := by group
    have hwi : r.w⁻¹ = r.w * r.b := by
      apply inv_eq_of_mul_eq_one_right
      calc
        r.w * (r.w * r.b) = r.b ^ 2 := by rw [← mul_assoc, ← pow_two, r.w_sq, pow_two]
        _ = 1 := r.b_sq d
    rw [hrel', hwi, mul_assoc]
  refine ⟨{ y := f y
            y_mem := mem_map_of_mem (Centralizer r.b).subtype y.property
            y_sq := ?_
            conjugates_z := ?_
            inverts_w := congrArg f hyw
            conjugates_u := Or.inr (hyu.trans hwu) }⟩
  · have hh : (f y) ^ 2 = r.w ^ 2 := congrArg f hy2
    exact hh.trans r.w_sq
  · have hh : f y * z * (f y)⁻¹ = z * r.w ^ 2 := congrArg f hyz
    rwa [r.w_sq] at hh

/-- The constructed element exchanges the literal generated four-groups used
by `RootConjugator.exchanges_generated` and the marked-normalizer consumer. -/
public theorem RootData.exists_generated_exchange (r : RootData s)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z) :
    ∃ y ∈ coreInG r.b, y ^ 2 = r.b ∧
      (zpowers r.b ⊔ zpowers (s.u * r.w * z)).map (MulAut.conj y).toMonoidHom =
        zpowers r.b ⊔ zpowers (s.u * z) ∧
      (zpowers r.b ⊔ zpowers (s.u * z)).map (MulAut.conj y).toMonoidHom =
        zpowers r.b ⊔ zpowers (s.u * r.w * z) := by
  obtain ⟨c⟩ := r.nonempty_rootConjugator hn d
  exact ⟨c.y, c.y_mem, c.y_sq, c.exchanges_generated d⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
