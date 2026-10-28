module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.Transfer
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Selection
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.Frattini.BinarySquares

/-!
# The abelian span of the original cyclic core center

Distinct conjugates of the cyclic center have disjoint involution lines.
Each normalizes the other, so they commute. Their span under the plane
residual is therefore an abelian two-group B. Its squares lie in V₂, and
the orbit of the marked square generates V₂, giving Φ(B) = V₂.

These are the exact subgroup facts used by the terminal cubic norm
argument; no full abelian-group or involution-centralizer classification
is needed. Source: Aschbacher–Smith,13.5.16, printed p.922.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH) (b : Conclusions D M 6 g)
  (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)))

include d h e hseed hn hU b in
theorem center_normalized_by_H :
    D.H ≤ normalizer ((center D.QH).map D.QH.subtype : Set G) := by
  rw [←core_normalizer d h e hseed hn hU b]
  exact normalizer_le_normalizer_characteristic_image D.QH (center D.QH)

include d h b in
theorem center_conjugate_le_H {y : G} (hy : y ∈ normalizer (V₂ : Set G)) :
    ((center D.QH).map D.QH.subtype).conjBy y ≤ D.H := by
  rw [b.six.1]
  rintro c ⟨q,hq,rfl⟩ z hz
  obtain ⟨q,hq,rfl⟩ := hq
  have hzP : MulAut.conj y⁻¹ z ∈ V₂ :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V₂ : Set G)).inv_mem hy) ▸
      mem_map_of_mem (MulAut.conj y⁻¹).toMonoidHom (d.line_le_plane hz)
  have hzQ : MulAut.conj y⁻¹ z ∈ D.QH :=
    h.UH_le_QH (le_conjugateSpanBy _ _ (d.plane_le_seed hzP))
  have hc := congrArg (fun u : D.QH => MulAut.conj y u.val)
    (mem_center_iff.mp hq ⟨MulAut.conj y⁻¹ z,hzQ⟩)
  change MulAut.conj y ((MulAut.conj y⁻¹ z) * q.val) =
    MulAut.conj y (q.val * (MulAut.conj y⁻¹ z)) at hc
  simpa [MulAut.conj_apply, mul_assoc] using hc

include d h e hseed hn hU b hS in
theorem center_conjugate_commutes {y : G} (hy : y ∈ normalizer (V₂ : Set G)) :
    ((center D.QH).map D.QH.subtype).conjBy y ≤
      centralizer ((center D.QH).map D.QH.subtype : Set G) := by
  let C := (center D.QH).map D.QH.subtype
  by_cases hyH : y ∈ D.H
  · have he : C.conjBy y = C := mem_normalizer_iff_map_conj_eq.mp
      (center_normalized_by_H d h e hseed hn hU b hyH)
    rw [he]
    let a : center D.QH ≃* C := (center D.QH).equivMapOfInjective D.QH.subtype D.QH.subtype_injective
    exact le_centralizer_iff_isMulCommutative.mpr (⟨⟨fun x y => a.symm.injective (by simp only [map_mul, mul_comm])⟩⟩)
  · obtain ⟨z,hz,hz1⟩ := D.V₁.bot_or_exists_ne_one.resolve_left (by
      intro he
      have hc := h.point_card
      simp [he] at hc)
    have hd := center_conjugate_disjoint d h e hseed hn hU b hS z hz hz1 y hyH
    have hleft : C.conjBy y ≤ normalizer (C : Set G) :=
      (center_conjugate_le_H d h b hy).trans (center_normalized_by_H d h e hseed hn hU b)
    have hright : C ≤ normalizer (C.conjBy y : Set G) := by
      have hinv := map_mono (f := (MulAut.conj y).toMonoidHom)
        ((center_conjugate_le_H d h b ((normalizer (V₂ : Set G)).inv_mem hy)).trans
          (center_normalized_by_H d h e hseed hn hU b))
      rw [map_equiv_normalizer_eq] at hinv
      change (C.conjBy y⁻¹).conjBy y ≤ normalizer (C.conjBy y : Set G) at hinv
      simpa only [conjBy_conjBy,mul_inv_cancel,conjBy_one] using hinv
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply eq_bot_iff.mpr
    exact (le_inf (le_normalizer_iff_commutator_le_right.mp hleft)
      (le_normalizer_iff_commutator_le_left.mp hright)).trans (disjoint_iff.mp hd).le




include d h e hseed hn hU b hS in
theorem center_span_abelian :
    IsMulCommutative (conjugateSpanBy ((center D.QH).map D.QH.subtype)
      (Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂)) := by
  apply (conjugateSpanBy_commutative_iff _ _).mpr
  apply le_centralizer_iff.mp
  apply (closure_le _).mpr
  rintro _ ⟨y,hy,c,hc,rfl⟩
  exact center_conjugate_commutes d h e hseed hn hU b hS
    ((Section08.TransvectionParabolic.EarlierCore.residual_le _ hy).2)
    (mem_map_of_mem _ hc)

include d h in
theorem point_span_plane :
    conjugateSpanBy D.V₁
      (Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂) = V₂ := by
  let R := Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂
  let W := conjugateSpanBy D.V₁ R
  have hR : R ≤ normalizer (V₂ : Set G) :=
    (Section08.TransvectionParabolic.EarlierCore.residual_le _).trans inf_le_right
  have hW : W ≤ V₂ := conjugateSpanBy_le d.line_le_plane hR
  have hd : Nat.card W ∣ 4 := by
    rw [←d.plane_card]
    exact card_dvd_of_le hW
  have hlow : 2 ≤ Nat.card W := by
    rw [←d.line_card]
    exact card_le_of_le (le_conjugateSpanBy D.V₁ R)
  have hne : Nat.card W ≠ 2 := by
    intro he
    have hWeq : D.V₁ = W := eq_of_le_of_card_ge (le_conjugateSpanBy _ _)
      (by rw [d.line_card,he])
    obtain ⟨_,_,_,y,hy,_,_,hyG⟩ := ReturningPlane.exists_original_returning d h
    have hyn : y.val ∈ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _ hy
    rw [←hWeq,h.normalizer_point_eq] at hyn
    exact hyG hyn
  have hcard : Nat.card W = 4 := by
    have hupper := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases Nat.card W <;> norm_num at *
  exact eq_of_le_of_card_ge hW (by rw [d.plane_card,hcard])

include d h e hseed hn hU b in
theorem core_squares_in_point (q : G) (hq : q ∈ D.QH) : q ^ 2 ∈ D.V₁ := by
  let : Fact (IsPGroup 2 D.QH) := ⟨isPGroup_pCoreIn 2 D.H⟩
  rw [←core_frattini_image d h e hseed hn hU b]
  exact mem_map_of_mem D.QH.subtype (pth_power_mem_frattini_of_isPGroup
    (p := 2) (⟨q,hq⟩ : D.QH))

include d h e hseed hn hU b hS in
theorem center_span_squares_in_plane (x : G)
    (hx : x ∈ conjugateSpanBy ((center D.QH).map D.QH.subtype)
      (Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂)) : x ^ 2 ∈ V₂ := by
  let C := (center D.QH).map D.QH.subtype
  let R := Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂
  let B := conjugateSpanBy C R
  let : IsMulCommutative B := center_span_abelian d h e hseed hn hU b hS
  induction hx using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨y,hy,q,hq,rfl⟩ := hc
    have hq2 := core_squares_in_point d h e hseed hn hU b q (map_subtype_le _ hq)
    change (MulAut.conj y q) ^ 2 ∈ V₂
    rw [←map_pow]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Section08.TransvectionParabolic.EarlierCore.residual_le _ hy).2) ▸
      mem_map_of_mem (MulAut.conj y).toMonoidHom (d.line_le_plane hq2)
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := setLike_mul_comm (s := B) hx hy
    rw [hc.mul_pow]
    exact V₂.mul_mem ihx ihy
  | inv x hx ih => rw [inv_pow]; exact V₂.inv_mem ih

include d h e hseed hn hU b hS in
theorem center_span_isPGroup :
    IsPGroup 2 (conjugateSpanBy ((center D.QH).map D.QH.subtype)
      (Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂)) := by
  apply isPGroup_iff_exponent_dvd_pow.mpr
  refine ⟨2, Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro x
  apply Subtype.ext
  change (x.val) ^ (2 ^ 2) = 1
  rw [pow_two, pow_mul]
  let : IsElementaryAbelian 2 D.V := h.elementary
  exact elemPow_eq_one_of_isElementaryAbelian (x.val ^ 2)
    ((d.plane_le_seed.trans d.seed_le)
      (center_span_squares_in_plane d h e hseed hn hU b hS x.val x.property))

include d h e hseed hn hU b hS in
theorem center_span_frattini :
    let B := conjugateSpanBy ((center D.QH).map D.QH.subtype)
      (Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂)
    (frattini B).map B.subtype = V₂ := by
  let C := (center D.QH).map D.QH.subtype
  let R := Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂
  let B := conjugateSpanBy C R
  have hBp : IsPGroup 2 B := center_span_isPGroup d h e hseed hn hU b hS
  let : Fact (IsPGroup 2 B) := ⟨hBp⟩
  apply le_antisymm
  · rw [map_le_iff_le_comap,hBp.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    exact center_span_squares_in_plane d h e hseed hn hU b hS x.val x.property
  · change V₂ ≤ (frattini B).map B.subtype
    conv_lhs => rw [←point_span_plane d h]
    apply conjugateSpanBy_le
    · obtain ⟨z,hz,hz1⟩ := D.V₁.bot_or_exists_ne_one.resolve_left (by
        intro he
        have hc := h.point_card
        simp [he] at hc)
      obtain ⟨j,hj,hjz,hgen⟩ := exists_center_generator d h e hseed hn hU b hS z hz hz1
      rw [(TypeU4.point_generator h z hz hz1).2]
      apply zpowers_le.mpr
      have hjC : j ∈ C := by
        change j ∈ (center D.QH).map D.QH.subtype
        rw [hgen]
        exact mem_zpowers j
      have hjB : j ∈ B := le_conjugateSpanBy _ _ hjC
      rw [←hjz]
      exact mem_map_of_mem B.subtype (pth_power_mem_frattini_of_isPGroup
        (p := 2) (⟨j,hjB⟩ : B))
    · exact (le_normalizer_conjugateSpanBy _ _).trans
        (normalizer_le_normalizer_characteristic_image B (frattini B))

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
