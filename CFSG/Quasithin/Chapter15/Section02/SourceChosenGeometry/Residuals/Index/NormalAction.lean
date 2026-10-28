module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Inputs
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Wreath
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.PrimeComplement
public import Theory.SpecificGroups.GL2.ThreeResidualAutomorphisms
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
public import Mathlib.GroupTheory.IndexNormal

/-!
# The full normalizer action in the equality residual branch

The actual wreath quotient identifies the action of H on K/O₂(K) with D₈.
Transport through the embedded residual subtype retains the original quotient
map. Since T is an ambient Sylow subgroup, this image is Sylow in the full
normalizer action. Coordinates identify Aut(K/O₂(K)) with GL₂(3). A subgroup
of GL₂(3) with dihedral Sylow subgroup of order eight is itself that Sylow
subgroup: the only possible larger order is 24, whose normal quaternion
subgroup contradicts the dihedral isomorphism.

Thus the full normalizer image is actually D₈. When Kc=K, Mc normalizes K,
and its literal O^{3′} residual lies in the kernel of the induced action on
K/O₂(K). The final index calculation must still control this kernel modulo K;
the three-rank bound alone is not used to assert that missing implication.

The kernel calculation and ambient Held exclusion remain with
`qt-e-152-residual-geometry`. The parent `qt-e-152-plane-geometry` supplies
the earlier source hypotheses in ResidualInput.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.2.12(4), printed p.1111, the Kc=K normalizer-action step.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix Matrix.GeneralLinearGroup
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

private theorem dihedral_not_quaternion (e : DihedralGroup 4 ≃* QuaternionGroup 2) : False := by
  have hcases : ∀ q : QuaternionGroup 2, q ^ 2 = 1 → q = 1 ∨ q = QuaternionGroup.a 2 := by decide
  have ha := hcases (e (DihedralGroup.sr 0)) (by rw [← map_pow, show (DihedralGroup.sr 0 : DihedralGroup 4) ^ 2 = 1 by decide, map_one])
  have hb := hcases (e (DihedralGroup.sr 1)) (by rw [← map_pow, show (DihedralGroup.sr 1 : DihedralGroup 4) ^ 2 = 1 by decide, map_one])
  have ha1 : e (DihedralGroup.sr 0) ≠ 1 := by
    intro he
    have := e.injective (he.trans (map_one e).symm)
    exact (by decide : (DihedralGroup.sr 0 : DihedralGroup 4) ≠ 1) this
  have hb1 : e (DihedralGroup.sr 1) ≠ 1 := by
    intro he
    have := e.injective (he.trans (map_one e).symm)
    exact (by decide : (DihedralGroup.sr 1 : DihedralGroup 4) ≠ 1) this
  have he := e.injective ((ha.resolve_left ha1).trans (hb.resolve_left hb1).symm)
  exact (by decide : (DihedralGroup.sr 0 : DihedralGroup 4) ≠ DihedralGroup.sr 1) he

private theorem ternary_linear_dihedral_sylow
    (D : Subgroup (GL (Fin 2) (ZMod 3))) (S : Sylow 2 D)
    (e : S ≃* DihedralGroup 4) : IsPGroup 2 D := by
  have hS : Nat.card S = 8 := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hG : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by rw [Matrix.card_GL_field]; decide
  have hc : 8 * S.index = Nat.card D := by simpa only [hS] using (S : Subgroup D).card_mul_index
  have hd : S.index ∣ 6 := by
    have hh : 8 * S.index ∣ 8 * 6 := by simpa only [hc, hG] using D.card_subgroup_dvd_card
    exact Nat.dvd_of_mul_dvd_mul_left (by decide) hh
  have ho := S.not_dvd_index
  have hi : S.index = 1 ∨ S.index = 3 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
    interval_cases hs : S.index <;> norm_num at *
  rcases hi with hi | hi
  · exact IsPGroup.of_card (n := 3) (by norm_num; simpa only [hi, mul_one] using hc.symm)
  · have hD : D.index = 2 := by
      have hh := D.card_mul_index
      rw [hG, ← hc, hi] at hh
      omega
    let _ : D.Normal := D.normal_of_index_eq_two hD
    have hQ : threeQuaternion ≤ D := by
      apply threeQuaternion_le_specialLinear.trans
      rw [← three_twoResidual]
      exact sInf_le ⟨inferInstance, IsPGroup.of_card (n := 1) (by simpa only [← Subgroup.index_eq_card, pow_one] using hD)⟩
    let Q := threeQuaternion.subgroupOf D
    have hQS : Q ≤ (S : Subgroup D) :=
      (threeQuaternion_isPGroup.comap_subtype).le_sylow_of_normal S
    have hQc : Nat.card Q = 8 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hQ).toEquiv, threeQuaternion_card]
    have heq : Q = (S : Subgroup D) := eq_of_le_of_card_ge hQS (by omega)
    let q : S ≃* QuaternionGroup 2 :=
      (MulEquiv.subgroupCongr heq.symm).trans
        ((subgroupOfEquivOfLe hQ).trans threeQuaternionEquiv)
    exact (dihedral_not_quaternion (e.symm.trans q)).elim

private theorem plane_dihedral_sylow {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 3 W] (hw : Nat.card W = 3 ^ 2)
    (D : Subgroup (MulAut W)) (S : Sylow 2 D) (e : S ≃* DihedralGroup 4) :
    IsPGroup 2 D := by
  obtain ⟨_, a, _⟩ := Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates hw
  let b := a.subgroupMap D
  let S' := S.mapSurjective (f := b.toMonoidHom) b.surjective
  let eS : S' ≃* DihedralGroup 4 :=
    ((S : Subgroup D).equivMapOfInjective b.toMonoidHom b.injective).symm.trans e
  exact (ternary_linear_dihedral_sylow (D.map a.toMonoidHom) S' eS).of_equiv b.symm

private theorem action_dihedral_of_dihedral_overgroup {A W : Type*}
    [Group A] [Finite A] [Group W] [Finite W] [IsElementaryAbelian 3 W]
    (hw : Nat.card W = 3 ^ 2) (f : A →* MulAut W) (S : Sylow 2 A)
    (J : Subgroup A) (hSJ : (S : Subgroup A) ≤ J)
    (e : J.map f ≃* DihedralGroup 4) : Nonempty (f.range ≃* DihedralGroup 4) := by
  let R := S.mapSurjective f.rangeRestrict_surjective
  let D := J.map f.rangeRestrict
  have heq : D.map f.range.subtype = J.map f := by
    change (J.map f.rangeRestrict).map f.range.subtype = _
    rw [Subgroup.map_map]
    rfl
  let eD : D ≃* DihedralGroup 4 :=
    (D.equivMapOfInjective f.range.subtype f.range.subtype_injective).trans
      ((MulEquiv.subgroupCongr heq).trans e)
  have hD : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
    norm_num)
  have hDR : D = (R : Subgroup f.range) := R.is_maximal' hD (map_mono hSJ)
  have hp := plane_dihedral_sylow hw f.range R ((MulEquiv.subgroupCongr hDR.symm).trans eD)
  have htop : (R : Subgroup f.range) = ⊤ :=
    (R.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  exact ⟨Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr (hDR.trans htop).symm).trans eD)⟩

open Chapter1
open Chapter13.Section08.Components.Swapped.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The actual ambient normalizer acts on the residual modulo its own two-core. -/
@[expose] noncomputable def residualNormalizerAction (H : Subgroup G) :
    normalizer (residual H : Set G) →* MulAut (XiQuotient (residual H)) :=
  (quotientAut (pCore 2 (residual H))).comp (residual H).normalizerMonoidHom

omit [Finite G] in
private theorem local_le_residual_normalizer (H : Subgroup G) :
    H ≤ normalizer (residual H : Set G) := by
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, residual] using
    (pResidual 2 H).le_normalizer_map H.subtype

private theorem residual_local_action_dihedral (H : Subgroup G)
    (hw : (H ⧸ pCore 2 H) ≃* Wreath) :
    Nonempty (((H.subgroupOf (normalizer (residual H : Set G))).map
      (residualNormalizerAction H)) ≃* DihedralGroup 4) := by
  let a : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr (pCore 2 (pResidual 2 H))
    (pCore 2 (residual H)) a (pCore_map_iso 2 a)
  let c := MulAut.congr q
  let f := (residualNormalizerAction H).comp (inclusion (local_le_residual_normalizer H))
  have he : f = c.toMonoidHom.comp (ResidualAction.action (X := H)) := by
    ext x z
    obtain ⟨z, rfl⟩ := q.surjective z
    induction z using Quotient.inductionOn with
    | h z =>
      change quotientAut (pCore 2 (residual H))
        ((residual H).normalizerMonoidHom (inclusion (local_le_residual_normalizer H) x))
          (q (QuotientGroup.mk' (pCore 2 (pResidual 2 H)) z)) =
        q (ResidualAction.action x (q.symm (q (QuotientGroup.mk' (pCore 2 (pResidual 2 H)) z))))
      rw [q.symm_apply_apply]
      have hq (y : pResidual 2 H) : q (QuotientGroup.mk' (pCore 2 (pResidual 2 H)) y) =
          QuotientGroup.mk' (pCore 2 (residual H)) (a y) :=
        QuotientGroup.congr_mk' _ _ _ _ y
      change _ = q (quotientAut _ (MulAut.conjNormal x) (QuotientGroup.mk' _ z))
      rw [hq, quotientAut_apply_mk, quotientAut_apply_mk, hq]
      rfl
  have hr : f.range = (ResidualAction.action (X := H)).range.map c.toMonoidHom := by
    rw [he, MonoidHom.range_comp]
  have hf : f.range = (H.subgroupOf (normalizer (residual H : Set G))).map
      (residualNormalizerAction H) := by
    change ((residualNormalizerAction H).comp (inclusion (local_le_residual_normalizer H))).range = _
    rw [MonoidHom.range_comp, inclusion_range]
  exact ⟨(MulEquiv.subgroupCongr hf.symm).trans
    ((MulEquiv.subgroupCongr hr).trans
      (((ResidualAction.action (X := H)).range.equivMapOfInjective c.toMonoidHom
        c.injective).symm.trans (ResidualAction.actionEquivDihedral (hw.trans matrixWreathEquiv))))⟩

/-- The normalizer's full action on K/O₂(K) is the actual dihedral group.
The original Sylow makes the wreath's dihedral image a Sylow subgroup of the
full action; the GL₂(3) calculation excludes a larger image. -/
theorem ResidualInput.normalizer_quotient_action_dihedral {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    Nonempty ((residualNormalizerAction H).range ≃* DihedralGroup 4) := by
  let r := residualQuotientEquiv H d.quotient.some
  let : IsElementaryAbelian 3 (XiQuotient (residual H)) :=
    IsElementaryAbelian.of_injective r.toMonoidHom r.injective
  have hc : Nat.card (XiQuotient (residual H)) = 3 ^ 2 :=
    (Nat.card_congr r.toEquiv).trans WreathModel.cubicBase_card
  let N := normalizer (residual H : Set G)
  let S := T.subtype (d.outside.1.1.2.trans (local_le_residual_normalizer H))
  exact action_dihedral_of_dihedral_overgroup hc (residualNormalizerAction H) S
    (H.subgroupOf N) (fun _ hx => d.outside.1.1.2 hx)
    (residual_local_action_dihedral H d.quotient.some).some

/-- In particular the full normalizer action has order prime to three. -/
theorem ResidualInput.normalizer_quotient_action_two {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) : IsPGroup 2 (residualNormalizerAction H).range := by
  exact IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr d.normalizer_quotient_action_dihedral.some.toEquiv,
      DihedralGroup.nat_card]
    norm_num)

omit [Finite G] in
/-- In the equality row the literal partner normalizes K. -/
theorem partner_normalizes_of_eq (H Mc : Subgroup G)
    (he : partnerSpan H Mc = residual H) :
    Mc ≤ normalizer (residual H : Set G) := by
  rw [← he]
  exact le_normalizer_conjugateSpanBy _ _

/-- The actual partner action in the equality branch. -/
@[expose] noncomputable def partnerQuotientAction (H Mc : Subgroup G)
    (he : partnerSpan H Mc = residual H) :
    Mc →* MulAut (XiQuotient (residual H)) :=
  (residualNormalizerAction H).comp (inclusion (partner_normalizes_of_eq H Mc he))

/-- The source prime-complement residual acts trivially on K/O₂(K).
The remaining index calculation must control this literal action kernel. -/
theorem ResidualInput.threeResidual_le_action_kernel_of_eq {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) (he : partnerSpan H Mc = residual H) :
    primeToResidual 3 Mc ≤ (partnerQuotientAction H Mc he).ker := by
  have hp : IsPGroup 2 (partnerQuotientAction H Mc he).range := by
    apply d.normalizer_quotient_action_two.to_le
    rintro _ ⟨x, rfl⟩
    exact ⟨inclusion (partner_normalizes_of_eq H Mc he) x, rfl⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (partnerQuotientAction H Mc he).range) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hk := primeToResidual_le_ker (partnerQuotientAction H Mc he).rangeRestrict hc
  simpa only [MonoidHom.ker_rangeRestrict] using hk

/-- The same source consequence on the literal embedded prime-set residual. -/
theorem ResidualInput.threePrimeResidual_le_action_kernel_of_eq
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) :
    threePrimeResidual Mc ≤ (partnerQuotientAction H Mc he).ker.map Mc.subtype := by
  rw [threePrimeResidual_eq]
  exact map_mono (d.threeResidual_le_action_kernel_of_eq he)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
