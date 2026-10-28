module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.Diagonal
public import Theory.SpecificGroups.AlternatingSix.M10.OuterInvolutions
public import CFSG.Quasithin.ChapterA.Section05To06.Counting
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.FixedSubgroups

/-!
# The two ambient involution classes and transposition fusion

The marked normalizer has two M10 orbits of outer involutions, distinguished
by membership in the natural S6. The diagonal fixed-five obstruction excludes
the z-class, while the earlier source supplies inverters from both the z- and
s-classes. Lifting the M10 conjugators through the actual cubic kernel identifies
the two orbits with these two ambient classes. Earlier H-fusion and Sylow
conjugacy then exhaust all involutions of the original group.

The transposition theorem has the exact markedMap convention required by the
cubic Sylow and triple-cover consumer. Every original-source input is discharged.

Source: Aschbacher–Smith J.2.7(4,7), printed p.436 (PDF p.447).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
variable (e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6)
  (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)

include hM

lemma inverter_marked_not_extension (u : c.NB) (hu : c.InvertsB (u:G)) :
    e (c.normalizerQuotientMap u)∉AlternatingSix.M10.extension := by
  intro hm
  rw [←hM] at hm
  obtain ⟨a,ha,he⟩ := hm
  have he' : a=c.normalizerQuotientMap u := e.injective he
  have hq : c.normalizerQuotientMap u∈c.centralizerImage := he' ▸ ha
  have hh : u∈c.centralizerImage.comap c.normalizerQuotientMap := hq
  rw [c.centralizerImage_comap (SourceCompletion.B_card c)] at hh
  exact c.not_mem_GB_of_inverts (SourceCompletion.B_card c) hu hh

omit hM in
lemma inverter_marked_order (u : c.NB) (hu : c.InvertsB (u:G)) (hu2 : orderOf u=2) :
    orderOf (e (c.normalizerQuotientMap u))=2 := by
  have hh := (c.normalizer_extension_of_inverter (SourceCompletion.B_card c) (u:G) hu
    ((Subgroup.orderOf_coe u).trans hu2)).1
  exact (e.orderOf_eq _).trans hh

public theorem natural_inverter_z_fused_source (u : c.NB) (hu : c.InvertsB (u:G))
    (hu2 : orderOf u=2)
    (hn : e (c.normalizerQuotientMap u)∈AlternatingSix.ShadowLocal.natural) :
    IsConj (u:G) c.z := by
  obtain ⟨v,hvH,hzv,hvi,hv2⟩ := c.exists_z_class_inverter_source
  let vN : c.NB := ⟨v,c.mem_NB_of_inverts hvi⟩
  have hvN : orderOf vN=2 := (Subgroup.orderOf_coe vN).symm.trans hv2
  have hvn : e (c.normalizerQuotientMap vN)∈AlternatingSix.ShadowLocal.natural := by
    by_contra h
    exact c.diagonal_not_z_fused_source e hM vN (c.inverter_marked_order e vN hvi hvN) h hzv.symm
  have hc := AlternatingSix.M10.OuterInvolutions.same_side_conjugate
    (e (c.normalizerQuotientMap u)) (e (c.normalizerQuotientMap vN))
    (c.inverter_marked_order e u hu hu2) (c.inverter_marked_order e vN hvi hvN)
    (c.inverter_marked_not_extension e hM u hu) (c.inverter_marked_not_extension e hM vN hvi)
    (iff_of_true hn hvn)
  obtain ⟨g,hg,hgu⟩ := c.inverter_model_conjugacy_lift_source e hM u vN hu hc
  exact (isConj_iff.mpr ⟨g,hgu⟩).trans hzv.symm

public theorem diagonal_inverter_s_fused_source (u : c.NB) (hu : c.InvertsB (u:G))
    (hu2 : orderOf u=2)
    (hn : e (c.normalizerQuotientMap u)∉AlternatingSix.ShadowLocal.natural) :
    IsConj (u:G) c.s := by
  obtain ⟨h,hh,hvi,hv2⟩ := SourceCompletion.exists_inverter c
  let v := h*c.s*h⁻¹
  have hsv : IsConj c.s v := isConj_iff.mpr ⟨h,rfl⟩
  let vN : c.NB := ⟨v,c.mem_NB_of_inverts hvi⟩
  have hvN : orderOf vN=2 := (Subgroup.orderOf_coe vN).symm.trans hv2
  have hvn : e (c.normalizerQuotientMap vN)∉AlternatingSix.ShadowLocal.natural := by
    intro h
    exact c.not_isConj_z_s_source
      (hsv.trans (c.natural_inverter_z_fused_source e hM vN hvi hvN h)).symm
  have hc := AlternatingSix.M10.OuterInvolutions.same_side_conjugate
    (e (c.normalizerQuotientMap u)) (e (c.normalizerQuotientMap vN))
    (c.inverter_marked_order e u hu hu2) (c.inverter_marked_order e vN hvi hvN)
    (c.inverter_marked_not_extension e hM u hu) (c.inverter_marked_not_extension e hM vN hvi)
    (iff_of_false hn hvn)
  obtain ⟨g,hg,hgu⟩ := c.inverter_model_conjugacy_lift_source e hM u vN hu hc
  exact (isConj_iff.mpr ⟨g,hgu⟩).trans hsv.symm

lemma inverter_two_classes_source (u : c.NB) (hu : c.InvertsB (u:G))
    (hu2 : orderOf u=2) : IsConj (u:G) c.z ∨ IsConj (u:G) c.s := by
  by_cases hn : e (c.normalizerQuotientMap u)∈AlternatingSix.ShadowLocal.natural
  · exact Or.inl (c.natural_inverter_z_fused_source e hM u hu hu2 hn)
  · exact Or.inr (c.diagonal_inverter_s_fused_source e hM u hu hu2 hn)

lemma H_involution_two_classes_source (x : G) (hxH : x∈d.toTypeRuSetup.H)
    (hx2 : orderOf x=2) : IsConj x c.z ∨ IsConj x c.s := by
  have h26 := (SourceCompletion.fusion c).2.2.1
  by_cases hxQ : x∈d.toTypeRuSetup.Q
  · exact Or.inl (h26.2.2.1 x hxQ hx2)
  by_cases hxK : x∈d.toTypeRuSetup.K
  · obtain ⟨h,hh,hi⟩ := c.H_inverter_transport_source x hxH hxQ hx2
    let u : c.NB := ⟨h*x*h⁻¹,c.mem_NB_of_inverts hi⟩
    have hc : IsConj x (u:G) := isConj_iff.mpr ⟨h,rfl⟩
    have hu : orderOf u=2 := by
      rw [←Subgroup.orderOf_coe]
      exact ((MulAut.conj h).orderOf_eq x).trans hx2
    exact (c.inverter_two_classes_source e hM u hi hu).imp hc.trans hc.trans
  · exact Or.inl (h26.1.2.2 x ⟨hxH,hxK,hx2⟩)

omit e hM in
public theorem two_involution_classes_source :
    CFSG.Quasithin.ChapterA.Section05To06.TwoInvolutionClasses c.z c.s := by
  obtain ⟨e,hM⟩ := c.normalizer_equiv_autA6_source
  refine ⟨SourceCompletion.z_order c,c.s_order_source,c.not_isConj_z_s_source,?_⟩
  intro x hx
  have hxpow : orderOf x=2^1 := by simpa using hx
  obtain ⟨v,hv⟩ := d.T.exists_isConj_of_orderOf_eq_prime_pow hxpow
  have hv2 : orderOf (v:G)=2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hv
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hcases := c.H_involution_two_classes_source e hM v
    (d.toTypeRuSetup.T_le_H v.property) hv2
  exact hcases.imp (fun h => (hv.trans h).symm) (fun h => (hv.trans h).symm)

public theorem transposition_fusion_source : CubicSylow.TranspositionFusion c e := by
  intro u hu2 hmark
  obtain ⟨t,ht,he⟩ := hmark
  have he' : e (c.normalizerQuotientMap u)=AlternatingSix.ShadowLocal.permutationAction t := he
  have huM : e (c.normalizerQuotientMap u)∉AlternatingSix.M10.extension := by
    rw [he']
    exact AlternatingSix.M10.Action.swap_not_mem_extension t ht
  have huGB : (u:G)∉c.GB := by
    intro h
    exact huM (hM ▸ mem_map_of_mem e.toMonoidHom
      (mem_map_of_mem c.normalizerQuotientMap (show u∈c.GB.subgroupOf c.NB from h)))
  have hui : c.InvertsB (u:G) := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one c.B
      (by rw [SourceCompletion.B_card c];decide) (u:G)
      (congrArg Subtype.val (hu2 ▸ pow_orderOf_eq_one u)) u.property with hc | hi
    · exact (huGB (fun b hb => (hc b hb).symm)).elim
    · exact hi
  exact isConj_iff.mp (c.natural_inverter_z_fused_source e hM u hui hu2 (he' ▸ ⟨t,rfl⟩))


omit e hM in
/-- The actual marked quotient and its source transposition fusion, with no additional premise. -/
public theorem marked_normalizer_fusion_source :
    ∃ e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6,
      c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension ∧
      CubicSylow.TranspositionFusion c e := by
  obtain ⟨e,hM⟩ := c.normalizer_equiv_autA6_source
  exact ⟨e,hM,c.transposition_fusion_source e hM⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
