module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Source
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.LinearComponent
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.ParabolicAutomorphisms
public import Theory.SpecificGroups.BinaryLinear.CubicSylowExtension
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.Mathieu.M24.ValueBoundParabolics.CubicExtension
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Source

/-!
# Strict linear and Mathieu point-component enlargement

The actual point-parabolic intersection in the linear component is a
maximal two- or three-space stabilizer. Its preservation forces the
original Sylow action on K₁/O₂(K₁) to be inner. The binary flag parabolics
then lift through that exact quotient to cubic overgroups of the original
ambient Sylow. For M₂₄, the native generating triple and its automorphism
invariance supply the same lift. Strict enlargement forces one cubic
overgroup to escape M = N_G(L); its solvability gives a genuine H-star
with generation parameter one.

Thus the genuine generation-one exclusion proves K₁ = L₁ in both rows.
Together with the checked radical escape and unconditional component
catalogue, this leaves only J₄ for strict enlargement. The source-parameter
applications retain Structural1222At and the two general normalizer
containments. The latter and the J₄ escape remain with qt-d-1251-local;
qt-d-1222-source supplies the earlier structure and qt-d-1251-source owns
final exterior assembly. No normalizer containment is inferred circularly
from the generation exclusion that consumes it.

Source: Aschbacher--Smith, 12.5.3 and 12.5.11(2), printed pp.818 and 821.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private theorem point_parabolic_action_invariant {K : Subgroup G}
    (hK : K ≤ s.marking.Gi 1) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (t : G) (ht : t ∈ s.marking.Mi 1) (htK : t ∈ normalizer (K : Set G)) :
    (s.pointComponentParabolic K).map
      (MulAut.congr (s.pointComponentCoreEquivImage hK hN)
        ((pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,htK⟩))).toMonoidHom =
      s.pointComponentParabolic K := by
  let e := s.pointComponentCoreEquivImage hK hN
  let a := (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,htK⟩)
  let c := MulAut.congr e a
  let q := QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))
  let tH : s.marking.Gi 1 := ⟨t,ht.2⟩
  have hqt : q tH ∈ s.pointCoreImage (s.marking.Mi 1) := mem_map_of_mem q ht
  have he (x : s.pointCoreImage K) :
      (c x : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) =
        q tH * (x : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) * (q tH)⁻¹ := by
    obtain ⟨z,rfl⟩ := e.surjective x
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
    simp only [c,MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply]
    rw [show a (QuotientGroup.mk' _ k) = QuotientGroup.mk' _
      (K.normalizerMonoidHom ⟨t,htK⟩ k) from quotientAut_apply_mk _ _ _]
    rw [s.pointComponentCoreEquivImage_mk,s.pointComponentCoreEquivImage_mk]
    change q (tH * ⟨k,hK k.property⟩ * tH⁻¹) = _
    rw [map_mul,map_mul,map_inv]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    change (c x : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) ∈ s.pointCoreImage (s.marking.Mi 1)
    rw [he]
    exact mul_mem (mul_mem hqt hx) (inv_mem hqt)
  · rw [card_map_of_injective c.injective]

/-- The original Sylow has inner action on the linear point-component quotient. -/
theorem point_linear_sylow_action_inner
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2)
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    (pCore 2 K).quotientAut (K.normalizerMonoidHom
      ⟨t,((normal_subgroupOf_iff_le_normalizer hK.1).mp hN) (s.sylow_le_G₁ ht)⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
  obtain ⟨e,b,hb⟩ := s.pointComponentParabolic_linear_flag hK.1 hN hLK
    (s.Y_le_point_component_of_large_model h hK hN (.inl hm)) hm
  let e0 := s.pointComponentCoreEquivImage hK.1 hN
  let a := (pCore 2 K).quotientAut (K.normalizerMonoidHom
    ⟨t,((normal_subgroupOf_iff_le_normalizer hK.1).mp hN) (s.sylow_le_G₁ ht)⟩)
  let c := MulAut.congr e0 a
  let f := MulAut.congr e c
  have hc : (s.pointComponentParabolic K).map c.toMonoidHom = s.pointComponentParabolic K :=
    s.point_parabolic_action_invariant hK.1 hN t ⟨(le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) ht,s.sylow_le_G₁ ht⟩ _
  have hf : ((s.pointComponentParabolic K).map e.toMonoidHom).map f.toMonoidHom =
      (s.pointComponentParabolic K).map e.toMonoidHom := by
    have he : f.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp c.toMonoidHom := by
      ext x
      simp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply]
    rw [map_map,he,←map_map,hc]
  have hi : f ∈ MulAut.innerSubgroup _ := by
    rcases hb with hb | hb
    all_goals
      rw [hb] at hf
      exact BinaryLinear.FiveFlagGeometry.singleton_flag_preserving_is_inner b _ f hf
  have hcI : c ∈ MulAut.innerSubgroup _ := by
    rw [←MulAut.map_innerSubgroup_congr e,mem_map_equiv] at hi
    simpa only [f,MulEquiv.symm_apply_apply] using hi
  rw [←MulAut.map_innerSubgroup_congr e0,mem_map_equiv] at hcI
  simpa only [c,MulEquiv.symm_apply_apply] using hcI
/-- Strict linear enlargement supplies an actual escaping cubic overgroup of
our original full Sylow subgroup. -/
theorem exists_cubic_overgroup_of_strict_linear_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) :
    ∃ J : Subgroup G, (T : Subgroup G) ≤ J ∧ J ≤ K ⊔ (T : Subgroup G) ∧
      (T : Subgroup G).relIndex J = 3 ∧ ¬ J ≤ s.marking.M := by
  obtain ⟨e,b,hb⟩ := s.pointComponentParabolic_linear_flag hK.1 hN hLK
    (s.Y_le_point_component_of_large_model h hK hN (.inl hm)) hm
  let eK := (s.pointComponentCoreEquivImage hK.1 hN).trans e
  exact BinaryLinear.CubicSylowExtension.exists_cubic_overgroup (by decide : 1 ≤ 4)
    T K s.marking.M D.sylow_normalizes_component
    (s.sylow_le_G₁.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hN)) eK
    (s.point_linear_sylow_action_inner h hK hLK hN hm)
    (fun hKM => hne (s.local_component_eq_of_le_M 1 (.inl rfl) hK hLK hKM))

/-- The strict linear branch of the source generation-one escape, inside the
actual K₁T and with no replacement of the Sylow actor. -/
theorem exists_generation_one_of_strict_linear_point_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ K ⊔ (T : Subgroup G) ∧ ChapterE.generationParameter H = 1 := by
  obtain ⟨J,hTJ,hJK,hindex,hJM⟩ :=
    s.exists_cubic_overgroup_of_strict_linear_point_component h hK hLK hN hne hm
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable J := (T : Subgroup G).isSolvable_of_relIndex_le_four J (by omega)
  obtain ⟨H,hH,hHJ,hgen⟩ := s.exists_generation_one_of_solvable_point_overgroup hTJ
    (hJK.trans (sup_le hK.1 s.sylow_le_G₁)) hJM
  exact ⟨H,hH,hHJ.trans hJK,hgen⟩

/-- The genuine generation-one exclusion discharges the linear branch of
source 12.5.11(2). -/
theorem point_component_eq_of_linear_of_generation_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2)
    (hex : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      ChapterE.generationParameter H ≠ 1) : s.marking.Li 1 = K := by
  by_contra hne
  obtain ⟨H,hH,_,hg⟩ := s.exists_generation_one_of_strict_linear_point_component
    h hK hLK hN hne hm
  exact hex H hH hg

/-- Source-parameter application of the linear enlargement exclusion; the
earlier structural theorem and both general normalizers remain explicit. -/
theorem point_component_eq_of_linear_of_source_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2) : s.marking.Li 1 = K := by
  apply s.point_component_eq_of_linear_of_generation_exclusion h hK hLK hN hm
  intro H hH
  exact generation_ne_one_of_source_parameters s h structural hG₃ hG₆
    (s.seed_le_point_core_of_linear_component h hK.1 hN hLK
      (s.Y_le_point_component_of_large_model h hK hN (.inl hm)) hm) hH

/-- Strict Mathieu enlargement supplies a cubic overgroup of the original Sylow. -/
theorem exists_cubic_overgroup_of_strict_mathieu_point_component
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) :
    ∃ J : Subgroup G, (T : Subgroup G) ≤ J ∧ J ≤ K ⊔ (T : Subgroup G) ∧
      (T : Subgroup G).relIndex J = 3 ∧ ¬ J ≤ s.marking.M :=
  Sporadic.Mathieu.M24ValueBoundParabolics.exists_cubic_overgroup
    T K s.marking.M D.sylow_normalizes_component
    (s.sylow_le_G₁.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hN)) hm.some
    (fun hKM => hne (s.local_component_eq_of_le_M 1 (.inl rfl) hK hLK hKM))

/-- The Mathieu escape lies in the actual K₁T and has generation parameter one. -/
theorem exists_generation_one_of_strict_mathieu_point_component
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ K ⊔ (T : Subgroup G) ∧ ChapterE.generationParameter H = 1 := by
  obtain ⟨J,hTJ,hJK,hindex,hJM⟩ :=
    s.exists_cubic_overgroup_of_strict_mathieu_point_component hK hLK hN hne hm
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable J := (T : Subgroup G).isSolvable_of_relIndex_le_four J (by omega)
  obtain ⟨H,hH,hHJ,hgen⟩ := s.exists_generation_one_of_solvable_point_overgroup hTJ
    (hJK.trans (sup_le hK.1 s.sylow_le_G₁)) hJM
  exact ⟨H,hH,hHJ.trans hJK,hgen⟩

/-- The genuine generation-one exclusion discharges the Mathieu branch of 12.5.11(2). -/
theorem point_component_eq_of_mathieu_of_generation_exclusion
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24))
    (hex : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      ChapterE.generationParameter H ≠ 1) : s.marking.Li 1 = K := by
  by_contra hne
  obtain ⟨H,hH,_,hg⟩ := s.exists_generation_one_of_strict_mathieu_point_component
    hK hLK hN hne hm
  exact hex H hH hg

/-- The Mathieu application retains just the earlier structure and general
normalizer inputs to the genuine generation-one exclusion. -/
theorem point_component_eq_of_mathieu_of_source_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) : s.marking.Li 1 = K := by
  apply s.point_component_eq_of_mathieu_of_generation_exclusion hK hLK hN hm
  intro H hH
  exact s.generation_ne_one_from_local_source h structural hG₃ hG₆ hH

/-- The sole remaining strict point-component branch under the genuine
source generation exclusion is J₄, with the original Y still contained. -/
theorem strict_point_component_janko_of_generation_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K)
    (hex : ∀ H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M,
      ChapterE.generationParameter H ≠ 1) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) ∧ s.Y ≤ K := by
  obtain ⟨hm,hY⟩ := s.strict_point_component_large_of_generation_exclusion h hK hLK hN hne hex
  rcases hm with hm | hm | hm
  · exact (hne (s.point_component_eq_of_linear_of_generation_exclusion h hK hLK hN hm hex)).elim
  · exact (hne (s.point_component_eq_of_mathieu_of_generation_exclusion hK hLK hN hm hex)).elim
  · exact ⟨hm,hY⟩

/-- The actual source-parameter consumer now leaves only the J₄ escape;
no LocalComponents record or point-core containment is assumed. -/
theorem strict_point_component_janko_of_source_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hne : s.marking.Li 1 ≠ K) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) ∧ s.Y ≤ K := by
  apply s.strict_point_component_janko_of_generation_exclusion h hK hLK hN hne
  intro H hH
  exact s.generation_ne_one_from_local_source h structural hG₃ hG₆ hH

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
