module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.MathieuComponent
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.SpecificGroups.Janko4.Representations.ElementaryDisplacement
public import Theory.SpecificGroups.Janko4.TwoRankLower
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointResidual.SevenSpace
public import Theory.GroupAction.SubgroupQuotientCommutatorBound

/-!
# The J₄ point component and the complete point-core implication

The actual point residual acts nontrivially on U₁/V₁: an exterior
transvection already moves V₇/V₁. The containing J₄ component is simple
by its inherited C-component hypothesis, its two-rank and its trivial
center. Therefore its restriction of the actual quotient action is faithful.

If V is not in O₂(G₁), its image is elementary of order eight inside that
component. A nonidentity seed involution has every displacement in the
image of V₇, a group of order at most 128. But the faithful J₄ displacement
theorem requires at least 4096 elements. This excludes the final model row
and proves V ≤ O₂(G₁) from the exact LocalComponents family.

This replaces the book's larger-parabolic step in the J₄ row while retaining
the original conjugation action, quotient maps and relative normality.
Constructing LocalComponents remains with qt-d-1251-local; the outer
exterior assembly belongs to qt-d-1251-source.
Source: Aschbacher--Smith, 12.5.8(1), printed p.820.
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

private theorem point_residual_moves_seven :
    ¬ ⁅s.marking.Li 1, s.marking.Vi 7⁆ ≤ s.marking.Vi 1 := by
  intro hc
  obtain ⟨g,hg,v,hv,hmove⟩ := Representation.SL5ExteriorSquare.pointResidual_moves_middle
  obtain ⟨l,hl⟩ := s.marking.residualActor_surjective 1 (Or.inl rfl) ⟨g,hg⟩
  let w := s.marking.coordinates.symm (Multiplicative.ofAdd v)
  have hw : (w : G) ∈ s.marking.Vi 7 := (s.marking.mem_subspace _ w).mpr (by
    simp only [w, MulEquiv.apply_symm_apply, toAdd_ofAdd]; exact hv)
  have hc' := hc (commutator_mem_commutator l.property hw)
  let t : V := ⟨(l : G) * w * (l : G)⁻¹, (mem_normalizer_iff.mp
    (D.normalizes (s.marking.Li_le_L 1 l.property)) w).mp w.property⟩
  have hcoord := s.marking.equivariant ⟨l,s.marking.Li_le_L 1 l.property⟩ w
  have hag : s.marking.componentActor ⟨l,s.marking.Li_le_L 1 l.property⟩ = g :=
    (s.marking.residualActor_apply 1 (Or.inl rfl) l).symm.trans (congrArg Subtype.val hl)
  have ht : (s.marking.coordinates t).toAdd =
      Representation.SL5TenDimensional.exteriorAction 2 g v := by
    change (s.marking.coordinates t).toAdd =
      Representation.SL5TenDimensional.exteriorAction 2
        (s.marking.componentActor ⟨l,s.marking.Li_le_L 1 l.property⟩)
        (s.marking.coordinates w).toAdd at hcoord
    simpa only [hag, w, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hcoord
  have hdiff := (s.marking.mem_subspace Representation.SL5ExteriorSquare.V₁ (t * w⁻¹)).mp hc'
  apply hmove
  simpa only [map_mul, map_inv, toAdd_mul, toAdd_inv,
    ht, w, MulEquiv.apply_symm_apply, toAdd_ofAdd, sub_eq_add_neg] using hdiff

private theorem janko_point_component_simple
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    IsSimpleGroup (s.pointCoreImage K) := by
  let H := s.marking.Gi 1
  let e := (s.pointComponentCoreEquivImage hK.1 hn).symm.trans hm.some
  have hq := ChapterE.Structure.sqtk_two_quotient
    (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (Or.inl rfl)))
    (pCore 2 H) pCore_isPGroup
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let : IsQuasisimple (s.pointCoreImage K) :=
    ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank hq
      (pCore_quotient_pCore_eq_bot 2) (hK.2.map_quotient _) (by
        rw [primeRank_equiv 2 e]
        exact (by decide : 2 ≤ 11).trans Janko4.eleven_le_twoRank)
  have hz : center (s.pointCoreImage K) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    rw [map_one]
    have he : e x ∈ center Janko4.Model := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
    exact mem_bot.mp (Janko4.model_center_eq_bot ▸ he)
  let := IsQuasisimple.simple (G := s.pointCoreImage K)
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private instance pointNormal : ((s.marking.Vi 1).subgroupOf s.sevenClosure).Normal :=
  s.point_normal_in_sevenClosure

/-- The actual action of G₁/O₂(G₁) on the original U₁/V₁. -/
private def pointCoreAction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) →*
      MulAut (s.sevenClosure ⧸ (s.marking.Vi 1).subgroupOf s.sevenClosure) :=
  (s.exists_point_core_quotient_action h).choose

/-- Its value on representatives is the original ambient conjugation. -/
private theorem pointCoreAction_mk
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (g : s.marking.Gi 1) (u : s.sevenClosure) :
    s.pointCoreAction h (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1)) g)
      (QuotientGroup.mk' ((s.marking.Vi 1).subgroupOf s.sevenClosure) u) =
    QuotientGroup.mk' ((s.marking.Vi 1).subgroupOf s.sevenClosure)
      ⟨(g : G) * (u : G) * (g : G)⁻¹,
        (mem_normalizer_iff.mp (s.point_normalizes_sevenClosure g.property) u).mp u.property⟩ :=
  (s.exists_point_core_quotient_action h).choose_spec g u

/-- The original point residual acts nontrivially on the original quotient. -/
private theorem pointCoreAction_point_residual_nontrivial
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ¬ s.pointCoreImage (s.marking.Li 1) ≤ (s.pointCoreAction h).ker := by
  intro hk
  apply s.point_residual_moves_seven
  have hc := quotient_conjugation_commutator_le_sup (s.marking.Gi 1) s.sevenClosure
    (s.marking.Vi 1) (s.marking.Vi 7) (s.marking.Li 1) ⊥
    s.point_normalizes_sevenClosure (s.marking.Li_le_Gi 1) s.seven_le_sevenClosure
    ((s.pointCoreAction h).comp (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))))
    (s.pointCoreAction_mk h) (by
      intro a ha u _
      have he := hk (mem_map_of_mem (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))) ha)
      change s.pointCoreAction h (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1)) a) = 1 at he
      simp only [MonoidHom.comp_apply, he, MulAut.one_apply, inv_mul_cancel]
      exact one_mem _)
  simpa only [bot_sup_eq] using hc

/-- The J₄ component acts faithfully on U₁/V₁, using inherited simplicity. -/
private theorem pointCoreAction_injective_on_janko_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hLK : s.marking.Li 1 ≤ K)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    Function.Injective ((s.pointCoreAction h).comp (s.pointCoreImage K).subtype) := by
  let := s.janko_point_component_simple h hK hn hm
  let f := (s.pointCoreAction h).comp (s.pointCoreImage K).subtype
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact (MonoidHom.ker_eq_bot_iff f).mp hb
  · exfalso
    apply s.pointCoreAction_point_residual_nontrivial h
    intro x hx
    exact (show f ⟨x, s.pointCoreImage_mono hLK hx⟩ = 1 from
      show (⟨x, s.pointCoreImage_mono hLK hx⟩ : s.pointCoreImage K) ∈ f.ker from
        ht.symm ▸ mem_top _)


/-- The J₄ row is impossible under failure of point-core containment: the
literal seed moves at most seven binary dimensions, while a faithful J₄
involution must move at least twelve. -/
theorem seed_le_point_core_of_janko_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hn : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hLK : s.marking.Li 1 ≤ K)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  by_contra hf
  let C := s.pointCoreImage K
  let E := s.sevenClosure ⧸ (s.marking.Vi 1).subgroupOf s.sevenClosure
  let π : s.sevenClosure →* E := QuotientGroup.mk' _
  let f : C →* MulAut E := (s.pointCoreAction h).comp C.subtype
  have hfi : Function.Injective f :=
    s.pointCoreAction_injective_on_janko_component h hK hn hLK hm
  let e : C ≃* Janko4.Model := (s.pointComponentCoreEquivImage hK.1 hn).symm.trans hm.some
  let : IsElementaryAbelian 2 E := s.sevenClosure_quotient_elementary h
  let B := ((s.marking.Vi 7).subgroupOf s.sevenClosure).map π
  have hcB : Nat.card B ≤ 128 := by
    have hc := Nat.le_of_dvd (Nat.card_pos (α := (s.marking.Vi 7).subgroupOf s.sevenClosure))
      (((s.marking.Vi 7).subgroupOf s.sevenClosure).card_map_dvd π)
    rw [Nat.card_congr (subgroupOfEquivOfLe s.seven_le_sevenClosure).toEquiv,
      s.card_V₇] at hc
    exact hc
  let : IsElementaryAbelian 2 (s.pointCoreImage V) := s.pointCoreImage_seed_elementary
  let : Nontrivial (s.pointCoreImage V) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [s.pointCoreImage_seed_card h hf]; decide)
  obtain ⟨x,hx⟩ := exists_ne (1 : s.pointCoreImage V)
  have hVC : s.pointCoreImage V ≤ C :=
    s.pointCoreImage_mono (s.seed_le_point_residual.trans hLK)
  let t : C := ⟨x, hVC x.property⟩
  have ht : orderOf t = 2 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := s.pointCoreImage V) x.val x.property
    · intro ht
      apply hx
      apply Subtype.ext
      exact congrArg (fun a : C => a.val) ht
  have hbig := Janko4.BinaryDegree.involution_moved_subgroup_card f hfi e t ht B (by
    intro w
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective ((s.marking.Vi 1).subgroupOf s.sevenClosure) w
    obtain ⟨v,hv,hvx⟩ := x.property
    change s.pointCoreAction h (x : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1))
      (π u) * (π u)⁻¹ ∈ B
    rw [← hvx, s.pointCoreAction_mk h, ← map_inv, ← map_mul]
    apply mem_map_of_mem
    exact s.seed_commutator_sevenClosure_le_seven h hf
      (commutator_mem_commutator hv u.property))
  omega

/-- Source 12.5.8(1), with the local component family as its earlier input.
Constructing this family remains with qt-d-1251-local; the final exterior
assembly belongs to qt-d-1251-source. -/
theorem seed_le_point_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (c : LocalComponents s) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 := by
  by_contra hf
  exact hf (s.seed_le_point_core_of_janko_component h (c.component 1 (Or.inl rfl))
    (c.normal 1 (Or.inl rfl)) (c.contains 1 (Or.inl rfl))
    (s.point_core_failure_janko4 h c hf))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
