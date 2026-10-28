module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDualSplit
public import Theory.Representation.SL5ExteriorSquare.SylowFixed
public import Theory.Representation.PSL3Two.NaturalDualInnerFixed

/-!
# The original point action in the remaining natural--dual case

The whole ten-dimensional containing action has a Sylow fixed space of
rank at most one. The original moved subgroup embeds equivariantly in that
orbit. If the original point Sylow acted only by inner automorphisms on
L/O₂(L), its natural--dual marking would supply two independent fixed
vectors. Thus the actual point action contains an outer automorphism.

The cover version first discharges its original fixed kernel. The literal
consumer excludes the row once the containing binary-five action is shown
to induce only inner automorphisms on this smaller quotient. The extension
Models.NaturalDualExclusion proves that last input and closes this source row.
The other original rows and final ConstrainedExclusionAt remain with
qt-d-10-nona5-point-constrained.

Source: Aschbacher--Smith 10.2.9, printed p.752.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The literal orbit and full point Sylow have at most one fixed dimension. -/
theorem Context.orbit_point_fixed_finrank_le_one_of_naturalDual_cover
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    Module.finrank (ZMod 2) (fixedSpace
      ((action (internalModule D v I)).comp
        ((actionMk (internalModule D v I)).comp (inclusion
          (show pointSylow T v ≤ pointJoin T v I from le_sup_right)))) ⊤) ≤ 1 := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf H).map (actionMk U)
  obtain ⟨⟨E⟩,hA,hi,hd⟩ := c.ten_dimensional_orbit_of_naturalDual_cover e r
  let F : ActionQuotient U ≃* SL(5,ZMod 2) := topEquiv.symm.trans
    ((MulEquiv.subgroupCongr hA.symm).trans E)
  have hs : Function.Surjective A.subtype := by
    intro a
    exact ⟨⟨a,by change a ∈ (I.subgroupOf H).map (actionMk U); rw [hA]; trivial⟩,rfl⟩
  let : IsIrreducible (action U) := (irreducible_comp_surjective_iff A.subtype hs _).mp hi
  obtain ⟨P,hP⟩ := c.join_sylow
  have hP' : (P : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  let q := actionMk U
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (centralizer (U : Set H)))
  have hb := SL5ExteriorSquare.marked_sylow_fixed_finrank_le_one (action U) F hd S
  change Module.finrank (ZMod 2) (fixedSpace (action U) ((P : Subgroup H).map q)) ≤ 1 at hb
  have hj : (⊤ : Subgroup (pointSylow T v)).map
      (inclusion (show pointSylow T v ≤ H from le_sup_right)) =
      (pointSylow T v).subgroupOf H := by
    ext x
    constructor
    · rintro ⟨a,_,rfl⟩
      exact a.property
    · intro hx
      exact ⟨⟨x,hx⟩,mem_top _,Subtype.ext rfl⟩
  rw [fixedSpace_comp_map,←map_map,hj,←hP']
  exact hb

/-- The literal normalizer action on the original quotient. -/
@[expose] def Context.pointQuotientAction (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    pointSylow T v →* MulAut BinaryLinearThree.Group :=
  (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp
      (L.normalizerMonoidHom.comp (inclusion c.escaping.sylow_normalizes)))

/-- The actual original quotient action must contain an outer automorphism. -/
theorem Context.pointQuotientAction_outer_of_naturalDual
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∃ p : pointSylow T v,
      c.pointQuotientAction e p ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let W := ⁅D.fullModule,L⁆
  let P := pointSylow T v
  let := c.reduced.normal
  let := c.reduced.elementary
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  have hPW : P ≤ normalizer (W : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T))
      c.escaping.sylow_normalizes).trans (source_moved_normalizer_local_containment D)
  have hz : sourceMovedFixed D = ⊥ :=
    c.moved_fixed_eq_bot_of_fullModule_centralized
      (c.thompson_centralizes_fullModule_of_naturalDual e r)
  have rcover : BinaryConjugationSection L W (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) := hz.symm ▸ r
  obtain ⟨η,hη⟩ := r.exists_original_quotient_action hPW (by rw [normalizer_eq_top]; exact le_top)
  let a := c.pointQuotientAction e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have ha (p : P) (l : L) : a p (q l) =
      q (L.normalizerMonoidHom (inclusion c.escaping.sylow_normalizes p) l) := by
    change e (quotientAut (pCore 2 L)
      (L.normalizerMonoidHom (inclusion c.escaping.sylow_normalizes p))
      (e.symm (e (QuotientGroup.mk' _ l)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hηa : ∀ p g x, η p (BinaryLinearThree.NaturalDual.action g x) =
      BinaryLinearThree.NaturalDual.action (a p g) (η p x) := by
    intro p g x
    obtain ⟨l,rfl⟩ := hq g
    obtain ⟨w,rfl⟩ := r.onto (Multiplicative.ofAdd x)
    change η p (BinaryLinearThree.NaturalDual.action (q l) (r.coordinates w).toAdd) =
      BinaryLinearThree.NaturalDual.action (a p (q l)) (η p (r.coordinates w).toAdd)
    have hs (k : L) (z : W) :
        (r.coordinates ⟨k*z*(k:G)⁻¹,
          (mem_normalizer_iff.mp (r.normalized k.property) z).mp z.property⟩).toAdd =
        BinaryLinearThree.NaturalDual.action (q k) (r.coordinates z).toAdd := r.equivariant k z
    rw [←hs,hη,ha,hη,←hs]
    apply congrArg (fun z : W => (r.coordinates z).toAdd)
    apply Subtype.ext
    change (p : G)*((l : G)*w*(l : G)⁻¹)*(p : G)⁻¹ =
      ((p : G)*l*(p : G)⁻¹)*((p : G)*w*(p : G)⁻¹)*((p : G)*l*(p : G)⁻¹)⁻¹
    group
  have hinj : Function.Injective r.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [r.kernel_eq,bot_subgroupOf])
  let E : Additive W ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space :=
    LinearEquiv.ofBijective (r.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hinj,r.onto⟩
  let j : W →* U := (subgroupOfEquivOfLe c.orbit_le_join).symm.toMonoidHom.comp
    (inclusion (c.moved_le_of_naturalDual e r))
  let f : BinaryLinearThree.NaturalDual.Space →ₗ[ZMod 2] Additive U :=
    (j.toAdditive.toZModLinearMap 2).comp E.symm.toLinearMap
  have hf : Function.Injective f :=
    ((subgroupOfEquivOfLe c.orbit_le_join).symm.injective.comp
      (inclusion_injective (c.moved_le_of_naturalDual e r))).comp E.symm.injective
  let β := (action U).comp ((actionMk U).comp
    (inclusion (show P ≤ H from le_sup_right)))
  have hfe (p : P) (x : BinaryLinearThree.NaturalDual.Space) :
      f (η p x) = β p (f x) := by
    obtain ⟨w,rfl⟩ := r.onto (Multiplicative.ofAdd x)
    have he (z : W) : E.symm (r.coordinates z).toAdd = Additive.ofMul z :=
      E.symm_apply_apply (Additive.ofMul z)
    change f (η p (r.coordinates w).toAdd) = β p (f (r.coordinates w).toAdd)
    rw [hη]
    change j.toAdditive.toZModLinearMap 2 (E.symm _) =
      action U (actionMk U (inclusion (show P ≤ H from le_sup_right) p))
        (j.toAdditive.toZModLinearMap 2 (E.symm _))
    rw [he,he]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg H.subtype (action_apply U (inclusion
      (show P ≤ H from le_sup_right) p) (Additive.ofMul (j w)))).symm
  let F : fixedSpace η ⊤ →ₗ[ZMod 2] fixedSpace β ⊤ :=
    (f.comp (fixedSpace η ⊤).subtype).codRestrict _ (by
      intro x p
      exact (hfe p x).symm.trans (congrArg f (x.property p)))
  have hF : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  have hb := (LinearMap.finrank_le_finrank_of_injective hF).trans
    (c.orbit_point_fixed_finrank_le_one_of_naturalDual_cover e rcover)
  by_contra hn
  push Not at hn
  have hl := BinaryLinearThree.NaturalDual.two_le_fixed_finrank_of_inner η
    (T.isPGroup'.to_le inf_le_left) a hηa hn
  omega

/-- The original fixed kernel is discharged before detecting the outer point action. -/
theorem Context.pointQuotientAction_outer_of_naturalDual_cover
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∃ p : pointSylow T v,
      c.pointQuotientAction e p ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
  rw [c.naturalDual_cover_fixed_eq_bot e r] at r
  exact c.pointQuotientAction_outer_of_naturalDual e r
end CFSG.Quasithin.Chapter10.PointControl.Constrained

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The natural--dual source row is excluded once the containing actor's
inner action on the original quotient is proved. Models.NaturalDualExclusion
discharges that input on the original context. -/
theorem Context.no_naturalDual_cover_of_pointQuotientAction_inner
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hinner : ∀ p : pointSylow T v,
      c.pointQuotientAction e p ∈ MulAut.innerSubgroup BinaryLinearThree.Group) : False := by
  obtain ⟨p,hp⟩ := c.pointQuotientAction_outer_of_naturalDual_cover e r
  exact hp (hinner p)
end CFSG.Quasithin.Chapter10.PointControl.Constrained
