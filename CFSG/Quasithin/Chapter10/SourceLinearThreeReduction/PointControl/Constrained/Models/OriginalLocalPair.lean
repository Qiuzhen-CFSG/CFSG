module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalLocalPairActions

/-!
# Excluding the original local natural–dual row

The complete containing-action alternatives and the local six-space
exclusions leave only the ten-dimensional exterior-square section. Its
vanishing dual cohomology removes the central attachment from the actual
VI. The whole action quotient is then SL₅(2), with its original two-group
kernel. Its Sylow fixed space has dimension at most one.

If the point Sylow acted innerly on the original SL₃(2) quotient, the local
natural–dual pair would supply two independent fixed vectors in VI. Thus
that point action is outer. But the actual containing flag quotient forces
it to be inner, a contradiction. OriginalLocal recognition consequently
leaves a natural local three-space or the unmarked Suzuki quotient branch.
The original full module, local module and literal VI are kept distinct.

Source.lean uses this reduction in its existing point-control assembly,
without adding a row callback. The local natural exclusion, Suzuki branch
and unconditional ConstrainedExclusionAt remain unproved.

Source: Aschbacher–Smith 10.2.9, printed p.752; the exterior central-cover
calculation is I.1.6, printed p.408. No later generation bound is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
local instance : IsElementaryAbelian 2 (⁅D.moduleSubgroup,L⁆ : Subgroup G) := by
  let := source_original_full_moved_elementary D
  exact IsElementaryAbelian.of_le
    (show ⁅D.moduleSubgroup,L⁆ ≤ ⁅D.fullModule,L⁆ from
      commutator_mono (le_componentOrbit _ _) le_rfl)

omit [Finite G] in
private theorem binary_three (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
  decide

private theorem Context.no_repeated_natural_section_of_local_pair
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {d n : ℕ} (hd : d = 4 ∨ d = 5) (hn : 0 < n) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (_E : ActionEquiv (s.space.toRepresentation.comp (A.subgroupOf N).subtype)
        (repeated (linearNatural BinaryField.two d) n)), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk U)
  dsimp only
  intro N hAN s E
  have hs : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.fully_moved
  let j : Additive U ≃ₗ[ZMod 2] s.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict s.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ h => congrArg Subtype.val h,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  let f : ActionEquiv ((action U).comp A.subtype)
      (repeated (linearNatural BinaryField.two d) n) := {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
    linearEquiv := j.trans E.linearEquiv
    intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }
  exact c.no_repeated_natural_action_of_local_pair e r hd hn f

private theorem Context.no_natural_dual_section_of_local_pair
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {d : ℕ} (hd : d = 4 ∨ d = 5) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (_E : ActionEquiv (s.space.toRepresentation.comp (A.subgroupOf N).subtype)
        (naturalPlusDual d)), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk U)
  dsimp only
  intro N hAN s E
  have hs : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.fully_moved
  let j : Additive U ≃ₗ[ZMod 2] s.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict s.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ h => congrArg Subtype.val h,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  let f : ActionEquiv ((action U).comp A.subtype)
      (naturalPlusDual d) := {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
    linearEquiv := j.trans E.linearEquiv
    intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }
  exact c.no_natural_dual_action_of_local_pair e r hd f

/-- Local natural–dual coordinates give exactly six dimensions. -/
private theorem Context.local_pair_finrank (_c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Module.finrank (ZMod 2) (Additive (⁅D.moduleSubgroup,L⁆ : Subgroup G)) = 6 := by
  have hi : Function.Injective r.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [r.kernel_eq,bot_subgroupOf])
  let f : Additive (⁅D.moduleSubgroup,L⁆ : Subgroup G) ≃ₗ[ZMod 2]
      BinaryLinearThree.NaturalDual.Space :=
    LinearEquiv.ofBijective (r.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hi,r.onto⟩
  rw [f.finrank_eq]
  change Module.finrank (ZMod 2)
    ((Fin 3 → ZMod 2) × Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 6
  rw [Module.finrank_prod,Subspace.dual_finrank_eq,Module.finrank_fin_fun]

/-- The actual local six-space rules out every containing row except the
irreducible exterior-square action, retaining the central section kernel. -/
private theorem Context.exterior_source_action_of_local_pair (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
      IsExteriorFiveSection h.sectionData := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk U)
  let N := offenderSubgroup (action U)
  have a := c.actionFacts_of_three (binary_three e)
  have hAN : A ≤ N := a.classification.2.1
  obtain ⟨h,hs,_,_,_⟩ := c.original_binary_source_action a
  have hsmall (hf : Function.Injective h.sectionData.action)
      (hd : Module.finrank (ZMod 2)
        (h.sectionData.space.toSubmodule ⧸ h.sectionData.central.toSubmodule) ≤ 6) : False :=
    c.no_small_faithful_section_of_local_moved a h.sectionData hf
      (hd.trans_eq (c.local_pair_finrank e r).symm)
  cases hs with
  | sevenFour hf hi E hd => exact (hsmall hf (by omega)).elim
  | sevenDeleted hf hi E =>
    exact (c.no_deletedSeven_source_section a h.sectionData ⟨E⟩).elim
  | linear d hd hf hi E =>
    apply (hsmall hf ?_).elim
    rw [E.linearEquiv.finrank_eq]
    change Module.finrank (ZMod 2) (Fin d → ZMod 2) ≤ 6
    rw [Module.finrank_fin_fun]
    omega
  | orthogonalSix hf hi E =>
    apply (hsmall hf ?_).elim
    rw [E.linearEquiv.finrank_eq,BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
    decide
  | symmetricEight hf hi E =>
    apply (hsmall hf ?_).elim
    rw [E.action.linearEquiv.finrank_eq,BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
    decide
  | exteriorFive hf hi E hd => exact ⟨h,hf,hi,⟨E⟩,hd⟩
  | naturalDual d hd E =>
    exact (c.no_natural_dual_section_of_local_pair e r hd N hAN h.sectionData E.some).elim
  | repeatedNatural d n hd hn hb E =>
    exact (c.no_repeated_natural_section_of_local_pair e r hd hn N hAN h.sectionData E.some).elim

/-- The whole literal VI is ten-dimensional and irreducible, and its full
action quotient is SL₅(2), when its local submodule is a natural–dual pair. -/
private theorem Context.ten_dimensional_orbit_of_local_pair (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    Nonempty (A ≃* SL(5,ZMod 2)) ∧ A = ⊤ ∧
      IsIrreducible ((action (internalModule D v I)).comp A.subtype) ∧
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 10 := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let H := pointJoin T v I
  let U := internalModule D v I
  let A := (I.subgroupOf H).map (actionMk U)
  let N := offenderSubgroup (action U)
  have a := c.actionFacts_of_three (binary_three e)
  have hAN : A ≤ N := a.classification.2.1
  obtain ⟨h,hf,hi,⟨E⟩,hd⟩ := c.exterior_source_action_of_local_pair e r
  have hm : moved ((action U).comp N.subtype) (A.subgroupOf N) = ⊤ := by
    rw [moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.fully_moved
  have hs : h.sectionData.space.toSubmodule = ⊤ := h.sectionData.space_eq.trans hm
  let j := h.sectionData.fullProjection hm
  let := hi
  let : IsIrreducible (Representation.dual (h.sectionData.action.comp
      (A.subgroupOf N).subtype)) := isIrreducible_dual
  let := SL5TenDimensional.h1_subsingleton_of_group_equiv
    (Representation.dual (h.sectionData.action.comp (A.subgroupOf N).subtype)) E
    (by rw [Subspace.dual_finrank_eq,hd])
  let p : IntertwiningMap (((action U).comp N.subtype).comp (A.subgroupOf N).subtype)
      (h.sectionData.action.comp (A.subgroupOf N).subtype) := {
    toLinearMap := j
    isIntertwining' := fun g => LinearMap.ext fun x =>
      h.sectionData.fullProjection_intertwines hm g x }
  have hp : OneCohomology.IsCover p := by
    refine ⟨h.sectionData.fullProjection_surjective hm,?_,?_⟩
    · intro x hx g
      exact (h.sectionData.fullProjection_eq_zero_iff hm x).mp hx g
    · rw [SourceCompletion.coinvariants_eq_moved]
      exact hm
  have hj : Function.Injective j := BinaryParabolicNatural.cover_injective_of_H1_zero p hp
    Module.finrank_zero_of_subsingleton
  have hsur : Function.Surjective j := h.sectionData.fullProjection_surjective hm
  let f : ActionEquiv ((action U).comp A.subtype)
      (h.sectionData.action.comp (A.subgroupOf N).subtype) := {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm
    linearEquiv := LinearEquiv.ofBijective j ⟨hj,hsur⟩
    intertwines := fun g x => h.sectionData.fullProjection_intertwines hm
      ⟨g,hAN g.property⟩ x }
  have hi' : IsIrreducible ((action U).comp A.subtype) :=
    ExtensionConsequences.irreducible_of_equiv f hi
  have hten : Module.finrank (ZMod 2) (Additive U) = 10 := f.linearEquiv.finrank_eq.trans hd
  let eA : A ≃* SL(5,ZMod 2) := (subgroupOfEquivOfLe hAN).symm.trans E
  let K := I.subgroupOf H
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  let : A.Normal := Normal.map inferInstance (actionMk U) (QuotientGroup.mk'_surjective _)
  let := hi'
  exact ⟨⟨eA⟩,BinaryLinearNormalActors.normal_ten_dimensional_eq_top
    (action U) (action_faithful U) A eA hten,hi',hten⟩

private theorem Context.orbit_point_fixed_finrank_le_one_of_local_pair
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
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
  obtain ⟨⟨E⟩,hA,hi,hd⟩ := c.ten_dimensional_orbit_of_local_pair e r
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

private theorem Context.pointQuotientAction_outer_of_local_pair
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∃ p : pointSylow T v,
      c.pointQuotientAction e p ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let W := ⁅D.moduleSubgroup,L⁆
  let P := pointSylow T v
  let := c.reduced.normal
  let := c.reduced.elementary
  let : IsElementaryAbelian 2 W := inferInstance
  have hPW : P ≤ normalizer (W : Set G) :=
    ((le_inf inf_le_left c.escaping.sylow_normalizes).trans le_sup_right).trans
      c.halfJoin_normalizes_local_moved
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
    (inclusion (c.local_moved_le))
  let f : BinaryLinearThree.NaturalDual.Space →ₗ[ZMod 2] Additive U :=
    (j.toAdditive.toZModLinearMap 2).comp E.symm.toLinearMap
  have hf : Function.Injective f :=
    ((subgroupOfEquivOfLe c.orbit_le_join).symm.injective.comp
      (inclusion_injective (c.local_moved_le))).comp E.symm.injective
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
    (c.orbit_point_fixed_finrank_le_one_of_local_pair e r)
  by_contra hn
  push Not at hn
  have hl := BinaryLinearThree.NaturalDual.two_le_fixed_finrank_of_inner η
    (T.isPGroup'.to_le inf_le_left) a hηa hn
  omega

private theorem Context.pointQuotientAction_inner_of_local_pair
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∀ p : pointSylow T v,
      c.pointQuotientAction e p ∈ MulAut.innerSubgroup BinaryLinearThree.Group := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf H).map (actionMk U)
  obtain ⟨⟨E⟩,hA,_,_⟩ := c.ten_dimensional_orbit_of_local_pair e r
  let F : ActionQuotient U ≃* BinaryLinear.OuterCyclic.LinearGroup 5 :=
    (topEquiv.symm.trans ((MulEquiv.subgroupCongr hA.symm).trans E)).trans
      (BinaryLinear.OuterCyclic.slEquivLinear 5)
  let q := actionMk U
  let f := F.toMonoidHom.comp q
  have hf : Function.Surjective f := F.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ F.injective]
    exact c.join_action_kernel_two_of_binary_actor (Or.inr rfl) E
  obtain ⟨S,hS⟩ := c.join_sylow
  have hS' : (S : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  let B := L ⊔ pointSylow T v
  have hBH : B ≤ H := sup_le (c.escaping.strict.le.trans le_sup_left) le_sup_right
  let K := B.subgroupOf H
  let k : K ≃* B := subgroupOfEquivOfLe hBH
  let b := pCoreJoinAction 2 c.escaping.sylow_normalizes
  let a : K →* MulAut BinaryLinearThree.Group :=
    (MulAut.congr e).toMonoidHom.comp (b.comp k.toMonoidHom)
  have hi : MulAut.innerSubgroup BinaryLinearThree.Group ≤ a.range := by
    rw [←MulAut.map_innerSubgroup_congr e]
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨z,hz⟩ := inner_le_pCoreJoinAction_range 2 c.escaping.sylow_normalizes hx
    refine ⟨k.symm z,?_⟩
    change MulAut.congr e (b (k (k.symm z))) = MulAut.congr e x
    rw [k.apply_symm_apply,hz]
  have ha : pCore 2 K ≤ a.ker := by
    intro x hx
    have hk : k x ∈ pCore 2 B := by
      rw [←pCore_map_iso 2 k]
      exact mem_map_of_mem k.toMonoidHom hx
    have hb : b (k x) = 1 :=
      pCore_le_pCoreJoinAction_kernel 2 c.escaping.sylow_normalizes hk
    change MulAut.congr e (b (k x)) = 1
    rw [hb,map_one]
  have hSK : (S : Subgroup H) ≤ K := by
    rw [hS']
    exact comap_mono le_sup_right
  let := D.quasisimple
  let : Group.IsPerfect BinaryLinearThree.Group :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (L ⧸ pCore 2 L) := Selection.ModuleChoice.component_quotient_simple
    D (fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem))
  let : IsSimpleGroup BinaryLinearThree.Group := e.symm.isSimpleGroup
  let : Group.IsNilpotent (MulAut.Outer BinaryLinearThree.Group) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.isNilpotent
  have hh := BinaryLinear.sylow_overgroup_quotient_action_inner
    Matrix.PSL3Two.center_eq_bot f hf S K hSK a hi
    (hfk.comap_subtype) ha
  intro p
  exact hh ⟨k.symm (inclusion le_sup_right p),rfl⟩

/-- No natural–dual marking of the whole local moved subgroup survives.
The local fixed vectors force an outer point action, whereas the actual
containing flag quotient forces that same action to be inner. -/
theorem Context.no_local_naturalDual (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False := by
  obtain ⟨p,hp⟩ := c.pointQuotientAction_outer_of_local_pair e r
  exact hp (c.pointQuotientAction_inner_of_local_pair e r p)

/-- The original binary branch has an actual natural local three-space.
The Suzuki quotient alternative remains separate and is not a marking. -/
theorem Context.original_local_natural_or_suzuki (c : Context D t v I) :
    (∃ f : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
      Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
        (BinaryLinearThree.W.comp (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) ∨
    ∃ m : ℕ, 0 < m ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rcases c.original_local_marking_or_suzuki with ⟨e,h | ⟨h⟩⟩ | h
  · exact Or.inl ⟨e,h⟩
  · exact (c.no_local_naturalDual e h.some).elim
  · exact Or.inr h

end CFSG.Quasithin.Chapter10.PointControl.Constrained
