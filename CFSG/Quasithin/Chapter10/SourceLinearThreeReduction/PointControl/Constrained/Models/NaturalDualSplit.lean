module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDualRows
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryLinear
public import Theory.Representation.SmallDualPair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankOneExclusion

/-!
# Natural--dual covers in the constrained containing action

An original natural--dual three-space pair cannot embed into a containing
natural--dual module of degree four or five. Opposite coordinate projections
split off a simple summand; the perfect actor fixes its complement of dimension
at most two. This kills the original two-core on the containing action,
contrary to proper local-component placement in the binary actor.

A positive original fixed kernel would force local Thompson movement and a
natural quotient of order eight, contradicting the original quotient of order
sixty-four. The complete source conclusion therefore leaves only a faithful
ten-dimensional irreducible SL₅(2) section. Vanishing cohomology and the linear
normalizer calculation identify it with the whole original orbit and its full
actor. The final exclusion of this case, positive natural covers, general quiet
preparation and the retained four-natural row remain with the final assembly
owner qt-d-10-nona5-point-constrained.

Source: Aschbacher--Smith 10.2.9, printed pp.751--753.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- A proper smaller local component in a binary containing actor cannot
kill its entire original two-core on the literal reduced orbit. -/
theorem Context.no_binary_actor_of_original_core_killed (c : Context D t v I)
    (a : ActionFacts c) (hz : center (L ⧸ pCore 2 L) = ⊥) {d : ℕ} (hd : d = 4 ∨ d = 5) :
    letI := c.reduced.normal
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (_E : A ≃* SL(d,ZMod 2)),
      (∀ l : L, l ∈ pCore 2 L →
        actionMk (internalModule D v I)
          ⟨l,(c.escaping.strict.le.trans le_sup_left) l.property⟩ = 1) → False := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let K := L.subgroupOf H
  let q := actionMk U
  let A := (I.subgroupOf H).map q
  let B := (K.map q).subgroupOf A
  let f := q.subgroupMap K
  have hLH : L ≤ H := c.escaping.strict.le.trans le_sup_left
  let k : K ≃* L := subgroupOfEquivOfLe hLH
  dsimp only
  intro E hkill
  have hk : pCore 2 K ≤ f.ker := by
    intro l hl
    apply Subtype.ext
    exact hkill (k l) (by rw [←pCore_map_iso 2 k]; exact mem_map_of_mem k.toMonoidHom hl)
  have hm : (pCore 2 K).map f = pCore 2 (K.map q) := by
    rw [←f.comap_pCore_of_ker_isPGroup (q.subgroupMap_surjective K)
      (c.small_image_twoCore a hz).1,map_comap_eq_self_of_surjective (q.subgroupMap_surjective K)]
  have hz : pCore 2 (K.map q) = ⊥ := by
    rw [←hm]
    apply bot_unique
    rintro _ ⟨l,hl,rfl⟩
    exact hk hl
  have hKA : K.map q ≤ A := map_mono (comap_mono c.escaping.strict.le)
  let eB : B ≃* K.map q := subgroupOfEquivOfLe hKA
  have hzB : pCore 2 B = ⊥ := by
    apply (map_injective (f := eB.toMonoidHom) eB.injective)
    rw [pCore_map_iso 2 eB,hz,Subgroup.map_bot]
  obtain ⟨eb⟩ := c.small_local_quotient a
  let b : B ≃* (L ⧸ pCore 2 L) :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hzB.symm)).trans eb
  let := D.quasisimple
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv b.symm
  let : IsQuasisimple A := a.classification.1
  obtain ⟨hp,S,_,hl⟩ := a.small_local
  have ht : (⊤ : Subgroup A).IsCComponent :=
    (show IsComponent A ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  apply hp.ne
  apply ChapterA.Section03.SourceEmbeddings.eq_of_binary_linear_four_or_five
    (S.mapSurjective (q.subgroupMap_surjective (I.subgroupOf H))) hl ht le_top hd
  exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨topEquiv.trans (E.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm)⟩⟩

/-- The literal orbit cannot be a small natural--dual sum. -/
theorem Context.no_natural_dual_action_of_naturalDual
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {d : ℕ} (hd : d = 4 ∨ d = 5) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (_E : ActionEquiv ((action (internalModule D v I)).comp A.subtype)
      (naturalPlusDual d)), False := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let R := orbitModule D v I
  let K := I.subgroupOf H
  let := c.reduced.normal
  let := c.reduced.elementary
  let W := ⁅D.fullModule,L⁆
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  let A := K.map (actionMk U)
  dsimp only
  intro E
  have hspan := c.moved_le_of_naturalDual e r
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ρ : Representation (ZMod 2) L (Fin 3 → ZMod 2) :=
    (specialLinearNatural (k := ZMod 2) 3).comp q
  let η : Representation (ZMod 2) L (Module.Dual (ZMod 2) BinaryLinearThree.Vector) :=
    BinaryLinearThree.W.dual.comp q
  let : IsIrreducible η := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let f : I →* A := ((actionMk U).subgroupMap K).comp
    (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm.toMonoidHom
  let φ := E.groupEquiv.toMonoidHom.comp f
  let σ : Representation (ZMod 2) I (Fin d → ZMod 2) :=
    (linearNatural BinaryField.two d).comp φ
  let τ := σ.prod σ.dual
  let j : R ≃* U := (subgroupOfEquivOfLe c.orbit_le_join).symm
  let s : BinaryConjugationSection I R ⊥ τ := {
    section_le := c.orbit_le_component
    kernel_le := bot_le
    normalized := le_normalizer_conjugateSpanBy _ _
    coordinates := {
      toFun w := Multiplicative.ofAdd (E.linearEquiv (Additive.ofMul (j w)))
      map_one' := by change E.linearEquiv (Additive.ofMul (j 1)) = 0; rw [map_one]; exact E.linearEquiv.map_zero
      map_mul' x y := by
        change E.linearEquiv (Additive.ofMul (j (x*y))) =
          E.linearEquiv (Additive.ofMul (j x)) + E.linearEquiv (Additive.ofMul (j y))
        rw [map_mul]; exact E.linearEquiv.map_add _ _ }
    onto := by
      intro w
      exact ⟨j.symm (E.linearEquiv.symm w.toAdd).toMul,by
        change E.linearEquiv (Additive.ofMul (j (j.symm _))) = w.toAdd
        rw [j.apply_symm_apply]
        exact E.linearEquiv.apply_symm_apply _⟩
    kernel_eq := by
      ext w
      change E.linearEquiv (Additive.ofMul (j w)) = 0 ↔ (w:G) = 1
      rw [E.linearEquiv.map_eq_zero_iff]
      change j w = 1 ↔ (w:G) = 1
      rw [j.map_eq_one_iff]
      exact Subtype.val_inj.symm
    equivariant := by
      intro i w
      have ha : action U (f i).val (Additive.ofMul (j w)) =
          Additive.ofMul (j ⟨(i:G)*w*(i:G)⁻¹,
            (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _ i.property) w).mp w.property⟩) := by
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg H.subtype
          (action_apply U ⟨i,(show I ≤ H from le_sup_left) i.property⟩ (Additive.ofMul (j w)))
      have he := (congrArg E.linearEquiv ha.symm).trans (E.intertwines (f i) _)
      have hh : (naturalPlusDual d) (φ i) = τ i := by
        apply LinearMap.ext
        intro z
        apply Prod.ext
        · rfl
        · apply LinearMap.ext
          intro x
          change z.2 (linearNatural BinaryField.two d ((φ i)⁻¹) x) =
            z.2 (linearNatural BinaryField.two d (φ i⁻¹) x)
          rw [map_inv φ]
      exact he.trans (LinearMap.congr_fun hh _) }
  have hzero (b : η.IntertwiningMap ρ) : b = 0 := by
    let b' : BinaryLinearThree.W.dual.IntertwiningMap BinaryLinearThree.W := {
      toLinearMap := b.toLinearMap
      isIntertwining' := by intro g; obtain ⟨l,rfl⟩ := hq g; exact b.isIntertwining' l }
    exact Representation.IntertwiningMap.ext
      (congrArg (fun z : BinaryLinearThree.W.dual.IntertwiningMap BinaryLinearThree.W => z.toLinearMap)
        (BinaryLinearThree.NaturalDual.dual_natural_zero b'))
  obtain ⟨F,hF⟩ := r.exists_injective_intertwiner s c.escaping.strict.le hspan
  let σL : Representation (ZMod 2) L (Fin d → ZMod 2) := σ.comp (inclusion c.escaping.strict.le)
  let F' : (ρ.prod η).IntertwiningMap (σL.prod σL.dual) := {
    toLinearMap := F.toLinearMap
    isIntertwining' := by
      intro l
      apply LinearMap.ext
      intro z
      have hh := LinearMap.congr_fun (F.isIntertwining' l) z
      apply hh.trans
      apply Prod.ext
      · rfl
      · apply LinearMap.ext
        intro x
        change (F z).2 (σ ((inclusion c.escaping.strict.le l)⁻¹) x) =
          (F z).2 (σ (inclusion c.escaping.strict.le l⁻¹) x)
        rw [map_inv (inclusion c.escaping.strict.le)] }
  have hL : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using D.maximal.1.1.subgroupOf_of_le
      (show L ≤ L from le_rfl) (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
  let := hL.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom) topEquiv.surjective
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center SL(3,ZMod 2) at hh
    rw [_root_.BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 3),mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  apply c.no_binary_actor_of_original_core_killed (c.actionFacts_of_naturalDual e r) hz hd E.groupEquiv
  intro l hl
  have hql : q l = 1 := by
    change e (QuotientGroup.mk' _ l) = 1
    have he : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    exact (congrArg e he).trans (map_one e)
  have hρ : ρ l = 1 := by change BinaryLinearThree.W (q l) = 1; rw [hql,map_one]
  have hη : η l = 1 := by change BinaryLinearThree.W.dual (q l) = 1; rw [hql,map_one]
  have hσ := Representation.SmallDualPair.fixes_of_pair_embedding
    (ρ := ρ) (η := η) (σ := σL)
    (by change Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3; rw [Module.finrank_fin_fun])
    (by rw [Subspace.dual_finrank_eq]; change Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3; rw [Module.finrank_fin_fun])
    (by change Module.finrank (ZMod 2) (Fin d → ZMod 2) ≤ 5; rw [Module.finrank_fin_fun]; omega)
    hzero F' hF l hρ hη
  have hφ : φ (inclusion c.escaping.strict.le l) = 1 := by
    apply ChapterK.Linear.Natural.natural_injective BinaryField.two d
    exact hσ.trans (map_one (linearNatural BinaryField.two d)).symm
  have hf : f (inclusion c.escaping.strict.le l) = 1 := E.groupEquiv.injective
    (hφ.trans (map_one E.groupEquiv).symm)
  exact congrArg Subtype.val hf

/-- The literal containing moved section cannot be a natural--dual sum. -/
theorem Context.no_natural_dual_section_of_naturalDual
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
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
    exact c.fully_moved_of_moved_le (c.moved_le_of_naturalDual e r)
  let j : Additive U ≃ₗ[ZMod 2] s.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict s.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ h => congrArg Subtype.val h,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  let f : ActionEquiv ((action U).comp A.subtype)
      (naturalPlusDual d) := {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
    linearEquiv := j.trans E.linearEquiv
    intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }
  exact c.no_natural_dual_action_of_naturalDual e r hd f

/-- The ten-dimensional faithful central section, including its actual actor. -/
@[expose] def IsExteriorFiveSection
    {Q X : Type*} [Group Q] [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) Q X} {A : Subgroup Q} (s : MovedSection ρ A) : Prop :=
  Function.Injective s.action ∧ IsIrreducible (s.action.comp A.subtype) ∧
    Nonempty (A ≃* SL(5,ZMod 2)) ∧
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10

/-- The remaining source action is the irreducible ten-dimensional SL₅(2)
section. Its original central kernel and the complete B.5.1 conclusion remain. -/
theorem Context.exterior_source_action_of_naturalDual
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
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
  have a := c.actionFacts_of_naturalDual e r
  have hAN : A ≤ N := a.classification.2.1
  obtain ⟨h,hs,_⟩ := c.remaining_source_action_of_naturalDual e r
  cases hs with
  | exteriorFive hf hi E hd => exact ⟨h,hf,hi,⟨E⟩,hd⟩
  | naturalDual d hd E =>
    exact (c.no_natural_dual_section_of_naturalDual e r hd N hAN h.sectionData E.some).elim

/-- In the local Thompson-moving branch the original moved quotient has
exactly eight elements. This uses minimality and the completed rank-one
exclusion, and keeps the original fixed kernel. -/
theorem Context.moved_quotient_card_eight_of_local_thompson_moves
    (c : Context D t v I)
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) L X}
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) :
    Nat.card X = 8 := by
  have hb := (c.natural_of_local_thompson_moves hJ).resolve_left c.no_rankOneNatural
  obtain ⟨e,⟨s⟩⟩ := hb
  have hc := r.card_section.symm.trans s.card_section
  have hn : Nat.card (sourceMovedFixed D) ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
  have hx : Nat.card (Fin 3 → ZMod 2) = 8 := by simp
  rw [hx] at hc
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn) hc

/-- The original natural--dual cover has no positive fixed kernel: local
Thompson movement would make the same quotient have both 8 and 64 elements. -/
theorem Context.naturalDual_cover_fixed_eq_bot
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    sourceMovedFixed D = ⊥ := by
  have hquiet : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
    by_contra hn
    have hc := c.moved_quotient_card_eight_of_local_thompson_moves hn r
    have hd : Module.finrank (ZMod 2) BinaryLinearThree.NaturalDual.Space = 6 := by
      change Module.finrank (ZMod 2)
        ((Fin 3 → ZMod 2) × Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 6
      rw [Module.finrank_prod,Subspace.dual_finrank_eq,Module.finrank_fin_fun]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd] at hc
    norm_num at hc
  by_contra hn
  have hf : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥ := by
    intro hz
    apply hn
    rw [c.moved_fixed_eq_orbit_fixed]
    apply bot_unique
    apply (inf_le_inf_right _ ?_).trans_eq hz
    exact le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
  exact Selection.ModuleChoice.local_thompson_moves_of_full_fixed_ne_bot D c.many hf hquiet

/-- The original fixed kernel is discharged, so every natural--dual cover
has the same single remaining ten-dimensional containing section. -/
theorem Context.exterior_source_action_of_naturalDual_cover
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
      IsExteriorFiveSection h.sectionData := by
  have hz := c.naturalDual_cover_fixed_eq_bot e r
  rw [hz] at r
  exact c.exterior_source_action_of_naturalDual e r

/-- The remaining cover case has a literal whole SL₅(2) action on the
original ten-dimensional orbit; its original fixed kernel was discharged. -/
theorem Context.ten_dimensional_orbit_of_naturalDual_cover
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
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
  let U := internalModule D v I
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk U)
  let N := offenderSubgroup (action U)
  have hz := c.naturalDual_cover_fixed_eq_bot e r
  rw [hz] at r
  have hspan := c.moved_le_of_naturalDual e r
  have a := c.actionFacts_of_naturalDual e r
  have hAN : A ≤ N := a.classification.2.1
  obtain ⟨h,hf,hi,⟨E⟩,hd⟩ := c.exterior_source_action_of_naturalDual e r
  obtain ⟨_,hI,hV⟩ := c.exterior_five_section_full hspan N hAN h.sectionData E hi hd
  exact ⟨⟨(subgroupOfEquivOfLe hAN).symm.trans E⟩,
    c.actor_eq_top_of_exterior_five_section hspan N hAN h.sectionData E hi hd,hI,hV⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
