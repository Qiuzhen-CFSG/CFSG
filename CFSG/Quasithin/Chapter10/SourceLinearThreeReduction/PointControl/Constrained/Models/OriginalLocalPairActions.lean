module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalLocal

/-!
# Containing actions above the original local natural–dual module

The literal local moved subgroup lies in VI and is fixed by J(T). Its
intersection with the containing central section kernel is trivial: any
such vector centralizes L and hence is zero by the original fixed-kernel
calculation. A faithful central section must therefore be larger than this
local subgroup, since otherwise Thompson movement on VI would vanish.

For a local natural–dual pair, repeated natural containing modules of
degree four or five cannot contain both inequivalent three-dimensional
constituents. In a containing natural–dual sum, their embedding kills the
original two-core, contradicting its actual parabolic image. These arguments
use the local subgroup throughout; they do not identify it with the full
original moved subgroup. OriginalLocalPair applies the exclusions to B.5.1.

Source: Aschbacher–Smith 10.2.9, printed pp.751–752. The coordinate arguments
extend Models.NaturalDualRows and Models.NaturalDualSplit to the local module.
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

private theorem end_eq_one_of_surjective {X Y : Type*}
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (f : X →ₗ[ZMod 2] Y) (hf : Function.Surjective f)
    (g : Y →ₗ[ZMod 2] Y) (hg : ∀ x, g (f x) = f x) : g = 1 := by
  apply LinearMap.ext
  intro y
  obtain ⟨x,rfl⟩ := hf y
  exact hg x

/-- A faithful containing central section is larger than the literal local moved subgroup. -/
theorem Context.no_small_faithful_section_of_local_moved
    (c : Context D t v I) (a : ActionFacts c)
    :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    letI := (inferInstance : IsElementaryAbelian 2 (⁅D.moduleSubgroup,L⁆ : Subgroup G))
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∀ (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N)),
      Function.Injective s.action →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≤
        Module.finrank (ZMod 2) (Additive (⁅D.moduleSubgroup,L⁆ : Subgroup G)) → False := by
  let H := pointJoin T v I
  let U := internalModule D v I
  have hspan := c.local_moved_le
  let W := ⁅D.moduleSubgroup,L⁆
  let := c.reduced.normal
  let := c.reduced.elementary
  let : IsElementaryAbelian 2 W := (inferInstance : IsElementaryAbelian 2 (⁅D.moduleSubgroup,L⁆ : Subgroup G))
  let A := (I.subgroupOf H).map (actionMk U)
  let N := offenderSubgroup (action U)
  dsimp only
  intro s hfaith hdim
  have hAN : A ≤ N := a.classification.2.1
  have hm : moved ((action U).comp N.subtype) (A.subgroupOf N) = ⊤ := by
    rw [moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.fully_moved
  let p := s.fullProjection hm
  let j : W →* U := (subgroupOfEquivOfLe c.orbit_le_join).symm.toMonoidHom.comp
    (inclusion hspan)
  let jlin : Additive W →ₗ[ZMod 2] Additive U := j.toAdditive.toZModLinearMap 2
  let f := p.comp jlin
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    have hfix := (s.fullProjection_eq_zero_iff hm (jlin w)).mp hw
    have hc : (w.toMul : G) ∈ centralizer (L : Set G) := by
      intro l hl
      let lH : H := ⟨l,(c.escaping.strict.le.trans le_sup_left) hl⟩
      let lA : A := ⟨actionMk U lH,mem_map_of_mem _ (c.escaping.strict.le hl)⟩
      have hh := hfix ⟨⟨lA,hAN lA.property⟩,lA.property⟩
      have hh' := congrArg (fun z : Additive U => ((z.toMul : H) : G)) hh
      have ha := congrArg H.subtype (action_apply U lH (jlin w))
      have he : l * (w.toMul : G) * l⁻¹ = (w.toMul : G) := ha.symm.trans hh'
      exact mul_inv_eq_iff_eq_mul.mp he
    have hz : (w.toMul : G) ∈ sourceMovedFixed D := ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) w.toMul.property,hc⟩
    rw [c.moved_fixed_eq_bot] at hz
    exact Additive.toMul.injective (Subtype.ext (mem_bot.mp hz))
  have hsur : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    have he : Module.finrank (ZMod 2) (Additive (⁅D.moduleSubgroup,L⁆ : Subgroup G)) =
        Module.finrank (ZMod 2) f.range := (LinearEquiv.ofInjective f hfi).finrank_eq
    exact le_antisymm (Submodule.finrank_le _) (hdim.trans he.le)
  obtain ⟨P,hP⟩ := c.join_sylow
  have hPN : (elementaryAbelianMaxJ (pointSylow T v)).subgroupOf H ≤
      N.comap (actionMk U) := by
    have hmap : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (pointSylow T v) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
    have he : (elementaryAbelianMaxJ (pointSylow T v)).subgroupOf H =
        elementaryAbelianMaxJ (P : Subgroup H) := by
      rw [←hmap]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he]
    exact map_le_iff_le_comap.mp (thompson_image_le P U)
  apply a.prepared.thompson_moves
  intro z hz w hw
  have hJS : elementaryAbelianMaxJ (pointSylow T v) ≤ pointSylow T v :=
    sSup_le fun _ hA => hA.1
  have hzH : z ∈ H := (show pointSylow T v ≤ H from le_sup_right)
    (hJS hz)
  let zH : H := ⟨z,hzH⟩
  let zN : N := ⟨actionMk U zH,hPN hz⟩
  have hact' (u : Additive W) : s.central.quotientRepresentation zN (f u) = f u := by
    change s.central.quotientRepresentation zN (p (jlin u)) = p (jlin u)
    rw [←s.fullProjection_intertwines hm zN]
    apply congrArg p
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have ha := congrArg H.subtype (action_apply U zH (jlin u))
    change _ = z * (u.toMul : G) * z⁻¹ at ha
    rw [a.prepared.thompson_eq] at hz
    have hWV : W ≤ D.moduleSubgroup := le_normalizer_iff_commutator_le_left.mp
      ((le_componentOrbit L T).trans D.orbit_normalizes_module)
    exact ha.trans (by
      rw [←c.local_thompson_fixed hz u.toMul (hWV u.toMul.property),mul_inv_cancel_right]
      rfl)
  have hact : s.central.quotientRepresentation zN = 1 :=
    end_eq_one_of_surjective f hsur _ hact'
  have hzq : actionMk U zH = 1 := congrArg Subtype.val
    (hfaith (hact.trans (map_one s.action).symm))
  have hzk : zH ∈ centralizer (U : Set H) := (QuotientGroup.eq_one_iff zH).mp hzq
  exact congrArg H.subtype (hzk ⟨w,c.orbit_le_join hw⟩ hw)

/-- Repeated natural containing actions cannot contain the original local natural–dual pair. -/
theorem Context.no_repeated_natural_action_of_local_pair
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {d n : ℕ} (hd : d = 4 ∨ d = 5) (_hn : 0 < n) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (_E : ActionEquiv ((action (internalModule D v I)).comp A.subtype)
      (repeated (linearNatural BinaryField.two d) n)), False := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let R := orbitModule D v I
  let K := I.subgroupOf H
  let := c.reduced.normal
  let := c.reduced.elementary
  let W := ⁅D.moduleSubgroup,L⁆
  let : IsElementaryAbelian 2 W := inferInstance
  let A := K.map (actionMk U)
  dsimp only
  intro E
  have hspan := c.local_moved_le
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ρ : Representation (ZMod 2) L BinaryLinearThree.Vector := BinaryLinearThree.W.comp q
  let η : Representation (ZMod 2) L (Module.Dual (ZMod 2) BinaryLinearThree.Vector) := BinaryLinearThree.W.dual.comp q
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible η := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  let f : I →* A := ((actionMk U).subgroupMap K).comp
    (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm.toMonoidHom
  let φ := E.groupEquiv.toMonoidHom.comp f
  let σ := (linearNatural BinaryField.two d).comp φ
  let τ := (repeated (linearNatural BinaryField.two d) n).comp φ
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
      exact (congrArg E.linearEquiv ha.symm).trans (E.intertwines (f i) _) }
  have hzero (b : η.IntertwiningMap ρ) : b = 0 := by
    let b' : BinaryLinearThree.W.dual.IntertwiningMap BinaryLinearThree.W := {
      toLinearMap := b.toLinearMap
      isIntertwining' := by intro g; obtain ⟨l,rfl⟩ := hq g; exact b.isIntertwining' l }
    exact Representation.IntertwiningMap.ext
      (congrArg (fun z : BinaryLinearThree.W.dual.IntertwiningMap BinaryLinearThree.W => z.toLinearMap)
        (BinaryLinearThree.NaturalDual.dual_natural_zero b'))
  have hdim : Module.finrank (ZMod 2) (Fin d → BinaryField.two.Carrier) <
      Module.finrank (ZMod 2) BinaryLinearThree.Vector +
        Module.finrank (ZMod 2) (Module.Dual (ZMod 2) BinaryLinearThree.Vector) := by
    change Module.finrank (ZMod 2) (Fin d → ZMod 2) < _
    rw [Subspace.dual_finrank_eq]
    change Module.finrank (ZMod 2) (Fin d → ZMod 2) <
      Module.finrank (ZMod 2) (Fin 3 → ZMod 2) + Module.finrank (ZMod 2) (Fin 3 → ZMod 2)
    rw [Module.finrank_fin_fun,Module.finrank_fin_fun]
    omega
  obtain ⟨f,hfi⟩ := r.exists_injective_intertwiner s c.escaping.strict.le hspan
  exact no_small_repeated_inequivalent_pair (ρ := ρ) (η := η) hzero hdim
    (σ.comp (inclusion c.escaping.strict.le))
    (τ.comp (inclusion c.escaping.strict.le)) (fun _ _ _ => rfl) f hfi

/-- The original local natural–dual pair excludes a natural–dual containing action. -/
theorem Context.no_natural_dual_action_of_local_pair
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
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
  let W := ⁅D.moduleSubgroup,L⁆
  let : IsElementaryAbelian 2 W := inferInstance
  let A := K.map (actionMk U)
  dsimp only
  intro E
  have hspan := c.local_moved_le
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
  apply c.no_binary_actor_of_original_core_killed (c.actionFacts_of_three (binary_three e)) hz hd E.groupEquiv
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

end CFSG.Quasithin.Chapter10.PointControl.Constrained
