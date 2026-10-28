module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalNaturalOrbit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalSelection

/-!
# Single containing actions on the original local natural orbit

A natural local three-space generates only one natural constituent in a
repeated containing module. It cannot generate a natural–dual containing
module: the dimension and duality constraints on restriction exclude this.
Applying these facts to the literal B.5.1 section leaves the natural four/five,
orthogonal six/seven, or exterior ten actions on the smaller orbit, with its
exact original action kernel. The seven-dimensional augmentation cover is
then excluded by its Sylow fixed vectors.

Source: Aschbacher–Smith 10.2.9, printed p.752. The Source consumer retains
this smaller orbit and its original VI kernel in the remaining endgame.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open BinaryNaturalDual.VectorStabilizers
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Repetition in the smaller orbit has multiplicity one because its local
generator is an actual natural three-space. -/
theorem Context.repeated_multiplicity_one_of_local_seed_of_local_natural
    (c : Context D t v I)
    (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1)
    {d n : ℕ} (hd : d = 4 ∨ d = 5) (hn : 0 < n) :
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk ((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)))
    ∀ (_E : ActionEquiv ((action ((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I))).comp A.subtype)
      (repeated (linearNatural BinaryField.two d) n)), n = 1 := by
  obtain ⟨e,⟨r⟩⟩ := h
  have hf : LocalNaturalCover D := ⟨e,⟨r⟩⟩
  let H := pointJoin T v I
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
  let R := conjugateSpanBy (zpowers u) I
  let K := I.subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let W := ⁅D.moduleSubgroup,L⁆
  let : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le
    (show W ≤ ⁅D.fullModule,L⁆ from commutator_mono (le_componentOrbit _ _) le_rfl)
  let A := K.map (actionMk U)
  dsimp only
  intro E
  have hWI : W ≤ I := (commutator_mono (le_componentOrbit _ _) le_rfl).trans
    ((source_full_moved_le_component D).trans c.escaping.strict.le)
  have hRI : R ≤ I := conjugateSpanBy_le_self (zpowers_le.mpr (hWI hu.1))
  have hRH : R ≤ H := hRI.trans le_sup_left
  have hspan : W ≤ R := by
    change ⁅D.moduleSubgroup,L⁆ ≤ conjugateSpanBy (zpowers u) I
    rw [←c.local_orbit_eq_seed_orbit_of_local_natural hf hu hne]
    exact le_conjugateSpanBy _ _
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ρ : Representation (ZMod 2) L (Fin 3 → ZMod 2) :=
    (specialLinearNatural (k := ZMod 2) 3).comp q
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let f : I →* A := ((actionMk U).subgroupMap K).comp
    (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm.toMonoidHom
  let φ := E.groupEquiv.toMonoidHom.comp f
  let σ := (linearNatural BinaryField.two d).comp φ
  let τ := (repeated (linearNatural BinaryField.two d) n).comp φ
  let j : R ≃* U := (subgroupOfEquivOfLe hRH).symm
  let s : BinaryConjugationSection I R ⊥ τ := {
    section_le := hRI
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
  have hscalar (b : ρ.IntertwiningMap ρ) : ∃ a : ZMod 2, ∀ w, b w = a • w := by
    let b' : BinaryLinearThree.W.IntertwiningMap BinaryLinearThree.W := {
      toLinearMap := b.toLinearMap
      isIntertwining' := by intro g; obtain ⟨l,rfl⟩ := hq g; exact b.isIntertwining' l }
    exact BinaryLinearThree.NaturalDual.natural_scalar b'
  let : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  have hdim : Module.finrank (ZMod 2) (Fin d → BinaryField.two.Carrier) <
      2 * Module.finrank (ZMod 2) (Fin 3 → ZMod 2) := by
    change Module.finrank (ZMod 2) (Fin d → ZMod 2) <
      2 * Module.finrank (ZMod 2) (Fin 3 → ZMod 2)
    rw [Module.finrank_fin_fun,Module.finrank_fin_fun]
    omega
  exact r.copies_eq_one_of_generates σ τ (fun _ _ _ => rfl) s
    c.escaping.strict.le hspan
    (c.local_orbit_eq_seed_orbit_of_local_natural hf hu hne).ge hscalar hdim hn


/-- The literal B.5.1 moved section on the local seed orbit has only one
natural copy in either binary containing degree. -/
theorem Context.repeated_section_multiplicity_one_of_local_seed_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) {d n : ℕ} (hd : d = 4 ∨ d = 5) (hn : 0 < n) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    ∀ (N : Subgroup (ActionQuotient U)) (_hAN : A ≤ N)
      (s : MovedSection ((action U).comp N.subtype) (A.subgroupOf N))
      (_E : ActionEquiv (s.space.toRepresentation.comp (A.subgroupOf N).subtype)
        (repeated (linearNatural BinaryField.two d) n)), n = 1 := by
  let H := pointJoin T v I
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let A := (I.subgroupOf H).map (actionMk U)
  dsimp only
  intro N hAN s E
  have hs : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.local_seed_orbit_fully_moved_of_local_natural h hu hne
  let j : Additive U ≃ₗ[ZMod 2] s.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict s.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ he => congrArg Subtype.val he,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  exact c.repeated_multiplicity_one_of_local_seed_of_local_natural h hu hne hd hn {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
    linearEquiv := j.trans E.linearEquiv
    intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }


/-- The orbit of the actual local fixed involution cannot be a small natural--dual sum. -/
theorem Context.no_natural_dual_action_of_local_seed_of_local_natural
    (c : Context D t v I)
    (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1)
    {d : ℕ} (hd : d = 4 ∨ d = 5) :
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I))))
    ∀ (_E : ActionEquiv ((action (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)))).comp A.subtype)
      (naturalPlusDual d)), False := by
  obtain ⟨e,⟨r⟩⟩ := h
  have hf : LocalNaturalCover D := ⟨e,⟨r⟩⟩
  let H := pointJoin T v I
  let U := ((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I))
  let R := conjugateSpanBy (zpowers u) I
  let K := I.subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let W := ⁅D.moduleSubgroup,L⁆
  let : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le
    (show W ≤ ⁅D.fullModule,L⁆ from commutator_mono (le_componentOrbit _ _) le_rfl)
  let A := K.map (actionMk U)
  dsimp only
  intro E
  have hWI : W ≤ I := (commutator_mono (le_componentOrbit _ _) le_rfl).trans
    ((source_full_moved_le_component D).trans c.escaping.strict.le)
  have hRI : R ≤ I := conjugateSpanBy_le_self (zpowers_le.mpr (hWI hu.1))
  have hRH : R ≤ H := hRI.trans le_sup_left
  have hspan : W ≤ R := by
    change ⁅D.moduleSubgroup,L⁆ ≤ conjugateSpanBy (zpowers u) I
    rw [←c.local_orbit_eq_seed_orbit_of_local_natural hf hu hne]
    exact le_conjugateSpanBy _ _
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ρ : Representation (ZMod 2) L (Fin 3 → ZMod 2) :=
    (specialLinearNatural (k := ZMod 2) 3).comp q
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff q hq _).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let f : I →* A := ((actionMk U).subgroupMap K).comp
    (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm.toMonoidHom
  let φ := E.groupEquiv.toMonoidHom.comp f
  let σ : Representation (ZMod 2) I (Fin d → ZMod 2) :=
    (linearNatural BinaryField.two d).comp φ
  let τ := σ.prod σ.dual
  let j : R ≃* U := (subgroupOfEquivOfLe hRH).symm
  let s : BinaryConjugationSection I R ⊥ τ := {
    section_le := hRI
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
  have hzero (b : ρ.IntertwiningMap ρ.dual) : b = 0 := by
    let b' : BinaryLinearThree.W.IntertwiningMap BinaryLinearThree.W.dual := {
      toLinearMap := b.toLinearMap
      isIntertwining' := by
        intro g
        obtain ⟨l,rfl⟩ := hq g
        apply LinearMap.ext
        intro w
        apply LinearMap.ext
        intro x
        have he := congrArg (fun z => z x) (LinearMap.congr_fun (b.isIntertwining' l) w)
        change b (ρ l w) x = b w (specialLinearNatural 3 (q l⁻¹) x) at he
        change b (ρ l w) x = b w (specialLinearNatural 3 ((q l)⁻¹) x)
        simpa only [map_inv q] using he }
    have he := BinaryLinearThree.NaturalDual.natural_dual_zero b'
    apply Representation.IntertwiningMap.ext
    exact congrArg (fun z : BinaryLinearThree.W.IntertwiningMap BinaryLinearThree.W.dual => z.toLinearMap) he
  let : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  have hdim : Module.finrank (ZMod 2) (Fin d → BinaryField.two.Carrier) <
      2 * Module.finrank (ZMod 2) (Fin 3 → ZMod 2) := by
    change Module.finrank (ZMod 2) (Fin d → ZMod 2) <
      2 * Module.finrank (ZMod 2) (Fin 3 → ZMod 2)
    rw [Module.finrank_fin_fun,Module.finrank_fin_fun]
    omega
  exact r.no_dual_sum_of_generates σ s
    c.escaping.strict.le hspan
    (c.local_orbit_eq_seed_orbit_of_local_natural hf hu hne).ge hzero hdim

/-- Exclude the literal B.5.1 natural--dual row on the smaller seed orbit. -/
theorem Context.no_natural_dual_section_of_local_seed_of_local_natural
    (c : Context D t v I)
    (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1)
    {d : ℕ} (hd : d = 4 ∨ d = 5) :
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I))))
    ∀ (N : Subgroup (ActionQuotient (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I))))) (_hAN : A ≤ N)
      (s : MovedSection ((action (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)))).comp N.subtype) (A.subgroupOf N))
      (_E : ActionEquiv (s.space.toRepresentation.comp (A.subgroupOf N).subtype)
        (naturalPlusDual d)), False := by
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let U := ((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I))
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk U)
  dsimp only
  intro N hAN s E
  have hs : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.local_seed_orbit_fully_moved_of_local_natural h hu hne
  let j : Additive U ≃ₗ[ZMod 2] s.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict s.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ h => congrArg Subtype.val h,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  let f : ActionEquiv ((action U).comp A.subtype)
      (naturalPlusDual d) := {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
    linearEquiv := j.trans E.linearEquiv
    intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }
  exact c.no_natural_dual_action_of_local_seed_of_local_natural h hu hne hd f


/-- The smaller orbit's literal component is contained in its own offender group. -/
theorem Context.local_seed_actor_le_offender_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    (I.subgroupOf H).map (actionMk R) ≤ offenderSubgroup (action R) := by
  let H := pointJoin T v I
  let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
  have hr := c.local_seed_orbit_reduced hu
  let := hr.normal
  let := hr.elementary
  have hc := c.local_seed_centralizer_eq_of_local_natural h hu hne
  have p := c.prepared_of_three h.three_dvd
  obtain ⟨P,hP⟩ := c.join_sylow
  have hP' : (P : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hjmap : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      Stellmacher.elementaryAbelianMaxJ (pointSylow T v) := by
    rw [←Stellmacher.elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
  have hm : ¬ Stellmacher.elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (R : Set H) := by
    intro hz
    apply p.thompson_moves
    rw [←hjmap]
    rintro _ ⟨j,hj,rfl⟩ z hz'
    have hh : j ∈ centralizer (internalModule D v I : Set H) := hc ▸ hz hj
    exact congrArg H.subtype (hh ⟨z,c.orbit_le_join hz'⟩ hz')
  let : (I.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  have hK : (I.subgroupOf H).IsCComponent := c.escaping.component.subgroupOf_of_le
    le_sup_left (sup_le c.escaping.le_centralizer inf_le_right)
  have hKP : I.subgroupOf H ⊔ (P : Subgroup H) = ⊤ := by
    rw [hP',←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  let := quasisimple_of_thompson_movement
    ChapterB.SourceInduction.adequateClassification_knownSimple c.join_sqtk
    P (I.subgroupOf H) R hK hKP hr.quotient_pCore_eq_bot hm
  exact component_le_offenderSubgroup P (I.subgroupOf H) R hKP hr.quotient_pCore_eq_bot hm


/-- The local fixed involution's orbit has only the single natural,
orthogonal-cover, or ten-dimensional irreducible containing action.
The natural--dual and higher repeated rows are discharged on this actual orbit. -/
theorem Context.local_seed_single_action_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    BinarySingleOrbitAction (action U) A := by
  let H := pointJoin T v I
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let A := (I.subgroupOf H).map (actionMk U)
  let N := offenderSubgroup (action U)
  let : (I.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  let : A.Normal := Normal.map inferInstance (actionMk U) (QuotientGroup.mk'_surjective _)
  have hAN : A ≤ N := c.local_seed_actor_le_offender_of_local_natural h hu hne
  obtain ⟨d,hd,⟨eb⟩⟩ := c.local_seed_binary_actor_of_local_natural h hu hne
  obtain ⟨_,⟨r⟩⟩ := c.local_seed_ff_of_local_natural h hu hne
  have hm := ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor.movedCase hd
    (ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor.actionCase _ hd
      ((subgroupOfEquivOfLe hAN).trans eb) r.clause_one)
  have hs : r.sectionData.space.toSubmodule = ⊤ := by
    rw [r.sectionData.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.local_seed_orbit_fully_moved_of_local_natural h hu hne
  let j : Additive U ≃ₗ[ZMod 2] r.sectionData.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict r.sectionData.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ he => congrArg Subtype.val he,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  cases hm with
  | natural E =>
    let f : ActionEquiv ((action U).comp A.subtype) (linearNatural BinaryField.two d) := {
      groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
      linearEquiv := j.trans E.linearEquiv
      intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }
    exact .natural d hd (BinaryLinearNormalActors.normal_natural_eq_top
      (action U) (action_faithful U) A d f.groupEquiv f.linearEquiv f.intertwines) f
  | orthogonal hd4 _ model dim =>
    subst d
    refine .orthogonal eb ?_ (dim.imp (j.finrank_eq.trans) (j.finrank_eq.trans))
    rcases model with E | E
    · obtain ⟨E⟩ := E
      exact Or.inl ⟨{
        groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
        linearEquiv := j.trans E.linearEquiv
        intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }⟩
    · obtain ⟨E⟩ := E
      exact Or.inr ⟨{
        groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
        linearEquiv := j.trans E.linearEquiv
        intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }⟩
  | exterior _ E hi dim =>
    let e : ActionEquiv ((action U).comp A.subtype)
        (r.sectionData.space.toRepresentation.comp (A.subgroupOf N).subtype) := {
      groupEquiv := (subgroupOfEquivOfLe hAN).symm
      linearEquiv := j
      intertwines := fun _ _ => rfl }
    have hi' := ExtensionConsequences.irreducible_of_equiv e hi
    let := hi'
    have hdim := j.finrank_eq.trans dim
    let eb5 := (subgroupOfEquivOfLe hAN).symm.trans E
    exact .exterior eb5 (BinaryLinearNormalActors.normal_ten_dimensional_eq_top
      (action U) (action_faithful U) A eb5 hdim) hi' hdim
  | naturalDual E =>
    exact (c.no_natural_dual_section_of_local_seed_of_local_natural h hu hne hd N hAN r.sectionData E.some).elim
  | repeatedNatural n hn _ E =>
    obtain ⟨E⟩ := E
    have hn1 := c.repeated_section_multiplicity_one_of_local_seed_of_local_natural h hu hne hd hn N hAN r.sectionData E
    subst n
    let one : (Fin 1 → Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) := {
      toFun w := w 0
      invFun w _ := w
      left_inv w := funext fun i => congrArg w (Subsingleton.elim _ _)
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    let f : ActionEquiv ((action U).comp A.subtype) (linearNatural BinaryField.two d) := {
      groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
      linearEquiv := (j.trans E.linearEquiv).trans one
      intertwines := fun a w => congrFun (E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w)) 0 }

    exact .natural d hd (BinaryLinearNormalActors.normal_natural_eq_top
      (action U) (action_faithful U) A d f.groupEquiv f.linearEquiv f.intertwines) f


/-- In the binary-five case the entire smaller orbit is irreducible. -/
theorem Context.local_seed_irreducible_of_binary_five_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    ∀ (_E : A ≃* SL(5,ZMod 2)),
      A = ⊤ ∧ IsIrreducible ((action U).comp A.subtype) ∧
        (Module.finrank (ZMod 2) (Additive U) = 5 ∨
          Module.finrank (ZMod 2) (Additive U) = 10) := by
  let H := pointJoin T v I
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let A := (I.subgroupOf H).map (actionMk U)
  dsimp only
  intro E
  have ha := c.local_seed_single_action_of_local_natural h hu hne
  cases ha with
  | natural d hd ht f =>
    have hd5 := ChapterB.QuasisimpleSource.SourceCompletion.binary_degree_eq hd (Or.inr rfl)
      (f.groupEquiv.symm.trans E)
    subst d
    exact ⟨ht,ExtensionConsequences.irreducible_of_equiv f
      (ExtensionConsequences.linearNatural_irreducible BinaryField.two (by decide)),
      Or.inl (f.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2)))⟩
  | orthogonal eb _ _ =>
    have he := ChapterB.QuasisimpleSource.SourceCompletion.binary_degree_eq
      (Or.inl rfl : 4 = 4 ∨ 4 = 5) (Or.inr rfl : 5 = 4 ∨ 5 = 5) (eb.symm.trans E)
    omega
  | exterior _ ht hi hd => exact ⟨ht,hi,Or.inr hd⟩


/-- After excluding the augmentation cover, the whole smaller orbit has
only dimensions four, five, six or ten. -/
theorem Context.local_seed_dimension_without_seven_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
    letI := (c.local_seed_orbit_reduced hu).elementary
    Module.finrank (ZMod 2) (Additive U) = 4 ∨
      Module.finrank (ZMod 2) (Additive U) = 5 ∨
      Module.finrank (ZMod 2) (Additive U) = 6 ∨
      Module.finrank (ZMod 2) (Additive U) = 10 := by
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  cases c.local_seed_single_action_of_local_natural h hu hne with
  | natural d hd _ E =>
    have he := E.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
    rcases hd with rfl | rfl
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  | orthogonal _ model _ =>
    rcases model with h6 | h7
    · obtain ⟨E⟩ := h6
      exact Or.inr (Or.inr (Or.inl (E.linearEquiv.finrank_eq.trans
        (BinaryPermutation.finrank_natural_even (Fin 8) (by decide)))))
    · exact (c.no_augmentation_cover_of_local_seed hu hne h7.some).elim
  | exterior _ _ _ dim => exact Or.inr (Or.inr (Or.inr dim))



end CFSG.Quasithin.Chapter10.PointControl.Constrained
