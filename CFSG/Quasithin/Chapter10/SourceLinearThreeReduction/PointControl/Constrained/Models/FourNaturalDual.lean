module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalRepeated
public import Theory.Representation.BinaryConjugationSection.DualGeneration
public import Theory.Representation.PSL3Two.NaturalDualCentralizer



/-!
# Natural--dual exclusion on the local seed orbit

The natural local three-space generates its own I-orbit. It has no nonzero
map to its dual, so it cannot generate both summands of a natural--dual
module of degree four or five. The proof uses the actual smaller orbit and
its original action kernel; it never places the full four-copy subgroup there.
Source: Aschbacher--Smith 10.2.9, printed p.752, the irreducible-orbit step.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The orbit of the actual local fixed involution cannot be a small natural--dual sum. -/
theorem Context.no_natural_dual_action_of_local_seed
    (c : Context D t v I)
    (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1)
    {d : ℕ} (hd : d = 4 ∨ d = 5) :
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I))))
    ∀ (_E : ActionEquiv ((action (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)))).comp A.subtype)
      (naturalPlusDual d)), False := by
  obtain ⟨e,⟨s₀⟩⟩ := h
  obtain ⟨r⟩ := c.local_natural_of_four_natural_cover e s₀
  have hf : FourNaturalCover D := ⟨e,⟨s₀⟩⟩
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
    rw [←c.local_orbit_eq_seed_orbit_of_four_natural_cover hf hu hne]
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
    (c.local_orbit_eq_seed_orbit_of_four_natural_cover hf hu hne).ge hzero hdim

/-- Exclude the literal B.5.1 natural--dual row on the smaller seed orbit. -/
theorem Context.no_natural_dual_section_of_local_seed
    (c : Context D t v I)
    (h : FourNaturalCover D) {u : G}
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
    exact c.local_seed_orbit_fully_moved_of_four_natural_cover h hu hne
  let j : Additive U ≃ₗ[ZMod 2] s.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict s.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ h => congrArg Subtype.val h,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  let f : ActionEquiv ((action U).comp A.subtype)
      (naturalPlusDual d) := {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
    linearEquiv := j.trans E.linearEquiv
    intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }
  exact c.no_natural_dual_action_of_local_seed h hu hne hd f

end CFSG.Quasithin.Chapter10.PointControl.Constrained
