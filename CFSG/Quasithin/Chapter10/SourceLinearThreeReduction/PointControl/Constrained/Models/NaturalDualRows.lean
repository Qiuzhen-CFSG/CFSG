module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.QuietDimension
public import Theory.Representation.BinaryConjugationSection.SmallRepeated
public import Theory.Representation.PSL3Two.NaturalDualCentralizer

/-!
# Containing-action reductions for the original natural--dual row

The natural and dual three-dimensional constituents are inequivalent. An
embedding in repeated four- or five-dimensional natural modules would force
both constituents into one coordinate module, contradicting its dimension.
For the orthogonal and deleted-eight actions, the original six-space fills
the faithful containing central section. Original Thompson fixedness then
contradicts movement on VI, with the central kernel retained throughout.

The final consumer keeps the complete B.5.1 conclusion and leaves precisely
the ten-dimensional irreducible and the natural--dual containing families.
Those two families, positive original covers, general quiet preparation and
the retained four-natural original row remain with
qt-d-10-nona5-point-constrained. This is a reduction for the displayed original
zero-kernel natural--dual marking, not a universal recognition theorem.
Source: Aschbacher--Smith 10.2.9, printed pp.751--752.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Repeated natural containing actions exclude the original natural--dual pair. -/
theorem Context.no_repeated_natural_action_of_naturalDual
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
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
  let W := ⁅D.fullModule,L⁆
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  let A := K.map (actionMk U)
  dsimp only
  intro E
  have hspan := c.moved_le_of_naturalDual e r
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

/-- The complete repeated-natural containing row is excluded, on the
original orbit and with its source action marking retained. -/
theorem Context.no_repeated_natural_section_of_naturalDual
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
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
    exact c.fully_moved_of_moved_le (c.moved_le_of_naturalDual e r)
  let j : Additive U ≃ₗ[ZMod 2] s.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict s.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ h => congrArg Subtype.val h,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  let f : ActionEquiv ((action U).comp A.subtype)
      (repeated (linearNatural BinaryField.two d) n) := {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
    linearEquiv := j.trans E.linearEquiv
    intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }
  exact c.no_repeated_natural_action_of_naturalDual e r hd hn f

end CFSG.Quasithin.Chapter10.PointControl.Constrained

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Original Thompson fixedness excludes every faithful containing central
section of dimension at most six in the natural--dual row. -/
theorem Context.no_small_faithful_section_of_naturalDual
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∀ (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N)),
      Function.Injective s.action →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≤ 6 → False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let W := ⁅D.fullModule,L⁆
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  dsimp only
  intro s hf hd
  have hinj : Function.Injective r.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [r.kernel_eq,bot_subgroupOf])
  let f : Additive W ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space :=
    LinearEquiv.ofBijective (r.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hinj,r.onto⟩
  have hdim : Module.finrank (ZMod 2) (Additive W) = 6 := by
    rw [f.finrank_eq]
    change Module.finrank (ZMod 2)
      ((Fin 3 → ZMod 2) × Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 6
    rw [Module.finrank_prod,Subspace.dual_finrank_eq,Module.finrank_fin_fun]
  exact c.no_small_faithful_section_of_fullModule_centralized
    (c.actionFacts_of_naturalDual e r) (c.moved_le_of_naturalDual e r)
    (c.thompson_centralizes_fullModule_of_naturalDual e r) s hf (hd.trans_eq hdim.symm)

/-- The remaining marked containing actions for the original natural--dual
row: the ten-dimensional irreducible and natural--dual sums. -/
inductive NaturalDualRemainingAction
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A : Subgroup Q} (s : MovedSection ρ A) : Prop
  | exteriorFive (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp A.subtype))
      (actor : A ≃* SL(5,ZMod 2))
      (dimension : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10)
  | naturalDual (d : ℕ) (degree : d = 4 ∨ d = 5)
      (action : IsNaturalPlusDual (s.space.toRepresentation.comp A.subtype) d)

/-- The literal B.5.1 consumer discards repeated naturals and both
six-dimensional containing actions without any extra preparation or
fixed-kernel premise. The remaining two containing families stay with
qt-d-10-nona5-point-constrained for final source assembly. -/
theorem Context.remaining_source_action_of_naturalDual
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
      NaturalDualRemainingAction h.sectionData ∧
        ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* SL(d,ZMod 2)) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk U)
  let N := offenderSubgroup (action U)
  have a := c.actionFacts_of_naturalDual e r
  have hAN : A ≤ N := a.classification.2.1
  obtain ⟨h,hs,ha⟩ := c.binary_source_action_of_naturalDual e r
  refine ⟨h,?_,ha⟩
  cases hs with
  | sevenFour hf hi E hd =>
    exact (c.no_small_faithful_section_of_naturalDual e r h.sectionData hf (by omega)).elim
  | sevenDeleted hf hi E =>
    exact (c.no_deletedSeven_source_section a h.sectionData ⟨E⟩).elim
  | linear d hd hf hi E =>
    exact (c.no_binary_natural_section_of_naturalDual e r hd N hAN h.sectionData E).elim
  | orthogonalSix hf hi E =>
    apply (c.no_small_faithful_section_of_naturalDual e r h.sectionData hf ?_).elim
    rw [E.linearEquiv.finrank_eq,BinaryPermutation.finrank_natural_even]
    · decide
    · decide
  | symmetricEight hf hi E =>
    apply (c.no_small_faithful_section_of_naturalDual e r h.sectionData hf ?_).elim
    rw [E.action.linearEquiv.finrank_eq,BinaryPermutation.finrank_natural_even]
    · decide
    · decide
  | exteriorFive hf hi E hd => exact .exteriorFive hf hi E hd
  | naturalDual d hd E => exact .naturalDual d hd E
  | repeatedNatural d n hd hn hb E =>
    exact (c.no_repeated_natural_section_of_naturalDual e r hd hn N hAN h.sectionData E.some).elim

end CFSG.Quasithin.Chapter10.PointControl.Constrained
