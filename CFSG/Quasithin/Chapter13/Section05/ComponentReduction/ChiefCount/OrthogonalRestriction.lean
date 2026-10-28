module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.UpperSection
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.Representation.Quotient

/-!
# The orthogonal lower contribution in 13.5.22

The actual normal flag in O²(N_L(V₁)) is
`1 ≤ V₁∩L₁ ≤ V∩L₁ ≤ V_L∩L₁`. Here the G.2 seed V is Chapter 13's V₃,
whereas V_L is Chapter 13's V. Generation puts the whole seed in L₁.
The point interval and the interval above the seed are central.

Relabel the derived singular point simultaneously in the actors and the
five-point augmentation coordinates. The seed becomes the moved three-space,
the point becomes its fixed line, and the literal seed/point quotient becomes
the irreducible binary A₄ plane. Equivariant chief refinement gives one
noncentral two-factor, with constituent coordinates, for every series from
1 to V_L∩L₁. No equality between this last intersection and the seed or V_L
is required.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.22(2), printed p.924 (PDF p.941), using the orthogonal A₅ module
of G.2.4, printed pp.334–335.
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.OrthogonalRestriction
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open BinaryPermutation
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

theorem seed_le_residual (d : Hypothesis D g) (hgen : D.I g = D.L) : D.V ≤ D.L₁ := by
  rw [d.seed_eq]
  exact (commutator_mono ((d.central_first d.L_le_I).trans inf_le_left) le_rfl).trans
    (core_commutator_le_residual d hgen)

def point (_d : Hypothesis D g) : NormalNode D.L₁ :=
  ⟨D.V₁.subgroupOf D.L₁, normal_subgroupOf_of_le_normalizer
    ((map_subtype_le _).trans inf_le_right)⟩

def seed (d : Hypothesis D g) : NormalNode D.L₁ :=
  ⟨D.V.subgroupOf D.L₁, normal_subgroupOf_of_le_normalizer
    (le_sup_left.trans d.setup.local_normalizes_V)⟩

theorem point_le_seed (d : Hypothesis D g) : point d ≤ seed d :=
  comap_mono d.setup.point_le

theorem seed_le_first (d : Hypothesis D g) : seed d ≤ first d :=
  comap_mono (d.VL_inf_U ▸ inf_le_left)

theorem point_central (d : Hypothesis D g) : IsCentral ⊥ (point d) := by
  rw [isCentral_iff_commutator_le, commutator_le]
  intro x _ y hy
  have hC := normalizer_le_centralizer_of_card_two D.V₁ d.point_card
    (((map_subtype_le _).trans inf_le_right : D.L₁ ≤ D.G₁) x.property)
  apply Subtype.ext
  change (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ = 1
  rw [← hC y hy, mul_inv_cancel_right, mul_inv_cancel]

theorem above_seed_central (d : Hypothesis D g) : IsCentral (seed d) (first d) := by
  rw [isCentral_iff_commutator_le, commutator_le]
  intro x _ y hy
  change ⁅(x : G), (y : G)⁆ ∈ D.V
  rw [d.seed_eq, commutator_comm]
  exact commutator_mem_commutator x.property hy

private theorem exists_relabel (i : Fin 5) :
    ∃ a : alternatingGroup (Fin 5), a.val i = 4 := by
  revert i
  decide +kernel

noncomputable def relabel (d : Hypothesis D g) : alternatingGroup (Fin 5) :=
  Classical.choose (show ∃ a : alternatingGroup (Fin 5), a.val d.pointIndex = 4 from by
    exact exists_relabel d.pointIndex)

theorem relabel_point (d : Hypothesis D g) : (relabel d).val d.pointIndex = 4 :=
  Classical.choose_spec (exists_relabel d.pointIndex)

noncomputable def borelEquiv (d : Hypothesis D g) : Borel d ≃* AlternatingFiveBorel.B :=
  MulAction.stabilizerEquivStabilizer (relabel_point d).symm

noncomputable def actor (d : Hypothesis D g) : D.L₁ →* AlternatingFiveBorel.B :=
  (borelEquiv d).toMonoidHom.comp (localProjection d)

theorem actor_surjective (d : Hypothesis D g) : Function.Surjective (actor d) :=
  (borelEquiv d).surjective.comp (localProjection_surjective d)

noncomputable def coordinates (d : Hypothesis D g) :
    D.VL ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
  d.coordinates.trans (FiveMovedHyperplanes.coordinateAut (relabel d))

theorem coordinates_equivariant (d : Hypothesis D g) (k : D.L₁) (v : D.VL) :
    coordinates d ⟨(k : G) * v * (k : G)⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_VL D ((residual_le_L D) k.property)) v).mp v.property⟩ =
    Multiplicative.ofAdd (AlternatingFiveBorel.action (actor d k) (coordinates d v).toAdd) := by
  change FiveMovedHyperplanes.coordinateAut (relabel d) (d.coordinates _) = _
  refine (congrArg (FiveMovedHyperplanes.coordinateAut (relabel d))
    (d.equivariant ⟨k, (residual_le_L D) k.property⟩ v)).trans ?_
  exact FiveMovedHyperplanes.coordinateAut_conj (relabel d) (d.fiveAction (inclusion (residual_le_L D) k))
    (d.coordinates v).toAdd

theorem generator_coordinates (d : Hypothesis D g) :
    coordinates d ⟨d.pointGenerator, (le_conjugateSpanBy D.V₁ D.L) d.pointGenerator.property⟩ =
    Multiplicative.ofAdd AlternatingFiveBorel.fixedVector := by
  change FiveMovedHyperplanes.act (relabel d) d.pointVector = AlternatingFiveBorel.fixedVector
  rw [d.pointVector_eq_pointWord, Starred.pointWord_action, relabel_point]
  apply Subtype.ext
  rw [AlternatingFiveBorel.fixedVector_coordinates]
  funext i
  fin_cases i <;> rfl


noncomputable def inverseMap (d : Hypothesis D g) :
    Multiplicative (BinaryPermutation.core (Fin 5)) →* G :=
  D.VL.subtype.comp (coordinates d).symm.toMonoidHom

theorem inverseMap_injective (d : Hypothesis D g) : Function.Injective (inverseMap d) :=
  Subtype.val_injective.comp (coordinates d).symm.injective

theorem inverseMap_coordinates (d : Hypothesis D g) (v : D.VL) :
    inverseMap d (coordinates d v) = v :=
  congrArg Subtype.val ((coordinates d).symm_apply_apply v)

theorem inverseMap_commutator (d : Hypothesis D g) (k : D.L₁)
    (v : BinaryPermutation.core (Fin 5)) :
    ⁅(k : G), inverseMap d (Multiplicative.ofAdd v)⁆ =
      inverseMap d (Multiplicative.ofAdd (AlternatingFiveBorel.action (actor d k) v - v)) := by
  have he := coordinates_equivariant d k ((coordinates d).symm (Multiplicative.ofAdd v))
  rw [(coordinates d).apply_symm_apply] at he
  have hc := congrArg (fun x => ((coordinates d).symm x : G)) he
  simp only [MulEquiv.symm_apply_apply] at hc
  change (k : G) * inverseMap d (Multiplicative.ofAdd v) * (k : G)⁻¹ =
    inverseMap d (Multiplicative.ofAdd (AlternatingFiveBorel.action (actor d k) v)) at hc
  rw [ofAdd_sub, map_div, div_eq_mul_inv, ← hc]
  rfl

theorem seed_eq_moved_image (d : Hypothesis D g) :
    D.V = FiveMovedHyperplanes.moved.map (inverseMap d) := by
  have hle : D.V ≤ FiveMovedHyperplanes.moved.map (inverseMap d) := by
    rw [d.seed_eq, commutator_comm, commutator_le]
    intro k hk v hv
    let w : D.VL := ⟨v, hv⟩
    have he := inverseMap_commutator d ⟨k, hk⟩ (coordinates d w).toAdd
    simp only [ofAdd_toAdd, inverseMap_coordinates] at he
    rw [he]
    exact mem_map.mpr ⟨_,
      FiveMovedHyperplanes.difference_mem_moved (actor d ⟨k, hk⟩).val
        (actor d ⟨k, hk⟩).property _, rfl⟩
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective (inverseMap_injective d), FiveMovedHyperplanes.card_moved, d.card_V]

theorem coordinates_mem_moved (d : Hypothesis D g) (v : D.VL) :
    (coordinates d v).toAdd ∈ AlternatingFiveBorel.moved ↔ (v : G) ∈ D.V := by
  rw [seed_eq_moved_image]
  constructor
  · intro hv
    exact mem_map.mpr ⟨coordinates d v, hv, inverseMap_coordinates d v⟩
  · rintro ⟨x, hx, he⟩
    have hxe : x = coordinates d v := (inverseMap_injective d) (he.trans
      (inverseMap_coordinates d v).symm)
    exact hxe ▸ hx

noncomputable def seedCoordinates (d : Hypothesis D g) :
    D.V ≃* Multiplicative AlternatingFiveBorel.moved where
  toFun v := Multiplicative.ofAdd ⟨(coordinates d
    ⟨v, (d.VL_inf_U ▸ inf_le_left) v.property⟩).toAdd,
      (coordinates_mem_moved d _).mpr v.property⟩
  invFun v := ⟨inverseMap d (Multiplicative.ofAdd v.toAdd.val), by
    rw [seed_eq_moved_image]
    exact mem_map.mpr ⟨_, v.toAdd.property, rfl⟩⟩
  left_inv v := Subtype.ext (inverseMap_coordinates d _)
  right_inv v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact (coordinates d).apply_symm_apply (Multiplicative.ofAdd v.toAdd.val)
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_mul (coordinates d)
      ⟨v, (d.VL_inf_U ▸ inf_le_left) v.property⟩
      ⟨w, (d.VL_inf_U ▸ inf_le_left) w.property⟩)

theorem seedCoordinates_equivariant (d : Hypothesis D g) (k : D.L₁) (v : D.V) :
    seedCoordinates d ⟨(k : G) * v * (k : G)⁻¹,
      (mem_normalizer_iff.mp ((le_sup_left.trans d.setup.local_normalizes_V) k.property) v).mp
        v.property⟩ =
    Multiplicative.ofAdd (AlternatingFiveBorel.movedRepresentation (actor d k)
      (seedCoordinates d v).toAdd) := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change _ = (AlternatingFiveBorel.movedRepresentation (actor d k)
    (seedCoordinates d v).toAdd).val
  rw [AlternatingFiveBorel.movedRepresentation_apply]
  exact congrArg Multiplicative.toAdd (coordinates_equivariant d k
    ⟨v, (d.VL_inf_U ▸ inf_le_left) v.property⟩)

theorem coordinates_fixed_iff (d : Hypothesis D g) (v : D.VL) :
    (coordinates d v).toAdd ∈ AlternatingFiveBorel.action.invariants ↔ (v : G) ∈ D.V₁ := by
  rw [AlternatingFiveBorel.fixed_eq_line]
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    have hv' : coordinates d v = 1 ∨ coordinates d v = Multiplicative.ofAdd AlternatingFiveBorel.fixedVector := by
      fin_cases c
      · left
        apply Multiplicative.toAdd.injective
        exact hc.symm.trans (zero_smul (ZMod 2) _)
      · right
        apply Multiplicative.toAdd.injective
        exact hc.symm.trans (one_smul (ZMod 2) _)
    rcases hv' with hv' | hv'
    · have h := (coordinates d).injective (hv'.trans (coordinates d).map_one.symm)
      rw [h]; exact D.V₁.one_mem
    · have h := (coordinates d).injective (hv'.trans (generator_coordinates d).symm)
      exact (congrArg Subtype.val h) ▸ d.pointGenerator.property
  · intro hv
    by_cases h1 : (v : G) = 1
    · have he : v = 1 := Subtype.ext h1
      rw [he, map_one]
      exact Submodule.zero_mem _
    · have he := congrArg Subtype.val (d.eq_pointGenerator ⟨v, hv⟩
        (fun h => h1 (congrArg Subtype.val h)))
      have he' : v = ⟨d.pointGenerator, (le_conjugateSpanBy D.V₁ D.L) d.pointGenerator.property⟩ :=
        Subtype.ext he
      rw [he', generator_coordinates]
      exact Submodule.subset_span (Set.mem_singleton _)

noncomputable def fourActor (d : Hypothesis D g) : D.L₁ →* alternatingGroup (Fin 4) :=
  AlternatingFiveBorel.marking.symm.toMonoidHom.comp (actor d)

theorem fourActor_surjective (d : Hypothesis D g) : Function.Surjective (fourActor d) :=
  AlternatingFiveBorel.marking.symm.surjective.comp (actor_surjective d)

noncomputable def constituent (d : Hypothesis D g) :
    Representation (ZMod 2) D.L₁ (natural (Fin 4)) :=
  (alternatingNaturalRepresentation (Fin 4)).comp (fourActor d)

instance constituent_irreducible (d : Hypothesis D g) :
    Representation.IsIrreducible (constituent d) :=
  (Representation.irreducible_comp_surjective_iff _ (fourActor_surjective d) _).mpr
    AlternatingFiveBorel.natural_irreducible

noncomputable def seedProjection (d : Hypothesis D g) :
    D.V →* Multiplicative (natural (Fin 4)) :=
  AlternatingFiveBorel.projection.toAddMonoidHom.toMultiplicative.comp (seedCoordinates d).toMonoidHom

theorem seedProjection_surjective (d : Hypothesis D g) : Function.Surjective (seedProjection d) :=
  AlternatingFiveBorel.projection_surjective.comp (seedCoordinates d).surjective

-- A public-equation bridge: the model keeps the definition of its fixed line private.
private theorem fixedInMoved_eq :
    AlternatingFiveBorel.fixedInMoved =
      AlternatingFiveBorel.action.invariants.comap AlternatingFiveBorel.moved.subtype := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro v hv b
    exact (AlternatingFiveBorel.movedRepresentation_apply b v).symm.trans
      (congrArg Subtype.val (AlternatingFiveBorel.fixedInMoved_fixed b v hv))
  · exact AlternatingFiveBorel.finrank_fixedInMoved.trans
      ((Submodule.comapSubtypeEquivOfLe AlternatingFiveBorel.fixed_le_moved).finrank_eq.trans
        AlternatingFiveBorel.finrank_fixed).symm

theorem seedProjection_kernel (d : Hypothesis D g) (v : D.V) :
    seedProjection d v = 1 ↔ (v : G) ∈ D.V₁ := by
  change AlternatingFiveBorel.projection (seedCoordinates d v).toAdd = 0 ↔ _
  change (seedCoordinates d v).toAdd ∈ AlternatingFiveBorel.projection.ker ↔ _
  rw [AlternatingFiveBorel.projection_ker, fixedInMoved_eq]
  exact coordinates_fixed_iff d _

theorem seedProjection_equivariant (d : Hypothesis D g) (k : D.L₁) (v : D.V) :
    (seedProjection d ⟨(k : G) * v * (k : G)⁻¹,
      (mem_normalizer_iff.mp ((le_sup_left.trans d.setup.local_normalizes_V) k.property) v).mp
        v.property⟩).toAdd = constituent d k (seedProjection d v).toAdd := by
  change AlternatingFiveBorel.projection (seedCoordinates d _).toAdd = _
  rw [seedCoordinates_equivariant]
  have he := AlternatingFiveBorel.projection_equivariant
    (fourActor d k) (seedCoordinates d v).toAdd
  change AlternatingFiveBorel.projection
    (AlternatingFiveBorel.movedRepresentation (actor d k) (seedCoordinates d v).toAdd) =
      alternatingNaturalRepresentation (Fin 4) (fourActor d k)
        (AlternatingFiveBorel.projection (seedCoordinates d v).toAdd)
  simpa only [fourActor, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using he


theorem constituent_moves (d : Hypothesis D g) :
    ∃ k v, constituent d k v ≠ v := by
  by_contra hn
  push Not at hn
  have he : (alternatingNaturalRepresentation (Fin 4)).asGroupHom.ker = ⊤ := by
    apply top_unique
    intro b _
    obtain ⟨k, rfl⟩ := fourActor_surjective d b
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact hn k v
  have hk := AlternatingFiveBorel.natural_kernel.symm.trans he
  have hc := alternatingGroup.kleinFour_card_of_card_eq_four (by simp : Nat.card (Fin 4) = 4)
  rw [hk, card_top, alternatingGroup.card_of_card_eq_four (by simp : Nat.card (Fin 4) = 4)] at hc
  norm_num at hc

noncomputable def sectionProjection (d : Hypothesis D g) :
    (seed d).val →* Multiplicative (natural (Fin 4)) :=
  (seedProjection d).comp
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem sectionProjection_surjective (d : Hypothesis D g) (hgen : D.I g = D.L) :
    Function.Surjective (sectionProjection d) := by
  intro w
  obtain ⟨v, hv⟩ := seedProjection_surjective d w
  exact ⟨⟨⟨v, (seed_le_residual d hgen) v.property⟩, v.property⟩, hv⟩

theorem sectionProjection_kernel (d : Hypothesis D g) :
    (sectionProjection d).ker = (point d).val.subgroupOf (seed d).val := by
  ext x
  exact seedProjection_kernel d ⟨x.val.val, x.property⟩

noncomputable def sectionEquiv (d : Hypothesis D g) (hgen : D.I g = D.L) :
    Section (point d) (seed d) ≃* Multiplicative (natural (Fin 4)) :=
  (QuotientGroup.quotientMulEquivOfEq (sectionProjection_kernel d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (sectionProjection d)
      (sectionProjection_surjective d hgen))

@[simp] theorem sectionEquiv_mk (d : Hypothesis D g) (hgen : D.I g = D.L)
    (x : (seed d).val) :
    sectionEquiv d hgen (QuotientGroup.mk' _ x) = sectionProjection d x := rfl

theorem sectionEquiv_equivariant (d : Hypothesis D g) (hgen : D.I g = D.L)
    (k : D.L₁) (x : Section (point d) (seed d)) :
    (sectionEquiv d hgen (sectionAction (point d) (seed d) k x)).toAdd =
      constituent d k (sectionEquiv d hgen x).toAdd := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [sectionAction_mk, sectionEquiv_mk, sectionEquiv_mk]
  exact seedProjection_equivariant d k ⟨x.val.val, x.property⟩

noncomputable def sectionCoordinates (d : Hypothesis D g) (hgen : D.I g = D.L) :
    SectionCoordinates (point d) (seed d) (constituent d) 1 where
  equiv := (sectionEquiv d hgen).trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) (natural (Fin 4))).symm.toAddEquiv.toMultiplicative
  equivariant k x _i := sectionEquiv_equivariant d hgen k x

/-- The literal point/seed/orthogonal flag, allowing a repeated last term. -/
def filtration (d : Hypothesis D g) : Filtration D.L₁ 3 where
  term := ![⊥, point d, seed d, first d]
  monotone := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i
    · exact bot_le
    · exact point_le_seed d
    · exact seed_le_first d

theorem filtration_strata (d : Hypothesis D g) (hgen : D.I g = D.L) :
    ∀ i : Fin 3, IsModuleStratum (constituent d)
      ((filtration d).term i.castSucc) ((filtration d).term i.succ) (![0, 1, 0] i) := by
  intro i
  fin_cases i
  · exact Or.inl ⟨point_central d, rfl⟩
  · exact Or.inr ⟨sectionCoordinates d hgen⟩
  · exact Or.inl ⟨above_seed_central d, rfl⟩

/-- An actual refinement retains all four original subgroup intersections,
with one noncentral binary A₄ constituent and its literal conjugation action. -/
theorem exists_refinement (d : Hypothesis D g) (hgen : D.I g = D.L) :
    ∃ (s : ChiefSeries D.L₁) (ι : Fin 4 →o Fin (s.length + 1)),
      (∀ i, s (ι i) = (filtration d).term i) ∧
      ι 0 = 0 ∧ ι 3 = Fin.last s.length ∧
      s.head = ⊥ ∧ s.last = first d ∧ s.noncentralTwoCount = 1 ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) (constituent d) 1) := by
  obtain ⟨s, ι, hi, hi0, hil, hs0, hsl, hsc, hsa⟩ :=
    (filtration d).exists_marked_refinement ![0, 1, 0] (filtration_strata d hgen)
      (constituent_moves d)
  refine ⟨s, ι, hi, hi0, hil, hs0, hsl, ?_, hsa⟩
  simpa [Fin.sum_univ_succ] using hsc

/-- Every chief series on V_L∩L₁ has precisely one noncentral two-factor,
and every such factor has the constructed A₄ constituent coordinates. -/
theorem count_and_coordinates (d : Hypothesis D g) (hgen : D.I g = D.L)
    (t : ChiefSeries D.L₁) (ht0 : t.head = ⊥) (htl : t.last = first d) :
    t.noncentralTwoCount = 1 ∧
      ∀ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ) →
        Nonempty (SectionCoordinates (t i.castSucc) (t i.succ) (constituent d) 1) := by
  obtain ⟨s, _, _, _, _, hs0, hsl, hsc, hsa⟩ := exists_refinement d hgen
  obtain ⟨hc, ha⟩ := s.marked_of_same_endpoints t (hs0.trans ht0.symm) (hsl.trans htl.symm) hsa
  exact ⟨hc.trans hsc, ha⟩

theorem count_one (d : Hypothesis D g) (hgen : D.I g = D.L)
    (t : ChiefSeries D.L₁) (ht0 : t.head = ⊥) (htl : t.last = first d) :
    t.noncentralTwoCount = 1 := (count_and_coordinates d hgen t ht0 htl).1

/-- Original Chapter 13 application: its V₃ is the seed, and its V is V_L.
The given L₁ is identified with O²(N_{L⁻}(V₁)), retaining relative normality. -/
theorem source_count_one
    (V₁ V₃ V Lminus T H L₁ : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hgen : (chapter13Setup V₁ V₃ Lminus T H).I g = Lminus)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (t : ChiefSeries L₁) (h0 : t.head.val = ⊥)
    (h1 : t.last.val = V.subgroupOf L₁) : t.noncentralTwoCount = 1 := by
  subst L₁
  apply count_one d hgen t
  · exact Subtype.ext h0
  · apply Subtype.ext
    exact h1.trans (congrArg (fun A : Subgroup G => A.subgroupOf _) hspan.symm)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.OrthogonalRestriction
