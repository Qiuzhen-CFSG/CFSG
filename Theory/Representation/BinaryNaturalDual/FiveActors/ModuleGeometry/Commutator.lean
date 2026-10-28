module

public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Splitting

/-!
# The actual centralizer commutator summand

Restrict the actual representation to the outer involution fixed space and
take the span of its centralizer displacements. The compatible split
coordinates show this span is precisely the four-dimensional polar summand:
transitivity on nonzero polar vectors expresses every vector as a single
displacement. The remaining line is fixed and nonsingular. Both the internal
direct sum and its exact ambient subspaces are recorded.

Source: Aschbacher–Smith, H.9.2(1), printed p.390 (PDF p.401).
-/

@[expose] public section

open Matrix BinaryLinear BinaryLinear.OuterCyclic
open BinaryNaturalDual.AdaptedPair
open Theory.SpecificGroups.SymmetricSix
namespace BinaryNaturalDual.FiveActors.ModuleGeometry

variable (d : CoordinateAction 5) (t : M)

/-- Restriction of the actual actor to the fixed space. -/
def fixedAction (a : innerCentralizer t) :
    fixedSpace (linearAction d t) →ₗ[ZMod 2] fixedSpace (linearAction d t) :=
  (((linearAction d a.val).toLinearMap).comp (fixedSpace (linearAction d t)).subtype).codRestrict
    (fixedSpace (linearAction d t)) (by
      intro v
      apply (mem_fixedSpace _ _).mpr
      change linearAction d t (linearAction d a.val v) = linearAction d a.val v
      have hc := Subgroup.mem_centralizer_singleton_iff.mp a.property.2
      calc
        linearAction d t (linearAction d a.val v) =
            linearAction d a.val (linearAction d t v) := by
          simp only [← LinearEquiv.mul_apply, ← map_mul, hc]
        _ = _ := congrArg (linearAction d a.val) ((mem_fixedSpace _ _).mp v.property))

@[simp] theorem fixedAction_apply (a : innerCentralizer t)
    (v : fixedSpace (linearAction d t)) :
    (fixedAction d t a v : V) = d.representation a.val v := rfl

/-- The actual commutator submodule [C_V(t),C_L(t)]. -/
def centralizerCommutator : Submodule (ZMod 2) (fixedSpace (linearAction d t)) :=
  Submodule.span (ZMod 2) {z | ∃ (a : innerCentralizer t)
    (v : fixedSpace (linearAction d t)), fixedAction d t a v - v = z}

theorem displacement_mem (a : innerCentralizer t) (v : fixedSpace (linearAction d t)) :
    fixedAction d t a v - v ∈ centralizerCommutator d t :=
  Submodule.subset_span ⟨a, v, rfl⟩

private theorem polar_displacement (w : NaturalModule) :
    ∃ (σ : S6) (v : NaturalModule), polarAction σ v - v = w := by
  have hex : ∃ v : NaturalModule, v ≠ 0 ∧ v + w ≠ 0 := by
    exact (by decide : ∀ w : NaturalModule, ∃ v : NaturalModule, v ≠ 0 ∧ v + w ≠ 0) w
  obtain ⟨v, hv, hvw⟩ := hex
  obtain ⟨σ, hσ⟩ := polarPoint_transitive ⟨v, hv⟩ ⟨v + w, hvw⟩
  have he : polarAction σ v = v + w :=
    (polarAction_point σ ⟨v, hv⟩).trans (congrArg Subtype.val hσ)
  exact ⟨σ, v, by rw [he]; abel⟩

/-- The same commutator viewed as an actual subspace of V. -/
def ambientCommutator : Submodule (ZMod 2) V :=
  (centralizerCommutator d t).map (fixedSpace (linearAction d t)).subtype

theorem ambientCommutator_eq_span :
    ambientCommutator d t = Submodule.span (ZMod 2)
      {z | ∃ (a : innerCentralizer t) (v : V),
        v ∈ fixedSpace (linearAction d t) ∧ d.representation a.val v - v = z} := by
  rw [ambientCommutator, centralizerCommutator, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨a, v, rfl⟩, rfl⟩
    exact ⟨a, v.val, v.property, rfl⟩
  · rintro ⟨a, v, hv, rfl⟩
    exact ⟨fixedAction d t a ⟨v, hv⟩ - ⟨v, hv⟩, ⟨a, ⟨v, hv⟩, rfl⟩, rfl⟩

variable (g : G) (hg : MulAut.conj (MulAut.conj g) t = graphLinear 5)
variable (ht : t ^ 2 = 1) (hout : t ∉ L)

/-- The displayed nonsingular vector in the actual fixed space. -/
noncomputable def fixedVector : fixedSpace (linearAction d t) :=
  splitEquiv t g d ht hout (1, 0)

/-- The geometric alternating summand, before identifying it with commutators. -/
noncomputable def movingMap : NaturalModule →ₗ[ZMod 2] fixedSpace (linearAction d t) :=
  (splitEquiv t g d ht hout).toLinearMap.comp
    (LinearMap.inr (ZMod 2) (ZMod 2) NaturalModule)

@[simp] theorem movingMap_apply (v : NaturalModule) :
    movingMap d t g ht hout v = splitEquiv t g d ht hout (0, v) := rfl

include hg in
theorem fixedAction_split (a : innerCentralizer t) (c : ZMod 2) (v : NaturalModule) :
    fixedAction d t a (splitEquiv t g d ht hout (c, v)) =
      splitEquiv t g d ht hout (c, polarAction (centralizerSixEquiv t g hg a) v) :=
  Subtype.ext (splitEquiv_equivariant t g hg d ht hout a c v).symm

include hg in
theorem commutator_eq_range :
    centralizerCommutator d t = LinearMap.range (movingMap d t g ht hout) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, v, rfl⟩
    obtain ⟨⟨c, w⟩, rfl⟩ := (splitEquiv t g d ht hout).surjective v
    rw [fixedAction_split d t g hg ht hout]
    refine ⟨polarAction (centralizerSixEquiv t g hg a) w - w, ?_⟩
    change splitEquiv t g d ht hout (0, _) = _
    rw [← map_sub (splitEquiv t g d ht hout)]
    congr 1
    simp
  · rintro _ ⟨w, rfl⟩
    obtain ⟨σ, v, hσ⟩ := polar_displacement w
    let a := (centralizerSixEquiv t g hg).symm σ
    have h := displacement_mem d t a (splitEquiv t g d ht hout (0, v))
    rw [fixedAction_split d t g hg ht hout, MulEquiv.apply_symm_apply, ← map_sub (splitEquiv t g d ht hout)] at h
    have he : ((0 : ZMod 2), polarAction σ v) - (0, v) = (0, w) := by
      ext <;> simp [hσ]
    rw [he] at h
    exact h

include hg in
theorem fixedVector_nonsingular : quadratic (fixedVector d t g ht hout : V) = 1 :=
  splitEquiv_quadratic t g hg d ht hout 1 0

include hg in
theorem fixedVector_centralized (a : innerCentralizer t) :
    d.representation a.val (fixedVector d t g ht hout) = fixedVector d t g ht hout := by
  have h := splitEquiv_equivariant t g hg d ht hout a 1 0
  simpa only [fixedVector, polarAction_zero] using h.symm

include hg in
theorem fixed_direct_sum :
    IsCompl (Submodule.span (ZMod 2) {fixedVector d t g ht hout})
      (centralizerCommutator d t) := by
  rw [commutator_eq_range d t g hg ht hout]
  constructor
  · apply Submodule.disjoint_def.mpr
    intro z hz hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    obtain ⟨v, hv⟩ := hw
    have he : splitEquiv t g d ht hout (c, 0) = z := by
      simpa only [fixedVector, ← map_smul, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using hc
    have hp : (0, v) = (c, 0) := (splitEquiv t g d ht hout).injective (hv.trans he.symm)
    have hc0 : c = 0 := (congrArg Prod.fst hp).symm
    rw [hc0] at he
    simpa only [show ((0 : ZMod 2), (0 : NaturalModule)) = 0 from rfl, map_zero] using he.symm
  · apply Submodule.codisjoint_iff_exists_add_eq.mpr
    intro z
    obtain ⟨⟨c, v⟩, rfl⟩ := (splitEquiv t g d ht hout).surjective z
    refine ⟨splitEquiv t g d ht hout (c, 0), splitEquiv t g d ht hout (0, v), ?_, ?_, ?_⟩
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      change c • splitEquiv t g d ht hout (1, 0) = _
      rw [← map_smul]
      congr 1
      simp
    · exact ⟨v, rfl⟩
    · rw [← map_add]
      congr 1
      simp

include hg in
theorem ambient_fixed_sum :
    fixedSpace (linearAction d t) =
      Submodule.span (ZMod 2) {(fixedVector d t g ht hout : V)} ⊔ ambientCommutator d t := by
  have h := congrArg (Submodule.map (fixedSpace (linearAction d t)).subtype)
    (fixed_direct_sum d t g hg ht hout).sup_eq_top
  simpa only [Submodule.map_sup, Submodule.map_span, Set.image_singleton, Submodule.subtype_apply,
    Submodule.map_top, Submodule.range_subtype, ambientCommutator] using h.symm

include hg in
theorem ambient_fixed_disjoint :
    Disjoint (Submodule.span (ZMod 2) {(fixedVector d t g ht hout : V)})
      (ambientCommutator d t) := by
  have h := Submodule.disjoint_map (fixedSpace (linearAction d t)).injective_subtype
    (fixed_direct_sum d t g hg ht hout).disjoint
  simpa only [Submodule.map_span, Set.image_singleton, Submodule.subtype_apply, ambientCommutator] using h

include hg in
theorem fixed_line_finrank :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) {(fixedVector d t g ht hout : V)}) = 1 := by
  apply finrank_span_singleton
  intro h
  have hq := fixedVector_nonsingular d t g hg ht hout
  rw [h, map_zero] at hq
  exact zero_ne_one hq

/-- The natural four-space identified with the actual commutator module. -/
noncomputable def naturalEquiv : NaturalModule ≃ₗ[ZMod 2] centralizerCommutator d t :=
  (LinearEquiv.ofInjective (movingMap d t g ht hout)
    ((splitEquiv t g d ht hout).injective.comp LinearMap.inr_injective)).trans
      (LinearEquiv.ofEq _ _ (commutator_eq_range d t g hg ht hout).symm)

@[simp] theorem naturalEquiv_apply (v : NaturalModule) :
    (naturalEquiv d t g hg ht hout v : fixedSpace (linearAction d t)) =
      splitEquiv t g d ht hout (0, v) := rfl

/-- Compatibility with the designated polar S₆ action, in the original space. -/
theorem naturalEquiv_equivariant (a : innerCentralizer t) (v : NaturalModule) :
    ((naturalEquiv d t g hg ht hout (polarAction (centralizerSixEquiv t g hg a) v) :
      fixedSpace (linearAction d t)) : V) =
      d.representation a.val ((naturalEquiv d t g hg ht hout v :
        fixedSpace (linearAction d t)) : V) :=
  splitEquiv_equivariant t g hg d ht hout a 0 v

include hg ht hout in
theorem commutator_finrank : Module.finrank (ZMod 2) (centralizerCommutator d t) = 4 := by
  rw [← (naturalEquiv d t g hg ht hout).finrank_eq]
  exact naturalModule_finrank

end BinaryNaturalDual.FiveActors.ModuleGeometry
