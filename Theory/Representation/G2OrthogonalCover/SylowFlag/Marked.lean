module

public import Theory.Representation.G2OrthogonalCover.RootGeometry
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates

/-!
# The marked derived Sylow and its fixed flag in the G₂′ cover

The full positive-root Sylow intersects the actual commutator subgroup in a
Sylow. Its highest-root group is central in this intersection. Three elements
A(1), E(1), and [r,D(1)] = F(1)D(1) determine the natural fixed line and the
fixed plane modulo that line, uniformly in characteristic two. In particular,
we never require the individual short-root elements to be derived at F₂.

The six-coordinate calculation identifies the pre-existing naturalPlane.
Upstairs its first-line preimage is the span of the first octonion vector plus
the scalar radical. The norm there is the square of the scalar coordinate,
which proves uniqueness of the singular point.

Source: Aschbacher–Smith, I.2.3(1)(a),(c), printed p.413 / PDF p.424.
The root-coordinate conventions are from the attributed ATLAS ports; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. No new ATLAS source is copied.
-/

@[expose] public section
noncomputable section

open Atlas.SplitOctonion Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover.SylowFlag
open Explicit
open scoped commutatorElement
variable (F : Type*) [Field F] [CharP F 2]

abbrev D := commutator (Model F)
def U : Subgroup (D F) := unipotent.subgroupOf (D F)

theorem exists_sylow [Finite F] : ∃ Q : Sylow 2 (D F), (Q : Subgroup (D F)) = U F := by
  simpa only [LieParabolicSetup.sylow_coe, U] using
    (LieParabolicSetup.sylow (F := F)).exists_subgroupOf_eq_of_normal (D F)

def sylow [Finite F] : Sylow 2 (D F) := (exists_sylow F).choose
@[simp] theorem sylow_coe [Finite F] : (sylow F : Subgroup (D F)) = U F :=
  (exists_sylow F).choose_spec

omit [CharP F 2] in
theorem longRoot_le : longRoot F ≤ U F := by
  rintro g ⟨a, rfl⟩
  change rootA a.toAdd ∈ unipotent
  simpa [unipotentProduct] using unipotentProduct_mem (![a.toAdd,0,0,0,0,0] : Fin 6 → F)

omit [CharP F 2] in
theorem longRoot_central : longRoot F ≤ (Subgroup.center (U F)).map (U F).subtype := by
  intro g hg
  refine ⟨⟨g, longRoot_le F hg⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨a, rfl⟩ := hg
  have hh : h.val.val ∈ unipotent := h.property
  rw [unipotent_eq_range] at hh
  obtain ⟨t, ht⟩ := hh
  change h.val.val * rootA a.toAdd = rootA a.toAdd * h.val.val
  rw [← ht]
  exact (LieParabolicSetup.unipotentProduct_commute_rootA t a.toAdd).eq

omit [CharP F 2] in
theorem rootE_mem_derived (a : F) : rootE a ∈ D F := by
  rw [← weylS_rootB, ← weylR_rootA]
  exact (inferInstance : (D F).Normal).conj_mem _
    ((inferInstance : (D F).Normal).conj_mem _ (rootA_mem_derived F a) _) _

def actorA : U F := ⟨longRootElement F 1, longRoot_le F ⟨Multiplicative.ofAdd 1, rfl⟩⟩
def actorE : U F := ⟨⟨rootE 1, rootE_mem_derived F 1⟩, by
  change rootE (1 : F) ∈ unipotent
  simpa [unipotentProduct] using unipotentProduct_mem (![0,0,0,0,1,0] : Fin 6 → F)⟩

theorem commutator_word : ⁅(weylR : Model F), rootD (1 : F)⁆ = rootF (1 : F) * rootD 1 := by
  rw [commutatorElement_def, weylR_rootD]
  congr 1
  apply inv_eq_of_mul_eq_one_left
  rw [rootD_add, CharTwo.add_self_eq_zero, rootD_zero]

def actorH : U F := ⟨⟨⁅(weylR : Model F), rootD (1 : F)⁆,
  Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩, by
  change ⁅(weylR : Model F), rootD (1 : F)⁆ ∈ unipotent
  rw [commutator_word]
  apply (unipotent (K := F)).mul_mem
  · simpa [unipotentProduct] using unipotentProduct_mem (![0,0,0,0,0,1] : Fin 6 → F)
  · simpa [unipotentProduct] using unipotentProduct_mem (![0,0,0,1,0,0] : Fin 6 → F)⟩

abbrev coord := Restricted.NaturalCoordinates.equiv F

theorem coordinates_action (g : D F) (x : Space F) :
    coord F (derivedAction F g x) =
      Restricted.NaturalCoordinates.action F g.val (coord F x) :=
  LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' g.val) x

/-- The marked first octonion vector. -/
def pointVector : TraceZero F := planeLift F ![1,0]
/-- The marked singular projective point upstairs. -/
def P : Submodule F (TraceZero F) := F ∙ pointVector F
/-- Its literal image in the natural module. -/
def N1 : Submodule F (Space F) := (P F).map (mk F)

omit [CharP F 2] in
theorem P_le_plane : P F ≤ singularPlane F := by
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact ⟨![1,0], rfl⟩

theorem P_disjoint_scalar : Disjoint (P F) (scalarLine F) :=
  (singularPlane_disjoint_scalar F).mono_left (P_le_plane F)

omit [CharP F 2] in
theorem pointVector_ne_zero : pointVector F ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : TraceZero F => x.val 0) h
  simp [pointVector, planeLift] at h0

omit [CharP F 2] in
theorem P_finrank : Module.finrank F (P F) = 1 :=
  finrank_span_singleton (pointVector_ne_zero F)

theorem N1_eq_span : N1 F = F ∙ mk F (pointVector F) := by
  rw [N1, P, Submodule.map_span, Set.image_singleton]

theorem point_class_ne_zero : mk F (pointVector F) ≠ 0 := by
  intro h
  have hc := congrArg (fun x : Space F => coord F x 0) h
  simp [coord, Restricted.NaturalCoordinates.coordinates_mk,
    Restricted.NaturalCoordinates.projection, pointVector, planeLift] at hc

theorem N1_finrank : Module.finrank F (N1 F) = 1 := by
  rw [N1_eq_span]
  exact finrank_span_singleton (point_class_ne_zero F)

theorem mem_N1 (x : Space F) : x ∈ N1 F ↔ ∃ a : F, coord F x = ![a,0,0,0,0,0] := by
  rw [N1_eq_span, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    ext i
    fin_cases i <;> simp [coord, Restricted.NaturalCoordinates.projection, pointVector, planeLift]
  · rintro ⟨a, ha⟩
    refine ⟨a, (coord F).injective ?_⟩
    rw [ha]
    ext i
    fin_cases i <;> simp [coord, Restricted.NaturalCoordinates.projection, pointVector, planeLift]

theorem mem_naturalPlane (x : Space F) :
    x ∈ naturalPlane F ↔ ∃ a b : F, coord F x = ![a,b,0,0,0,0] := by
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v 0, v 1, rfl⟩
  · rintro ⟨a, b, h⟩
    refine ⟨planeLift F ![a,b], ⟨![a,b], rfl⟩, (coord F).injective ?_⟩
    exact h.symm

theorem naturalPlane_finrank : Module.finrank F (naturalPlane F) = 2 := by
  have hinj : Function.Injective ((mk F).comp (planeLift F)) := by
    intro v w h
    have hc := congrArg (coord F) h
    ext i
    fin_cases i
    · exact congrFun hc 0
    · exact congrFun hc 1
  have hr : naturalPlane F = ((mk F).comp (planeLift F)).range := by
    rw [naturalPlane, singularPlane, LinearMap.range_comp]
  rw [hr, LinearMap.finrank_range_of_inj hinj]
  simp

theorem N1_le_naturalPlane : N1 F ≤ naturalPlane F :=
  Submodule.map_mono (P_le_plane F)

theorem unipotent_plane (t : Fin 6 → F) (v : Fin 2 → F) :
    traceZeroAction F (unipotentProduct t) (planeLift F v) =
      planeLift F ![v 0 + t 5 * v 1, v 1] := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [traceZeroAction_val, unipotentProduct, planeLift,
      rootA, rootAEquiv, rootALinear, rootAApply,
      rootB, rootBEquiv, rootBLinear, rootBApply,
      rootC, rootCEquiv, rootCLinear, rootCApply,
      rootD, rootDEquiv, rootDLinear, rootDApply,
      rootE, rootEEquiv, rootELinear, rootEApply,
      rootF, rootFEquiv, rootFLinear, rootFApply, CharTwo.sub_eq_add]

theorem fixes_point (g : U F) : OrthogonalCover.action F g.val (pointVector F) = pointVector F := by
  have hg : g.val.val ∈ unipotent := g.property
  rw [unipotent_eq_range] at hg
  obtain ⟨t, ht⟩ := hg
  change traceZeroAction F g.val.val (planeLift F ![1,0]) = _
  rw [← ht, unipotent_plane]
  simp [pointVector]

theorem P_le_fixed : P F ≤ fixed ((OrthogonalCover.action F).comp (U F).subtype) := by
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact fixes_point F

theorem N1_le_fixed : N1 F ≤ fixed ((derivedAction F).comp (U F).subtype) := by
  rintro x ⟨y, hy, rfl⟩ g
  exact congrArg (mk F) (P_le_fixed F hy g)

theorem displacementA (x : Space F) :
    coord F (derivedAction F (actorA F).val x - x) =
      ![coord F x 4, coord F x 5,0,0,0,0] := by
  rw [map_sub, coordinates_action]
  change Restricted.NaturalCoordinates.action F (rootA 1) (coord F x) - coord F x = _
  rw [Restricted.NaturalCoordinates.action_rootA]
  ext i
  fin_cases i <;> simp

theorem displacementE (x : Space F) :
    coord F (derivedAction F (actorE F).val x - x) =
      ![0,coord F x 2,0,coord F x 4,0,0] := by
  rw [map_sub, coordinates_action]
  change Restricted.NaturalCoordinates.action F (rootE 1) (coord F x) - coord F x = _
  rw [Restricted.NaturalCoordinates.action_rootE]
  ext i
  fin_cases i <;> simp

theorem displacementH (x : Space F) :
    coord F (derivedAction F (actorH F).val x - x) =
      ![coord F x 1 + coord F x 2 + coord F x 4,coord F x 4,
        coord F x 3 + coord F x 5,coord F x 5,coord F x 5,0] := by
  rw [map_sub, coordinates_action]
  change Restricted.NaturalCoordinates.action F ⁅(weylR : Model F), rootD 1⁆ (coord F x) - coord F x = _
  rw [commutator_word, map_mul, Module.End.mul_apply,
    Restricted.NaturalCoordinates.action_rootD, Restricted.NaturalCoordinates.action_rootF]
  ext i
  fin_cases i <;> simp
  ring

theorem natural_fixed : fixed ((derivedAction F).comp (U F).subtype) = N1 F := by
  apply le_antisymm _ (N1_le_fixed F)
  intro x hx
  change ∀ g : U F, derivedAction F g.val x = x at hx
  have ha : ![coord F x 4,coord F x 5,0,0,0,0] = (0 : Fin 6 → F) := by
    rw [← displacementA, hx (actorA F), sub_self, map_zero]
  have he : ![0,coord F x 2,0,coord F x 4,0,0] = (0 : Fin 6 → F) := by
    rw [← displacementE, hx (actorE F), sub_self, map_zero]
  have hh := displacementH F x
  rw [hx (actorH F), sub_self, map_zero] at hh
  have h4 : coord F x 4 = 0 := congrFun ha 0
  have h5 : coord F x 5 = 0 := congrFun ha 1
  have h2 : coord F x 2 = 0 := congrFun he 1
  have h1 : coord F x 1 = 0 := by simpa [h2,h4] using (congrFun hh 0).symm
  have h3 : coord F x 3 = 0 := by simpa [h5] using (congrFun hh 2).symm
  apply (mem_N1 F x).mpr
  refine ⟨coord F x 0, ?_⟩
  ext i
  fin_cases i <;> simp [h1,h2,h3,h4,h5]

theorem displacement_mem_N1_iff (x : Space F) :
    (∀ g : U F, derivedAction F g.val x - x ∈ N1 F) ↔ x ∈ naturalPlane F := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (mem_N1 F _).mp (h (actorA F))
    obtain ⟨e, he⟩ := (mem_N1 F _).mp (h (actorE F))
    obtain ⟨b, hh⟩ := (mem_N1 F _).mp (h (actorH F))
    rw [displacementA] at ha
    rw [displacementE] at he
    rw [displacementH] at hh
    have h5 : coord F x 5 = 0 := congrFun ha 1
    have h2 : coord F x 2 = 0 := congrFun he 1
    have h4 : coord F x 4 = 0 := congrFun he 3
    have h3 : coord F x 3 = 0 := by simpa [h5] using congrFun hh 2
    apply (mem_naturalPlane F x).mpr
    refine ⟨coord F x 0, coord F x 1, ?_⟩
    ext i
    fin_cases i <;> simp [h2,h3,h4,h5]
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩ g
    have hg : g.val.val ∈ unipotent := g.property
    rw [unipotent_eq_range] at hg
    obtain ⟨t, ht⟩ := hg
    apply (mem_N1 F _).mpr
    refine ⟨t 5 * v 1, ?_⟩
    rw [derivedAction_mk]
    rw [← ht, unipotent_plane]
    ext i
    fin_cases i <;> simp [coord, Restricted.NaturalCoordinates.projection, planeLift]

/-- The first preimage is the marked point plus the literal scalar kernel. -/
theorem N1_preimage : (N1 F).comap (mk F) = P F ⊔ scalarLine F := by
  rw [N1, Submodule.comap_map_eq]
  simp only [mk, Submodule.ker_mkQ]

/-- The derived Sylow fixes the whole first preimage upstairs. -/
theorem cover_fixed : fixed ((OrthogonalCover.action F).comp (U F).subtype) =
    (N1 F).comap (mk F) := by
  apply le_antisymm
  · intro x hx
    change mk F x ∈ N1 F
    rw [← natural_fixed]
    intro g
    exact congrArg (mk F) (hx g)
  · rw [N1_preimage]
    apply sup_le (P_le_fixed F)
    intro x hx g
    exact (show x ∈ fixed (OrthogonalCover.action F) from (fixed_eq_scalarLine F).symm ▸ hx) g

/-- The restricted norm on the fixed two-space is precisely the square of the scalar coordinate. -/
theorem form_point_scalar (a b : F) :
    form F (a • pointVector F + b • identity F) = b ^ 2 := by
  simp [form, SplitOctonion.norm, pointVector, planeLift, identity, unit, pow_two]

/-- Singular vectors in the fixed two-space form exactly its marked point. -/
theorem singular_fixed_iff (x : TraceZero F)
    (hx : x ∈ fixed ((OrthogonalCover.action F).comp (U F).subtype)) :
    form F x = 0 ↔ x ∈ P F := by
  constructor
  · intro hz
    rw [cover_fixed, N1_preimage] at hx
    obtain ⟨y, hy, z, hzmem, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hzmem
    rw [form_point_scalar, sq_eq_zero_iff] at hz
    rw [hz, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact fun h => singularPlane_singular F x (P_le_plane F h)

/-- Genuine uniqueness among the singular projective points of the fixed space. -/
theorem unique_singular_point (R : Submodule F (TraceZero F))
    (hR : R ≤ fixed ((OrthogonalCover.action F).comp (U F).subtype))
    (hdim : Module.finrank F R = 1) (hq : ∀ x ∈ R, form F x = 0) : R = P F := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    exact (singular_fixed_iff F x (hR hx)).mp (hq x hx)
  · rw [hdim, P_finrank]

/-- The invariant first natural line, with the actual restricted action. -/
theorem N1_invariant (g : U F) : N1 F ≤ (N1 F).comap (derivedAction F g.val) := by
  intro x hx
  change derivedAction F g.val x ∈ N1 F
  rw [show derivedAction F g.val x = x from N1_le_fixed F hx g]
  exact hx

/-- The invariant second natural space is the pre-existing long-root plane image. -/
theorem naturalPlane_invariant (g : U F) :
    naturalPlane F ≤ (naturalPlane F).comap (derivedAction F g.val) := by
  intro x hx
  change derivedAction F g.val x ∈ naturalPlane F
  have hd := N1_le_naturalPlane F ((displacement_mem_N1_iff F x).mpr hx g)
  simpa only [sub_add_cancel] using (naturalPlane F).add_mem hd hx

/-- The literal quotient action by the marked fixed line. -/
def quotientAction : Representation F (U F) (Space F ⧸ N1 F) :=
  Representation.quotient ((derivedAction F).comp (U F).subtype) (N1 F) (N1_invariant F)

/-- The second space is exactly the inverse image of the quotient fixed space. -/
theorem quotient_fixed_preimage :
    (fixed (quotientAction F)).comap (N1 F).mkQ = naturalPlane F := by
  ext x
  change (∀ g : U F, (N1 F).mkQ (derivedAction F g.val x) = (N1 F).mkQ x) ↔ _
  rw [← displacement_mem_N1_iff]
  apply forall_congr'
  intro g
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]


end Atlas.G2.Natural.OrthogonalCover.SylowFlag
