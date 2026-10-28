module

public import Theory.Representation.G2OrthogonalCover

/-!
# The long-root commutator plane in the G₂′ orthogonal cover

The literal Wilson root A belongs to the derived group over every field:
A(a) is the commutator of B(a) and E(1). On the trace-zero space its
image of displacement is the plane on the first two octonion coordinates.
That plane is totally singular, has dimension two, and is disjoint from the
scalar radical. It complements the radical in the literal inverse image of
its image in the natural six-space.

These computations include the binary field without identifying G₂(2) and
G₂(2)′. Identifying the chosen root group inside the center of a derived Sylow
and proving the Sylow invariance of the selected flag remain separate steps.
Source: Aschbacher–Smith, I.2.3(1)(c), printed p.413 / PDF p.424.
Coordinates use the attributed ATLAS root maps; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No additional ATLAS source is copied here.
-/

@[expose] public section

open Atlas.SplitOctonion Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover
open Explicit
open scoped commutatorElement
variable (K : Type*) [Field K] [CharP K 2]

/-- The first two octonion coordinates, as vectors in the trace-zero space. -/
def planeLift : (Fin 2 → K) →ₗ[K] TraceZero K where
  toFun v := ⟨![v 0, v 1, 0, 0, 0, 0, 0, 0], by simp [trace]⟩
  map_add' v w := by apply Subtype.ext; ext i; fin_cases i <;> simp
  map_smul' a v := by apply Subtype.ext; ext i; fin_cases i <;> simp

/-- The marked totally singular plane in the orthogonal cover. -/
def singularPlane : Submodule K (TraceZero K) := (planeLift K).range

/-- The literal image of the marked plane in the natural six-space. -/
def naturalPlane : Submodule K (Space K) := (singularPlane K).map (mk K)

omit [CharP K 2] in
theorem planeLift_injective : Function.Injective (planeLift K) := by
  intro v w h
  have he := congrArg Subtype.val h
  funext i
  fin_cases i
  · exact congrFun he 0
  · exact congrFun he 1

omit [CharP K 2] in
/-- The marked orthogonal plane has dimension two. -/
theorem singularPlane_finrank : Module.finrank K (singularPlane K) = 2 := by
  rw [singularPlane, LinearMap.finrank_range_of_inj (planeLift_injective K)]
  simp

omit [CharP K 2] in
/-- The norm vanishes identically on the marked plane. -/
theorem singularPlane_singular (x : TraceZero K) (hx : x ∈ singularPlane K) :
    form K x = 0 := by
  obtain ⟨v, rfl⟩ := hx
  simp [form, planeLift, SplitOctonion.norm]

/-- The marked plane is disjoint from the polar radical. -/
theorem singularPlane_disjoint_scalar : Disjoint (singularPlane K) (scalarLine K) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hl
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hl
  have h := singularPlane_singular K _ hx
  rw [QuadraticMap.map_smul, form_identity, smul_eq_mul, mul_one] at h
  rw [mul_self_eq_zero.mp h, zero_smul]

/-- The marked plane complements the radical in the literal quotient preimage. -/
theorem naturalPlane_preimage :
    (naturalPlane K).comap (mk K) = singularPlane K ⊔ scalarLine K := by
  rw [naturalPlane, Submodule.comap_map_eq]
  simp only [mk, Submodule.ker_mkQ]

omit [CharP K 2] in
/-- The long-root elements are commutators, over every field and in particular over F₂. -/
theorem rootA_mem_derived (a : K) : rootA a ∈ commutator (Model K) := by
  have he : ⁅rootB a, rootE (1 : K)⁆ = rootA a := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext i
    fin_cases i <;>
      simp [commutatorElement_def, rootB, rootBEquiv, rootBLinear, rootBApply,
        rootE, rootEEquiv, rootELinear, rootEApply,
        rootA, rootAEquiv, rootALinear, rootAApply] <;> ring
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- A long-root element in the actual derived group. -/
def longRootElement (a : K) : commutator (Model K) := ⟨rootA a, rootA_mem_derived K a⟩

/-- The additive highest-root group with its actual derived-group embedding. -/
def longRootHom : Multiplicative K →* commutator (Model K) where
  toFun a := longRootElement K a.toAdd
  map_one' := by apply Subtype.ext; exact rootA_zero
  map_mul' a b := by apply Subtype.ext; exact (rootA_add _ _).symm

/-- The marked long-root subgroup of the actual derived group. -/
def longRoot : Subgroup (commutator (Model K)) := (longRootHom K).range

omit [CharP K 2] in
/-- The exact displacement of the long-root element in octonion coordinates. -/
theorem longRoot_displacement (a : K) (x : TraceZero K) :
    action K (longRootElement K a) x - x = planeLift K ![-a * x.val 6, a * x.val 7] := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [action, longRootElement, traceZeroAction_val, rootA, rootAEquiv,
      rootALinear, rootAApply, planeLift]

private def displacementSource (v : Fin 2 → K) : TraceZero K :=
  ⟨![0, 0, 0, 0, 0, 0, -v 0, v 1], by simp [trace]⟩

omit [CharP K 2] in
private theorem longRoot_displacement_one (v : Fin 2 → K) :
    action K (longRootElement K 1) (displacementSource K v) - displacementSource K v =
      planeLift K v := by
  rw [longRoot_displacement]
  congr 1
  ext i
  fin_cases i <;> simp [displacementSource]

omit [CharP K 2] in
/-- The commutator space of the actual long-root group is the marked singular plane. -/
theorem longRoot_commutator :
    Coinvariants.ker ((action K).comp (longRoot K).subtype) = singularPlane K := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, x⟩, rfl⟩
    obtain ⟨a, ha⟩ := g.property
    change action K g.val x - x ∈ singularPlane K
    rw [← ha]
    exact ⟨![-a.toAdd * x.val 6, a.toAdd * x.val 7], (longRoot_displacement K _ x).symm⟩
  · rintro x ⟨v, rfl⟩
    rw [← longRoot_displacement_one]
    let g : longRoot K := ⟨longRootElement K 1, ⟨Multiplicative.ofAdd 1, rfl⟩⟩
    exact Coinvariants.sub_mem_ker (ρ := (action K).comp (longRoot K).subtype)
      g (displacementSource K v)

/-- The long-root plane calculation, with the original quotient and radical. -/
theorem longRoot_geometry :
    Module.finrank K (Coinvariants.ker ((action K).comp (longRoot K).subtype)) = 2 ∧
    (∀ x ∈ Coinvariants.ker ((action K).comp (longRoot K).subtype), form K x = 0) ∧
    Disjoint (Coinvariants.ker ((action K).comp (longRoot K).subtype)) (scalarLine K) ∧
    (naturalPlane K).comap (mk K) =
      Coinvariants.ker ((action K).comp (longRoot K).subtype) ⊔ scalarLine K := by
  rw [longRoot_commutator]
  exact ⟨singularPlane_finrank K, singularPlane_singular K,
    singularPlane_disjoint_scalar K, naturalPlane_preimage K⟩

end Atlas.G2.Natural.OrthogonalCover
