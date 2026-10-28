module

public import Theory.Representation.FirstCohomologyG2Natural.OctonionCocycle
public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# The trace-zero orthogonal cover for the derived split G₂ group

The split-octonion norm restricts to a nondegenerate quadratic form on the
seven-dimensional trace-zero space. Its polar radical is the scalar identity
line, which is also the fixed space of the actual commutator subgroup,
including G₂(2)′. The literal projection to the natural six-space is a cover.

For commutator generation, extend a fixed functional to the ambient octonions
using their nondegenerate polar pairing. Invariance says every displacement
of its representing vector is scalar. The explicit octonion cocycle kernel
calculation forces that vector itself to be scalar, so the functional is zero.
This proves the covering property without assuming indecomposability.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma
I.2.3(1), printed p.413 / PDF p.424, combined manuscript of 1 March 2004.
Coordinates and norm identities use the attributed ATLAS octonion ports;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. This module establishes
the concrete orthogonal cover; universality and local root geometry require
additional arguments.
-/

@[expose] public section

open Atlas.SplitOctonion Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover
variable (K : Type*) [Field K] [CharP K 2]

/-- The octonion norm on the trace-zero seven-space. -/
def form : QuadraticForm K (TraceZero K) where
  toFun x := norm x.val
  toFun_smul a x := by simpa [pow_two] using norm_smul a x.val
  exists_companion' := ⟨normPolar.compl₁₂ (TraceZero K).subtype (TraceZero K).subtype,
    fun x y => norm_add x.val y.val⟩

omit [CharP K 2] in
@[simp] theorem form_apply (x : TraceZero K) : form K x = norm x.val := rfl

omit [CharP K 2] in
@[simp] theorem polar_apply (x y : TraceZero K) :
    (form K).polarBilin x y = normPolar x.val y.val := by
  rw [QuadraticMap.polarBilin_apply_apply]
  exact (normPolar_eq x.val y.val).symm

omit [CharP K 2] in
@[simp] theorem polar_unit (x : Carrier K) : normPolar unit x = trace x := by
  simp [normPolar, unit, trace, add_comm]

private def offDiagonal (i : Fin 8) (hi : i ≠ 3 ∧ i ≠ 4) : TraceZero K :=
  ⟨basisVector i, by simp [trace, basisVector, Ne.symm hi.1, Ne.symm hi.2]⟩

/-- The orthogonal complement of the trace-zero hyperplane in the ambient eight-space is the scalar line. -/
theorem orthogonal_traceZero_iff (x : Carrier K) :
    (∀ y : TraceZero K, normPolar x y.val = 0) ↔ ∃ a : K, a • unit = x := by
  constructor
  · intro h
    have h0 := h (offDiagonal K 7 (by decide))
    have h1 := h (offDiagonal K 6 (by decide))
    have h2 := h (offDiagonal K 5 (by decide))
    have h5 := h (offDiagonal K 2 (by decide))
    have h6 := h (offDiagonal K 1 (by decide))
    have h7 := h (offDiagonal K 0 (by decide))
    have ht := h (identity K)
    simp [offDiagonal, normPolar, basisVector] at h0 h1 h2 h5 h6 h7
    have ht' : x 4 = x 3 := by
      have ht'' : x 3 + x 4 = 0 := by simpa [identity, normPolar, unit] using ht
      exact eq_of_sub_eq_zero (by simpa [CharTwo.sub_eq_add, add_comm] using ht'')
    refine ⟨x 3, ?_⟩
    ext i
    fin_cases i <;> simp [unit, h0, h1, h2, h5, h6, h7, ht']
  · rintro ⟨a, rfl⟩ y
    rw [map_smul, LinearMap.smul_apply, polar_unit]
    rw [show trace y.val = 0 from y.property, smul_zero]

/-- The polar radical is precisely the scalar identity line. -/
theorem polar_ker : (form K).polarBilin.ker = scalarLine K := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [polar_apply, LinearMap.zero_apply]
  rw [orthogonal_traceZero_iff]
  change _ ↔ x ∈ K ∙ identity K
  rw [Submodule.mem_span_singleton]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩,
    fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩⟩

/-- The polar radical has field dimension one. -/
theorem finrank_scalarLine : Module.finrank K (scalarLine K) = 1 := by
  apply finrank_span_singleton
  exact fun h => unit_ne_zero (congrArg Subtype.val h)

/-- The orthogonal space has field dimension seven. -/
theorem finrank_traceZero : Module.finrank K (TraceZero K) = 7 := by
  have h := (scalarLine K).finrank_quotient_add_finrank
  rw [finrank_scalarLine] at h
  change Module.finrank K (Space K) + 1 = Module.finrank K (TraceZero K) at h
  rw [finrank_space] at h
  exact h.symm

@[simp] theorem form_identity : form K (identity K) = 1 := by
  simp [form, identity, SplitOctonion.norm, unit]

/-- Quadratic nondegeneracy: the polar radical has dimension one and contains no nonzero singular vector. -/
theorem form_nondegenerate : (form K).Nondegenerate := by
  constructor
  · apply le_antisymm _ bot_le
    intro x hx
    have hx' : x ∈ scalarLine K := polar_ker K ▸ (form K).radical_le_ker_polarBilin hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx'
    have hq : form K (a • identity K) = 0 := hx.1
    rw [QuadraticMap.map_smul, form_identity, smul_eq_mul, mul_one] at hq
    have ha : a = 0 := (mul_self_eq_zero.mp hq)
    simp [ha]
  · rw [polar_ker, ← Module.finrank_eq_rank, finrank_scalarLine]
    simp

/-- The seven-dimensional action of the actual commutator subgroup. -/
def action : Representation K (commutator (Model K)) (TraceZero K) :=
  (traceZeroAction K).comp (commutator (Model K)).subtype

omit [CharP K 2] in
@[simp] theorem action_val (g : commutator (Model K)) (x : TraceZero K) :
    (action K g x).val = g.val.val x.val := rfl

omit [CharP K 2] in
@[simp] theorem form_invariant (g : commutator (Model K)) (x : TraceZero K) :
    form K (action K g x) = form K x := automorphism_norm g.val x.val

/-- The literal natural quotient projection as an equivariant map. -/
def projection : (action K).IntertwiningMap (derivedAction K) :=
  (mk K).intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)

@[simp] theorem projection_apply (x : TraceZero K) : projection K x = mk K x := rfl

@[simp] theorem projection_ker : (projection K).toLinearMap.ker = scalarLine K :=
  Submodule.ker_mkQ _

/-- The derived group fixes precisely the scalar identity line, also over the two-element field. -/
theorem fixed_eq_scalarLine : fixed (action K) = scalarLine K := by
  ext x
  constructor
  · intro hx
    have h : ambientCocycle K x.val = 0 := by
      rw [ambientCocycle_traceZero]
      apply Subtype.ext
      funext g
      change derivedAction K g (mk K x) - mk K x = 0
      rw [derivedAction_mk]
      exact sub_eq_zero.mpr (congrArg (mk K) (hx g))
    obtain ⟨a, ha⟩ := (ambientCocycle_eq_zero_iff K x.val).mp h
    exact Submodule.mem_span_singleton.mpr ⟨a, Subtype.ext ha⟩
  · rintro hx g
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change traceZeroAction K g.val (a • identity K) = a • identity K
    rw [map_smul, traceZeroAction_identity]

omit [CharP K 2] in
private theorem ambientPairing_surjective :
    Function.Surjective (normPolar (F := K)) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := K) (V := Carrier K)).symm).mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  exact normPolar_nondegenerate (fun y => LinearMap.congr_fun hx y)

omit [CharP K 2] in
private theorem pairing_covariant (g : Model K) (x : Carrier K) (y : TraceZero K) :
    normPolar (g.val x) y.val = normPolar x (traceZeroAction K g⁻¹ y).val := by
  have h := automorphism_normPolar g x ((g⁻¹).val y.val)
  simpa using h

/-- The seven-space is generated by its derived-group commutators. -/
theorem commutator_eq_top : Coinvariants.ker (action K) = ⊤ := by
  apply (fixed_dual_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨l, hl⟩ := LinearMap.dualMap_surjective_of_injective
    (TraceZero K).injective_subtype f
  obtain ⟨x, rfl⟩ := ambientPairing_surjective K l
  have he (y : TraceZero K) : normPolar x y.val = f y := LinearMap.congr_fun hl y
  have hc : ambientCocycle K x = 0 := by
    apply Subtype.ext
    funext g
    change mk K (displacement K g.val x) = 0
    apply (mk_eq_zero_iff K _).mpr
    apply (orthogonal_traceZero_iff K _).mp
    intro y
    change normPolar (g.val.val x - x) y.val = 0
    rw [map_sub, LinearMap.sub_apply, pairing_covariant, he, he]
    have h := LinearMap.congr_fun (hf g) y
    exact sub_eq_zero.mpr h
  obtain ⟨a, rfl⟩ := (ambientCocycle_eq_zero_iff K x).mp hc
  change f = 0
  ext y
  rw [← he, map_smul, LinearMap.smul_apply, polar_unit]
  simp only [show trace y.val = 0 from y.property, smul_zero, LinearMap.zero_apply]

/-- The trace-zero quotient is a genuine perfect central module cover. -/
theorem projection_isCover : IsCover (projection K) := by
  refine ⟨mk_surjective K, ?_, commutator_eq_top K⟩
  rw [projection_ker, fixed_eq_scalarLine]


end Atlas.G2.Natural.OrthogonalCover
