module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.SubspaceQuotient
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The binary SL₄ adjoint quotient

The natural four-space gives a conjugation action on its endomorphisms. The
trace kernel has dimension fifteen and contains the invariant scalar line.
Its literal quotient therefore has dimension fourteen. This module exposes
the quotient map, its kernel and the induced action for the endpoint-pair
recognition and actor calculations.

The model definitions are exposed deliberately: both consumers need the actual
endomorphism and quotient carriers. No irreducibility, recognition or actor
bound is asserted here. The representation alias `traceAction` keeps the
canonical trace-kernel instances at the quotient boundary.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A; Aschbacher–Smith, K.3.2,
printed pp.454–455.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Representation
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint

abbrev Group := Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)
abbrev Natural := Fin 4 → ZMod 2
abbrev natural : Representation (ZMod 2) Group Natural := specialLinearNatural 4

/-- Conjugation preserves the kernel of the ordinary endomorphism trace. -/
noncomputable def traceZero : Subrepresentation (natural.linHom natural) where
  toSubmodule := LinearMap.ker (LinearMap.trace (ZMod 2) Natural)
  apply_mem_toSubmodule g f hf := by
    change LinearMap.trace (ZMod 2) Natural
      (natural g ∘ₗ f ∘ₗ natural g⁻¹) = 0
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    have hh : natural g⁻¹ ∘ₗ natural g = LinearMap.id := by
      rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hh, LinearMap.comp_id]
    exact hf

abbrev TraceZero : Type := (LinearMap.trace (ZMod 2) Natural).ker

/-- The trace-kernel action, on the canonical submodule carrier. -/
abbrev traceAction : Representation (ZMod 2) Group TraceZero := traceZero.toRepresentation

/-- The identity endomorphism lies in the trace kernel in characteristic two. -/
def scalarVector : TraceZero := ⟨LinearMap.id, by
  change LinearMap.trace (ZMod 2) Natural LinearMap.id = 0
  rw [LinearMap.trace_id]
  have hd : Module.finrank (ZMod 2) Natural = 4 := by simp [Natural]
  rw [hd]
  decide⟩

/-- Evaluation of the restricted action on its literal endomorphism. -/
@[simp] theorem traceAction_apply (g : Group) (f : TraceZero) :
    (traceAction g f).val = natural g ∘ₗ f.val ∘ₗ natural g⁻¹ := rfl

theorem scalarVector_ne_zero : scalarVector ≠ 0 := by
  intro h
  have he := congrArg (fun f : TraceZero => f.val (Pi.single 0 1) 0) h
  norm_num [scalarVector] at he

@[simp] theorem traceAction_scalarVector (g : Group) :
    traceAction g scalarVector = scalarVector := by
  apply Subtype.ext
  change natural g ∘ₗ LinearMap.id ∘ₗ natural g⁻¹ = LinearMap.id
  rw [LinearMap.id_comp, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The invariant one-dimensional space of scalar endomorphisms. -/
noncomputable def scalarLine : Subrepresentation traceAction where
  toSubmodule := Submodule.span (ZMod 2) {scalarVector}
  apply_mem_toSubmodule g f hf := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    exact Submodule.mem_span_singleton.mpr ⟨c, by
      rw [map_smul, traceAction_scalarVector]⟩

/-- The actual adjoint quotient sl₄(F₂) / ⟨Id⟩. -/
abbrev Adjoint : Type := TraceZero ⧸ scalarLine.toSubmodule
/-- Conjugation on the trace-zero quotient by scalars. -/
noncomputable def adjoint : Representation (ZMod 2) Group Adjoint :=
  scalarLine.quotientRepresentation

/-- The literal quotient map from trace-zero endomorphisms. -/
noncomputable def mkAdjoint : TraceZero →ₗ[ZMod 2] Adjoint := scalarLine.toSubmodule.mkQ

@[simp] theorem adjoint_mk (g : Group) (f : TraceZero) :
    adjoint g (mkAdjoint f) = mkAdjoint (traceAction g f) := rfl

theorem mkAdjoint_surjective : Function.Surjective mkAdjoint :=
  Submodule.mkQ_surjective _

theorem mkAdjoint_eq_zero_iff (f : TraceZero) :
    mkAdjoint f = 0 ↔ ∃ c : ZMod 2, c • scalarVector = f := by
  change Submodule.Quotient.mk f = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_span_singleton

theorem finrank_traceZero : Module.finrank (ZMod 2) TraceZero = 15 := by
  have hsurj : Function.Surjective (LinearMap.trace (ZMod 2) Natural) := by
    intro c
    refine ⟨(LinearMap.proj (0 : Fin 4)).smulRight (Pi.single 0 c), ?_⟩
    simp [LinearMap.trace_smulRight]
  have h := (LinearMap.trace (ZMod 2) Natural).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_self, Module.finrank_linearMap] at h
  have hv : Module.finrank (ZMod 2) Natural = 4 := by simp [Natural]
  rw [hv] at h
  change 1 + Module.finrank (ZMod 2) TraceZero = 4 * 4 at h
  omega


theorem finrank_scalarLine : Module.finrank (ZMod 2) scalarLine.toSubmodule = 1 := by
  change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {scalarVector}) = 1
  exact finrank_span_singleton scalarVector_ne_zero

/-- The source adjoint quotient has binary dimension fourteen. -/
theorem finrank_adjoint : Module.finrank (ZMod 2) Adjoint = 14 := by
  have h := scalarLine.toSubmodule.finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) Adjoint + Module.finrank (ZMod 2) scalarLine.toSubmodule =
    Module.finrank (ZMod 2) TraceZero at h
  rw [finrank_scalarLine, finrank_traceZero] at h
  omega

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint
