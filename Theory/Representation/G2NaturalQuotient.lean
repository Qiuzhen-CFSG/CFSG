module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The trace-zero quotient for the natural G2 module

In characteristic two, the identity of the split octonions has trace zero.
The natural six-dimensional module is the trace-zero hyperplane modulo the
line spanned by this identity. This file isolates the linear-algebra and
representation construction; the split-octonion model supplies its concrete
trace, identity, and automorphism action.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5) and Appendix B.4.6.
-/

@[expose] public section

namespace Representation.G2Natural

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The trace-zero hyperplane of an eight-dimensional algebra. -/
def traceZero (trace : V →ₗ[K] K) : Submodule K V := trace.ker

/-- The scalar identity line inside the trace-zero hyperplane. -/
def scalarLine (trace : V →ₗ[K] K) (unit : V) (hu : trace unit = 0) :
    Submodule K (traceZero trace) := K ∙ (⟨unit, hu⟩ : traceZero trace)

/-- The six-dimensional quotient underlying the natural module. -/
abbrev Space (trace : V →ₗ[K] K) (unit : V) (hu : trace unit = 0) :=
  traceZero trace ⧸ scalarLine trace unit hu

/-- The quotient class of a trace-zero element. -/
def quotientClass (trace : V →ₗ[K] K) (unit : V) (hu : trace unit = 0)
    (x : traceZero trace) : Space trace unit hu :=
  (scalarLine trace unit hu).mkQ x

@[simp] theorem quotientClass_add (trace : V →ₗ[K] K) (unit : V) (hu : trace unit = 0)
    (x y : traceZero trace) :
    quotientClass trace unit hu (x + y) =
      quotientClass trace unit hu x + quotientClass trace unit hu y := by
  exact map_add _ _ _

@[simp] theorem quotientClass_smul (trace : V →ₗ[K] K) (unit : V) (hu : trace unit = 0)
    (r : K) (x : traceZero trace) :
    quotientClass trace unit hu (r • x) = r • quotientClass trace unit hu x := by
  exact map_smul _ _ _

theorem finrank_space (trace : V →ₗ[K] K) (unit : V) (hu : trace unit = 0)
    [FiniteDimensional K V] (htrace : Function.Surjective trace)
    (hunit : unit ≠ 0) (hdim : Module.finrank K V = 8) :
    Module.finrank K (Space trace unit hu) = 6 := by
  have hrange : trace.range = ⊤ := LinearMap.range_eq_top.mpr htrace
  have hrank : Module.finrank K trace.range = 1 := by
    rw [hrange]
    simp
  have hker : Module.finrank K (traceZero trace) = 7 := by
    have h := trace.finrank_range_add_finrank_ker
    rw [hrank, hdim] at h
    dsimp [traceZero]
    exact Nat.add_left_cancel (show 1 + Module.finrank K (LinearMap.ker trace) =
      1 + 7 by simpa using h)
  have hline : Module.finrank K (scalarLine trace unit hu) = 1 := by
    apply finrank_span_singleton
    intro h
    apply hunit
    exact congrArg Subtype.val h
  have h := (scalarLine trace unit hu).finrank_quotient_add_finrank
  change Module.finrank K (Space trace unit hu) +
    Module.finrank K (scalarLine trace unit hu) =
      Module.finrank K (traceZero trace) at h
  omega

variable {G : Type*} [Group G]

/-- An action on the ambient algebra preserving trace and identity induces
the action on trace-zero elements. -/
def traceZeroAction (ρ : Representation K G V) (trace : V →ₗ[K] K)
    (htrace : ∀ g x, trace (ρ g x) = trace x) :
    Representation K G (traceZero trace) :=
  ρ.subrepresentation (traceZero trace) (by
    intro g x hx
    change trace (ρ g x) = 0
    rw [htrace]
    exact hx)

/-- The action induced on the quotient by the fixed identity line. -/
def action (ρ : Representation K G V) (trace : V →ₗ[K] K) (unit : V)
    (hu : trace unit = 0) (htrace : ∀ g x, trace (ρ g x) = trace x)
    (hunit : ∀ g, ρ g unit = unit) :
    Representation K G (Space trace unit hu) :=
  let σ := traceZeroAction ρ trace htrace
  σ.quotient (scalarLine trace unit hu) (by
    intro g x hx
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    rw [← hr]
    ext
    simp [σ, traceZeroAction, hunit])

@[simp] theorem action_class (ρ : Representation K G V) (trace : V →ₗ[K] K)
    (unit : V) (hu : trace unit = 0)
    (htrace : ∀ g x, trace (ρ g x) = trace x)
    (hunit : ∀ g, ρ g unit = unit)
    (g : G) (x : traceZero trace) :
    action ρ trace unit hu htrace hunit g (quotientClass trace unit hu x) =
      quotientClass trace unit hu ((traceZeroAction ρ trace htrace g) x) := by
  rfl

/-- Restriction to the actual commutator subgroup, including the small-field
case where it can differ from the full automorphism group. -/
def derivedAction (ρ : Representation K G V) (trace : V →ₗ[K] K) (unit : V)
    (hu : trace unit = 0) (htrace : ∀ g x, trace (ρ g x) = trace x)
    (hunit : ∀ g, ρ g unit = unit) :
    Representation K (commutator G) (Space trace unit hu) :=
  (action ρ trace unit hu htrace hunit).comp (commutator G).subtype

@[simp] theorem derivedAction_class (ρ : Representation K G V) (trace : V →ₗ[K] K)
    (unit : V) (hu : trace unit = 0)
    (htrace : ∀ g x, trace (ρ g x) = trace x)
    (hunit : ∀ g, ρ g unit = unit)
    (g : commutator G) (x : traceZero trace) :
    derivedAction ρ trace unit hu htrace hunit g (quotientClass trace unit hu x) =
      quotientClass trace unit hu ((traceZeroAction ρ trace htrace g) x) := by
  exact action_class ρ trace unit hu htrace hunit g x

end Representation.G2Natural
