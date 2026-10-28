module

public import Theory.AtlasPort.G2
public import Theory.Representation.G2NaturalQuotient

/-!
# The six-dimensional natural G₂ representation in characteristic two

The carrier is the trace-zero subspace of the split octonions, modulo the
scalar identity line. Octonion automorphisms preserve trace and fix the identity,
so their eight-dimensional action descends to this quotient. Rank-nullity gives
its dimension as `(8 - 1) - 1 = 6`.

The group is the actual `Atlas.G2.Model K`. The derived action is its restriction
to `commutator (Atlas.G2.Model K)`; in particular the construction includes the
binary field without identifying G₂(2) with G₂(2)'. The quotient map, its kernel,
and its action formula are exposed for cocycle calculations.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(5), PDF p.419, and B.4.6, printed pp.88–90. The split-octonion model is
provided by the attributed ATLAS ports imported above; no additional ATLAS
source is copied here.
-/

@[expose] public section

namespace Atlas.G2.Natural

open Atlas.SplitOctonion

variable (K : Type*) [Field K]

/-- The eight-dimensional octonion action, as a `Representation`. -/
def ambient : Representation K (Model K) (Carrier K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (representation K)

@[simp] theorem ambient_apply (g : Model K) (x : Carrier K) :
    ambient K g x = g.val x := rfl

/-- The invariant trace-zero hyperplane. -/
abbrev TraceZero := Representation.G2Natural.traceZero (traceLinearMap K)

@[simp] theorem mem_traceZero (x : Carrier K) :
    x ∈ TraceZero K ↔ trace x = 0 := Iff.rfl

/-- Restriction of the automorphism action to the trace-zero hyperplane. -/
def traceZeroAction : Representation K (Model K) (TraceZero K) :=
  Representation.G2Natural.traceZeroAction (ambient K) (traceLinearMap K)
    (fun g x => automorphism_trace g x)

@[simp] theorem traceZeroAction_val (g : Model K) (x : TraceZero K) :
    (traceZeroAction K g x).val = g.val x.val := rfl

variable [CharP K 2]

/-- The scalar identity, regarded as a trace-zero element in characteristic two. -/
def identity : TraceZero K := ⟨unit, trace_unit_charTwo K⟩

/-- The fixed scalar line in the trace-zero hyperplane. -/
def scalarLine : Submodule K (TraceZero K) := K ∙ identity K

/-- The natural module of G₂ in characteristic two. -/
abbrev Space := TraceZero K ⧸ scalarLine K

/-- The canonical linear quotient map. -/
def mk : TraceZero K →ₗ[K] Space K := (scalarLine K).mkQ

theorem mk_surjective : Function.Surjective (mk K) :=
  (scalarLine K).mkQ_surjective

@[simp] theorem mk_identity : mk K (identity K) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero (scalarLine K)).mpr (Submodule.mem_span_singleton_self _)

/-- Precisely scalar identities represent zero in the natural module. -/
theorem mk_eq_zero_iff (x : TraceZero K) :
    mk K x = 0 ↔ ∃ r : K, r • unit = x.val := by
  change Submodule.Quotient.mk x = (0 : Space K) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change x ∈ K ∙ identity K ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, congrArg Subtype.val hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr⟩

/-- Two trace-zero representatives give the same class exactly when their
 difference is a scalar identity. -/
theorem mk_eq_mk_iff (x y : TraceZero K) :
    mk K x = mk K y ↔ ∃ r : K, r • unit = x.val - y.val := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  rfl

/-- Automorphisms fix the scalar identity pointwise. -/
@[simp] theorem traceZeroAction_identity (g : Model K) :
    traceZeroAction K g (identity K) = identity K := by
  apply Subtype.ext
  exact automorphism_unit g

/-- The induced full G₂ action on the six-dimensional quotient. -/
def action : Representation K (Model K) (Space K) :=
  Representation.G2Natural.action (ambient K) (traceLinearMap K) unit
    (trace_unit_charTwo K) (fun g x => automorphism_trace g x)
    (fun g => automorphism_unit g)

/-- The quotient projection intertwines the actual octonion and natural actions. -/
@[simp] theorem action_mk (g : Model K) (x : TraceZero K) :
    action K g (mk K x) = mk K (traceZeroAction K g x) := rfl

/-- Formula directly in terms of the split-octonion automorphism. -/
theorem action_mk_explicit (g : Model K) (x : Carrier K) (hx : trace x = 0) :
    action K g (mk K ⟨x, hx⟩) =
      mk K ⟨g.val x, (automorphism_trace g x).trans hx⟩ := rfl

/-- Restriction to the actual derived subgroup; this retains the binary case. -/
def derivedAction : Representation K (commutator (Model K)) (Space K) :=
  (action K).comp (commutator (Model K)).subtype

@[simp] theorem derivedAction_apply (g : commutator (Model K)) (x : Space K) :
    derivedAction K g x = action K g.val x := rfl

@[simp] theorem derivedAction_mk (g : commutator (Model K)) (x : TraceZero K) :
    derivedAction K g (mk K x) = mk K (traceZeroAction K g.val x) := rfl

/-- The natural module is six-dimensional, including over the binary field. -/
@[simp] theorem finrank_space : Module.finrank K (Space K) = 6 :=
  Representation.G2Natural.finrank_space (traceLinearMap K) unit
    (trace_unit_charTwo K) (traceLinearMap_surjective K) unit_ne_zero
    (carrier_finrank K)

end Atlas.G2.Natural

namespace Representation

variable (K : Type*) [Field K] [CharP K 2]

/-- The natural six-dimensional representation of the actual split G₂ model. -/
abbrev g2Natural : Representation K (Atlas.G2.Model K) (Atlas.G2.Natural.Space K) :=
  Atlas.G2.Natural.action K

/-- The natural representation of G₂(K)', without excluding K = F₂. -/
abbrev g2DerivedNatural :
    Representation K (commutator (Atlas.G2.Model K)) (Atlas.G2.Natural.Space K) :=
  Atlas.G2.Natural.derivedAction K

end Representation
