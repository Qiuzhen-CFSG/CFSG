module

public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M11.Properties.Simplicity
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M12.Properties.Simplicity
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M22.Properties.Simplicity
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M24.Properties.Simplicity

/-!
# Shared finite-simple model facts for the quasithin ports

This file is the narrow CFSG-side interface used by the ATLAS ports.  It does
not identify a group from an order or from a classification predicate: a model
is supplied as an actual group together with independently proved finiteness,
order, and simplicity facts.  The five Mathieu instances below reuse the
explicit Witt-design models already proved in `Theory.Mathieu`.

The ATLAS source names and revision for the corresponding constructions are
recorded in `docs/atlas-port-map.md`.  The source modules are not imported
here, since the ATLAS checkout uses a different Lean/mathlib revision and its
Conway/Leech closure is much wider than this stable interface.
-/

@[expose] public section

namespace AtlasPort

/-- A concrete finite simple group model with its verified order.

The `Finite` and `Group` instances are parameters of the carrier, so clients
can use the record without unpacking duplicate instance fields. -/
structure SimpleFiniteModel (G : Type*) [Group G] [Finite G] where
  /-- The numerical order attached to the model. -/
  order : ℕ
  /-- The carrier has the advertised order. -/
  card_eq_order : Nat.card G = order
  /-- Simplicity is proved for this concrete carrier. -/
  simple : IsSimpleGroup G

namespace Mathieu

/-- The ATLAS/CFSG model of `M₁₁` as the automorphism group of the Witt design. -/
noncomputable def M11 : SimpleFiniteModel Sporadic.Mathieu.M11 where
  order := 7920
  card_eq_order := Sporadic.Mathieu.m11_order
  simple := Sporadic.Mathieu.m11_isSimpleGroup

/-- The ATLAS/CFSG model of `M₁₂`. -/
noncomputable def M12 : SimpleFiniteModel Sporadic.Mathieu.M12 where
  order := 95040
  card_eq_order := Sporadic.Mathieu.m12_order
  simple := Sporadic.Mathieu.m12_isSimpleGroup

/-- The ATLAS/CFSG model of `M₂₂`. -/
noncomputable def M22 : SimpleFiniteModel Sporadic.Mathieu.M22 where
  order := 443520
  card_eq_order := Sporadic.Mathieu.m22_order
  simple := Sporadic.Mathieu.m22_isSimpleGroup

/-- The ATLAS/CFSG model of `M₂₃`. -/
noncomputable def M23 : SimpleFiniteModel Sporadic.Mathieu.M23 where
  order := 10200960
  card_eq_order := Sporadic.Mathieu.m23_order
  simple := Sporadic.Mathieu.m23_isSimpleGroup

/-- The ATLAS/CFSG model of `M₂₄`. -/
noncomputable def M24 : SimpleFiniteModel Sporadic.Mathieu.M24 where
  order := 244823040
  card_eq_order := Sporadic.Mathieu.m24_order
  simple := Sporadic.Mathieu.m24_isSimpleGroup

@[simp] theorem M11_card : Nat.card Sporadic.Mathieu.M11 = M11.order := M11.card_eq_order
@[simp] theorem M12_card : Nat.card Sporadic.Mathieu.M12 = M12.order := M12.card_eq_order
@[simp] theorem M22_card : Nat.card Sporadic.Mathieu.M22 = M22.order := M22.card_eq_order
@[simp] theorem M23_card : Nat.card Sporadic.Mathieu.M23 = M23.order := M23.card_eq_order
@[simp] theorem M24_card : Nat.card Sporadic.Mathieu.M24 = M24.order := M24.card_eq_order

theorem M11_simple : IsSimpleGroup Sporadic.Mathieu.M11 := M11.simple
theorem M12_simple : IsSimpleGroup Sporadic.Mathieu.M12 := M12.simple
theorem M22_simple : IsSimpleGroup Sporadic.Mathieu.M22 := M22.simple
theorem M23_simple : IsSimpleGroup Sporadic.Mathieu.M23 := M23.simple
theorem M24_simple : IsSimpleGroup Sporadic.Mathieu.M24 := M24.simple

end Mathieu

end AtlasPort
