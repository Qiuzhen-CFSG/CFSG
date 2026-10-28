/-
Copyright (c) 2026 Gerald Höhn.
The underlying construction is adapted from ATLAS,
Atlas/Sporadic/Janko2.lean, Janko2Structure.lean, and Janko2Construction.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Sporadic.Janko2Construction
public import Theory.AtlasPort.ModelFacts

/-!
# The concrete Hall–Janko model

The carrier is the full right-quaternion-linear Hermitian stabilizer of the
icosian Leech lattice, divided by its two central signs. Its action on 525
frames, each with stabilizer of order 2304, gives linear-cover order 1209600
and quotient order 604800. Reflection generation, perfectness, and the
primitive action on 315 root lines give simplicity by Iwasawa's criterion.

The imported construction also proves the integral lattice comparison, the
faithful quaternionic projective action, and the compatible embeddings of
the linear cover, central product, and projective quotient into the Leech
groups. It identifies the scalar sign quotient with the alternating group
on five points and embeds its direct product with this model in the Leech
central quotient.

This module packages those independently proved facts as `SimpleFiniteModel`
without changing the ATLAS carrier or assuming a recognition theorem.
The source is Gerald Höhn's ATLAS construction at the revision above;
the port adapts imports, public boundaries, and proof syntax to Lean 4.33.0.
-/

public section

namespace AtlasPort.Janko2

/-- The actual projective icosian lattice group. -/
abbrev Model := Atlas.Sporadic.Janko2.Model

/-- The concrete carrier is finite. -/
theorem finite : Finite Model := Atlas.Sporadic.Janko2.finite

/-- The order obtained from the frame action and the two-sign quotient. -/
theorem card : Nat.card Model = 604800 := Atlas.Sporadic.Janko2.card

/-- Simplicity of the concrete quotient, proved by its primitive reflection action. -/
theorem simple : IsSimpleGroup Model := Atlas.Sporadic.Janko2.isSimpleGroup

/-- The verified finite-simple model consumed by the CFSG model catalogue. -/
def modelFacts : SimpleFiniteModel Model where
  order := 604800
  card_eq_order := card
  simple := simple

@[simp] theorem modelFacts_order : modelFacts.order = 604800 := by rfl

end AtlasPort.Janko2
