module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.LiteralLocal.Centralizer
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.LiteralLocal.Generation

/-!
# Centralization and generation for the literal Held local pair

The seed is exactly the join of catalogue rows 20 and 21, and the second local
is its full normalizer in the degree-2058 Held carrier. Finite permutation and
graph certificates prove that the ambient centralizer of the seed lies in it
and that its normalizer generates Held with the centralizer of the Sylow center.
The normal two-subgroup supplied by the seed then proves that the normalizer's
intrinsic two-core is self-centralizing.

These discharge the two literal-local premises of the canonical pair assembly.
Identifying the seed with the invariant elementary family remains the separate
input owned by that assembly. Source: GLS3 Table 5.3p and the sporadic generation
argument in Aschbacher--Smith, printed p.526.
-/

public section
namespace Held.AutomorphismLocalPair
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- Ambient centralization of the unchanged join of catalogue rows 20 and 21. -/
theorem representativeLargeSeed_centralizer_le :
    centralizer (representativeLargeSeed : Set He) ≤ representativeLargeSeed :=
  LiteralLocal.seed_centralizer_le

/-- Characteristic two inside the full normalizer, using its actual intrinsic core. -/
theorem representativeLargeLocal_selfCentralizingCore :
    centralizer (pCore 2 representativeLargeLocal : Set representativeLargeLocal) ≤
      pCore 2 representativeLargeLocal := by
  intro x hx
  apply representativeLargeKernel_le_pCore
  apply representativeLargeSeed_centralizer_le
  intro y hy
  have hyK : (⟨y, representativeLargeSeed.le_normalizer hy⟩ : representativeLargeLocal) ∈
      representativeLargeKernel := hy
  exact congrArg Subtype.val (hx _ (representativeLargeKernel_le_pCore hyK))

/-- Generation by the first canonical local and the full literal seed normalizer. -/
theorem representative_locals_generate :
    centerLocal representative ⊔ representativeLargeLocal = ⊤ :=
  LiteralLocal.locals_generate

end Held.AutomorphismLocalPair
