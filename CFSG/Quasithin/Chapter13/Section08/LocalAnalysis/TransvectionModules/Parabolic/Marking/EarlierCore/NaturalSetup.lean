module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Notation
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The ordinary natural module and its source flag

This records the representation data preceding 13.5.4: a genuine A₆
quotient of L, the compatible action of LT on the literal subgroup V,
and the T-invariant flag of dimensions one, two and three. The coordinate
map is an equivalence on V itself, not just on an unrelated section.
The ambient T is a Sylow subgroup, so its image in any action is Sylow.

No residual action, generation identity, local centralizer or core bound
is included. Global standing hypotheses and the earlier local theorem
remain separate from these representation data.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877; 13.3.3, p.885; 13.5.3, p.916.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore

open Subgroup

abbrev Natural := BinaryPermutation.natural (Fin 6)

variable {G : Type*} [Group G]

/-- The actual subgroup corresponding to a natural subspace. -/
def flagPreimage {V : Subgroup G} (e : V ≃* Multiplicative Natural)
    (P : Submodule (ZMod 2) Natural) : Subgroup G :=
  ((P.toAddSubgroup.toSubgroup).comap e.toMonoidHom).map V.subtype

theorem flagPreimage_le {V : Subgroup G} (e : V ≃* Multiplicative Natural)
    (P : Submodule (ZMod 2) Natural) : flagPreimage e P ≤ V := map_subtype_le _

theorem mem_flagPreimage_iff {V : Subgroup G} (e : V ≃* Multiplicative Natural)
    (P : Submodule (ZMod 2) Natural) (v : V) :
    v.val ∈ flagPreimage e P ↔ (e v).toAdd ∈ P := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (show w = v from Subtype.ext he) ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Ordinary A₆ natural action with a compatible Sylow-invariant flag.
The A₆ witness is supplied independently by 13.7.6 in the source application. -/
structure NaturalSetup (T : Sylow 2 G) (L V V₁ V₂ V₃ : Subgroup G) where
  model : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)
  normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G)
  normalizes_V : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
  permutation : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6)
  model_compatible : ∀ l : L,
    permutation (inclusion le_sup_left l) = (model (QuotientGroup.mk' (pCore 2 L) l)).val
  coordinate : V ≃* Multiplicative Natural
  conjugation : ∀ (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
    (coordinate (V.normalizerMonoidHom ⟨g.val, normalizes_V g.property⟩ v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (permutation g) (coordinate v).toAdd
  point : Submodule (ZMod 2) Natural
  plane : Submodule (ZMod 2) Natural
  hyperplane : Submodule (ZMod 2) Natural
  point_dim : Module.finrank (ZMod 2) point = 1
  plane_dim : Module.finrank (ZMod 2) plane = 2
  hyperplane_dim : Module.finrank (ZMod 2) hyperplane = 3
  point_le_plane : point ≤ plane
  plane_le_hyperplane : plane ≤ hyperplane
  line_eq : V₁ = flagPreimage coordinate point
  plane_eq : V₂ = flagPreimage coordinate plane
  seed_eq : V₃ = flagPreimage coordinate hyperplane
  line_stable : (T : Subgroup G) ≤ normalizer (V₁ : Set G)
  plane_stable : (T : Subgroup G) ≤ normalizer (V₂ : Set G)
  seed_stable : (T : Subgroup G) ≤ normalizer (V₃ : Set G)

namespace NaturalSetup

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)

include d

theorem line_le_plane : V₁ ≤ V₂ := by
  calc
    V₁ = flagPreimage d.coordinate d.point := d.line_eq
    _ ≤ flagPreimage d.coordinate d.plane := map_mono (comap_mono d.point_le_plane)
    _ = V₂ := d.plane_eq.symm

theorem plane_le_seed : V₂ ≤ V₃ := by
  calc
    V₂ = flagPreimage d.coordinate d.plane := d.plane_eq
    _ ≤ flagPreimage d.coordinate d.hyperplane := map_mono (comap_mono d.plane_le_hyperplane)
    _ = V₃ := d.seed_eq.symm

theorem seed_le : V₃ ≤ V := by
  rw [d.seed_eq]
  exact flagPreimage_le _ _

/-- The ordinary L₂ agrees with the residual convention used in 13.2.1. -/
theorem plane_residual_eq [Finite G] :
    residual ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₂ : Set G)) = localResidual L V₂ :=
  residual_relative_normalizer_eq L T V₂ T.isPGroup' d.normalizes_L d.plane_stable

/-- The same convention bridge for L₁, needed for the flag generation. -/
theorem line_residual_eq [Finite G] :
    residual ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G)) = localResidual L V₁ :=
  residual_relative_normalizer_eq L T V₁ T.isPGroup' d.normalizes_L d.line_stable

end NaturalSetup

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore

end
