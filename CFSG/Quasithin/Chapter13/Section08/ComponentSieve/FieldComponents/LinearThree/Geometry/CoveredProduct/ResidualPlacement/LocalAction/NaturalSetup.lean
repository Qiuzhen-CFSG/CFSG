module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions
public import Theory.Representation.HexacodeAction.Cover
public import Theory.Representation.BinaryPermutation

/-!
# The natural action used by the covered local calculation

This interface records only the earlier local setup: the actual hexacode
triple cover, its six-letter quotient, conjugation on the binary natural
module, and the compatible Sylow-stable flag. The map from V has kernel
C_V(L), so it identifies the actual natural section, rather than an arbitrary
representation. No local residual quotient or inverter is assumed.

The central-preimage centralizer input is the explicit observation preceding
Notation 13.2.1. It already implies that L₀ centralizes V, and hence V₃.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§13.2, printed pp.876–877; the application is 13.8.21(1), printed p.957.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction

abbrev Natural := BinaryPermutation.natural (Fin 6)

variable {G : Type*} [Group G]

/-- Pull back an actual subspace of the natural section to the subgroup V. -/
def flagPreimage {V : Subgroup G} (f : V →* Multiplicative Natural)
    (P : Submodule (ZMod 2) Natural) : Subgroup G :=
  ((P.toAddSubgroup.toSubgroup).comap f).map V.subtype

theorem flagPreimage_le {V : Subgroup G} (f : V →* Multiplicative Natural)
    (P : Submodule (ZMod 2) Natural) : flagPreimage f P ≤ V := map_subtype_le _

theorem mem_flagPreimage_iff {V : Subgroup G} (f : V →* Multiplicative Natural)
    (P : Submodule (ZMod 2) Natural) (v : V) :
    v.val ∈ flagPreimage f P ↔ (f v).toAdd ∈ P := by
  constructor
  · rintro ⟨w, hw, he⟩
    have : w = v := Subtype.ext he
    exact this ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- The genuine earlier natural action and flag. The Sylow subgroup is relative
 to LT; the two residuals retain the definitions from Notation 13.2.1. -/
structure NaturalSetup (L T V V₁ V₃ : Subgroup G) where
  cover : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms
  normalizes_L : T ≤ normalizer (L : Set G)
  normalizes_V : L ⊔ T ≤ normalizer (V : Set G)
  sylow : Sylow 2 (L ⊔ T : Subgroup G)
  sylow_eq : (sylow : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T)
  elementary : IsMulCommutative V
  exponent_two : ∀ v : V, v ^ 2 = 1
  permutation : (L ⊔ T : Subgroup G) →* Equiv.Perm (Fin 6)
  cover_compatible : ∀ l : L,
    permutation (inclusion le_sup_left l) =
      (Atlas.Codes.hexEvenCoordinate (cover (QuotientGroup.mk' (pCore 2 L) l))).val
  naturalMap : V →* Multiplicative Natural
  naturalMap_surjective : Function.Surjective naturalMap
  naturalMap_kernel : naturalMap.ker = (centralizer (L : Set G)).comap V.subtype
  conjugation : ∀ (g : (L ⊔ T : Subgroup G)) (v : V),
    (naturalMap (V.normalizerMonoidHom ⟨g.val, normalizes_V g.property⟩ v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (permutation g) (naturalMap v).toAdd
  point : Submodule (ZMod 2) Natural
  hyperplane : Submodule (ZMod 2) Natural
  point_dim : Module.finrank (ZMod 2) point = 1
  hyperplane_dim : Module.finrank (ZMod 2) hyperplane = 3
  compatible : point ≤ hyperplane
  line_eq : V₁ = flagPreimage naturalMap point
  seed_eq : V₃ = flagPreimage naturalMap hyperplane
  line_stable : T ≤ normalizer (V₁ : Set G)
  seed_stable : T ≤ normalizer (V₃ : Set G)
  /-- The explicit earlier observation on p.876, not a local-action conclusion. -/
  centralPreimage_centralizes : centralPreimage L ≤ centralizer (V : Set G)

namespace NaturalSetup
variable {L T V V₁ V₃ : Subgroup G} (d : NaturalSetup L T V V₁ V₃)
include d

theorem line_le_seed : V₁ ≤ V₃ := by
  calc
    V₁ = flagPreimage d.naturalMap d.point := d.line_eq
    _ ≤ flagPreimage d.naturalMap d.hyperplane :=
      map_mono (comap_mono (show d.point.toAddSubgroup.toSubgroup ≤
        d.hyperplane.toAddSubgroup.toSubgroup from d.compatible))
    _ = V₃ := d.seed_eq.symm

theorem seed_le : V₃ ≤ V := by
  rw [d.seed_eq]
  exact flagPreimage_le _ _

/-- L₀ centralizes the whole source V, by its actual central-preimage definition. -/
theorem zero_centralizes : zero L ≤ centralizer (V : Set G) :=
  (residual_le _).trans d.centralPreimage_centralizes

/-- The central residual acts trivially on the seed, before passing to V₃/V₁. -/
theorem zero_seed_commutator : ⁅zero L, V₃⁆ ≤ V₁ := by
  have h : zero L ≤ centralizer (V₃ : Set G) :=
    d.zero_centralizes.trans (centralizer_le d.seed_le)
  have hc : ⁅zero L, V₃⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr h
  rw [hc]
  exact bot_le

end NaturalSetup
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
