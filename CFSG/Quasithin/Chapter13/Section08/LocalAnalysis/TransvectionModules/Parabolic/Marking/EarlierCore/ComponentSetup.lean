module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Extension

/-!
# Natural L-action and a compatible Sylow flag

This input only specifies the source L-action on the literal V, the actual
ordinary quotient, and the T-invariant flag. The full LT permutation action
is constructed using the intrinsic normalizer of the natural alternating
image. Thus the final local-core helper does not assume an additional
action extension or any of its residual or generation conclusions.

Source: Aschbacher–Smith, setup and Notation 13.2.1, pp.876–877,
and Remark 13.5.3, p.916.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
variable {G : Type*} [Group G]

/-- The given ordinary natural L-action and source flag, before extending to LT. -/
structure ComponentSetup (T : Sylow 2 G) (L V V₁ V₂ V₃ : Subgroup G) where
  model : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)
  normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G)
  normalizes_V : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
  coordinate : V ≃* Multiplicative Natural
  conjugation : ∀ (l : L) (v : V),
    (coordinate (V.normalizerMonoidHom
      ⟨l.val, normalizes_V (show l.val ∈ L ⊔ T from
        (show L ≤ L ⊔ T from le_sup_left) l.property)⟩ v)).toAdd =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
        (model (QuotientGroup.mk' (pCore 2 L) l)) (coordinate v).toAdd
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


/-- Construct the LT action while retaining the given quotient, coordinates,
and every literal flag subgroup. -/
noncomputable def ComponentSetup.extend {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : ComponentSetup T L V V₁ V₂ V₃) : NaturalSetup T L V V₁ V₂ V₃ := by
  let hex := exists_permutation_extension L T V d.normalizes_L d.normalizes_V
    d.model d.coordinate d.conjugation
  exact {
    model := d.model
    normalizes_L := d.normalizes_L
    normalizes_V := d.normalizes_V
    permutation := hex.choose
    model_compatible := hex.choose_spec.1
    coordinate := d.coordinate
    conjugation := hex.choose_spec.2
    point := d.point
    plane := d.plane
    hyperplane := d.hyperplane
    point_dim := d.point_dim
    plane_dim := d.plane_dim
    hyperplane_dim := d.hyperplane_dim
    point_le_plane := d.point_le_plane
    plane_le_hyperplane := d.plane_le_hyperplane
    line_eq := d.line_eq
    plane_eq := d.plane_eq
    seed_eq := d.seed_eq
    line_stable := d.line_stable
    plane_stable := d.plane_stable
    seed_stable := d.seed_stable }

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
