module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Inputs

/-!
# Transporting the selected natural-plus-dual action

The B.5.1 action uses SL₄(2) and an extra top-subgroup restriction. Compose
its actual actor equivalence with the canonical SL₄(2)–PSL₄(2) equivalence.
The matrix action and its full contragredient agree under this map.
The classified moved space equals the literal component commutator, so an
identity-on-vectors linear equivalence places the coordinates on the given
subrepresentation, retaining its marked point.

This transport is conditional on selecting the natural-plus-dual row;
it does not select that row from the classification alternatives.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1iii),
printed p.99, and its use in 15.3.49, p.1145.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection
open Chapter2.ComponentRefinement.LieType.Binary

/-- The source's matrix natural-plus-dual representation descends through
SLₙ(2) ≃ PSLₙ(2), including the inverse in the contragredient action. -/
theorem naturalDual_project (n : ℕ) [NeZero n] (g : SL n)
    (v : Vector n × Module.Dual (ZMod 2) (Vector n)) :
    naturalPlusDual n g v = BinaryGeometry.naturalDual n (slEquivPSL n g) v := by
  apply Prod.ext
  · exact (BinaryGeometry.natural_project n g v.1).symm
  · apply LinearMap.ext
    intro w
    change v.2 (linearNatural BinaryField.two n g⁻¹ w) =
      v.2 (BinaryGeometry.natural n (slEquivPSL n g)⁻¹ w)
    rw [← map_inv]
    exact congrArg v.2 (BinaryGeometry.natural_project n g⁻¹ w).symm

private theorem moved_top_eq_coinvariants {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V) :
    moved ρ ⊤ = Representation.Coinvariants.ker ρ := by
  unfold moved subspaceCommutator Representation.Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g, _, w, _, rfl⟩
    exact ⟨(g, w), rfl⟩
  · rintro ⟨⟨g, w⟩, rfl⟩
    exact ⟨g, mem_top g, w, Submodule.mem_top, rfl⟩

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (L : Subgroup K)
    (U : Subrepresentation ρ)
    (hU : U.toSubmodule = Coinvariants.ker (ρ.comp L.subtype))
    (s : MovedSection (ρ.comp L.subtype) ⊤)

include hU in
/-- The classified moved space equals the given commutator submodule;
no abstract isomorphic copy replaces the marked point's space. -/
theorem movedSection_space_eq : s.space.toSubmodule = U.toSubmodule :=
  s.space_eq.trans ((moved_top_eq_coinvariants _).trans hU.symm)

include hU in
/-- Transport the selected source summands to coordinates on the specified
subrepresentation, through an actual component-to-projective equivalence. -/
theorem coordinates_of_naturalDual
    (hnat : IsNaturalPlusDual
      (s.space.toRepresentation.comp (⊤ : Subgroup L).subtype) 4) :
    ∃ e : L ≃* PSL 4, Nonempty (NaturalDualCoordinates ρ L e U) := by
  obtain ⟨f⟩ := hnat
  let e : L ≃* PSL 4 :=
    ((Subgroup.topEquiv (G := L)).symm.trans f.groupEquiv).trans (slEquivPSL 4)
  let E : U.toSubmodule ≃ₗ[ZMod 2] s.space.toSubmodule :=
    LinearEquiv.ofEq _ _ (movedSection_space_eq ρ L U hU s).symm
  refine ⟨e, ⟨{ component_space := hU
                coordinates := E.trans f.linearEquiv
                equivariant := ?_ }⟩⟩
  intro g v
  change f.linearEquiv (E (U.toRepresentation g v)) =
    BinaryGeometry.naturalDual 4 (e g) (f.linearEquiv (E v))
  have hE : E (U.toRepresentation g v) = s.space.toRepresentation g (E v) :=
    Subtype.ext rfl
  rw [hE]
  exact (f.intertwines ⟨g, mem_top g⟩ (E v)).trans (naturalDual_project 4 _ _)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection
