module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.PlaneCentralizer
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupTheory.MaximalTwoLocalElementary

/-!
# The literal max4 endpoint for the pure-first normalizer argument

The previously certified elementary eight and its full ambient normalizer
show that the literal max4 subgroup is a two-local. This converts the strict
normalizer bound for its distinguished plane into exclusion at maximal
TWO-local level. The same ambient conjugator is retained in both the eight
normalizer equality and the plane exclusion. The radical consumer keeps the
actual subgroup inclusions and both restricted two-core identities.

The line/plane placement of arbitrary pure-2A groups remains a separate source
obligation. This module reuses the existing finite certificates without moving
them across the Theory/CFSG boundary or rechecking new copies.
Source: Kleidman--Wilson (1988), Corollary 1.2.2(a) and Section 2.1,
pp.488--489. Literal matrix provenance remains in the imported max4 modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers
open SymmetricLinear
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
attribute [local irreducible] modelGroup matrixA matrixB

/-- The whole native max4 group is a two-local, witnessed by its actual eight. -/
theorem max4_isTwoLocal : IsTwoLocal max4Subgroup := by
  let : IsElementaryAbelian 2 NormalEight.eight := NormalEight.elementary_eight
  let : IsElementaryAbelian 2 max4Eight := IsElementaryAbelian.map_subtype
  have hcard : Nat.card max4Eight = 8 :=
    (card_map_of_injective max4Subgroup.subtype_injective).trans NormalEight.card_eight
  have hne : max4Eight ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcard
    contradiction
  exact ⟨max4Eight, hne, IsElementaryAbelian.isPGroup 2 max4Eight,
    max4_eight_normalizer_eq.symm⟩

/-- The native eight's conjugate has exactly the corresponding max4 normalizer. -/
theorem conjugate_eight_normalizer (g : Model) :
    normalizer (max4Eight.map (MulAut.conj g).toMonoidHom : Set Model) =
      max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  rw [← map_equiv_normalizer_eq, max4_eight_normalizer_eq]

/-- The full normalizer of the literal plane is strictly inside a two-local. -/
theorem plane_normalizer_lt_max4 :
    normalizer (max4Plane : Set Model) < max4Subgroup :=
  max4Plane_normalizer_lt_of_marking Max4EightCentralizer.marking

/-- An arbitrary ambient conjugate of the literal plane cannot have a maximal
TWO-local normalizer. This uses strict containment, not subgroup maximality. -/
theorem conjugate_plane_not_maximal (g : Model) :
    ¬ IsMaximalTwoLocal
      (normalizer (max4Plane.map (MulAut.conj g).toMonoidHom : Set Model)) := by
  intro hmax
  have hle : normalizer (max4Plane.map (MulAut.conj g).toMonoidHom : Set Model) ≤
      max4Subgroup.map (MulAut.conj g).toMonoidHom := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono plane_normalizer_lt_max4.le
  have he := hmax.eq_of_le (max4_isTwoLocal.map_equiv (MulAut.conj g)) hle
  have he' : normalizer (max4Plane : Set Model) = max4Subgroup := by
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    simpa only [map_equiv_normalizer_eq] using he
  exact plane_normalizer_lt_max4.ne he'

/-- A source witness equal to a conjugate of the certified eight gives the
literal max4 endpoint for the original whole normalizer. -/
theorem max4_endpoint_of_eight_witness (X Z : Subgroup Model) (g : Model)
    (hNZ : normalizer (X : Set Model) = normalizer (Z : Set Model))
    (hZ : Z = max4Eight.map (MulAut.conj g).toMonoidHom) :
    normalizer (X : Set Model) = max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  rw [hNZ, hZ]
  exact conjugate_eight_normalizer g

/-- A maximal source witness cannot be conjugate to the distinguished plane. -/
theorem source_witness_not_plane (X Z : Subgroup Model)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hNZ : normalizer (X : Set Model) = normalizer (Z : Set Model)) :
    ¬ ∃ g : Model, Z = max4Plane.map (MulAut.conj g).toMonoidHom := by
  rintro ⟨g, hZ⟩
  apply conjugate_plane_not_maximal g
  rwa [hNZ, hZ] at hmax

/-- The actual arbitrary-radical application for a source normalizer that
normalizes a conjugate of the certified eight. All restricted maps are literal. -/
theorem radical_max4_of_eight_witness
    (P X Z : Subgroup Model) (g : Model) (hP : P.IsPRadical 2)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hNZ : normalizer (X : Set Model) ≤ normalizer (Z : Set Model))
    (hZ : Z = max4Eight.map (MulAut.conj g).toMonoidHom) :
    let M := max4Subgroup.map (MulAut.conj g).toMonoidHom
    IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype =
        normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  dsimp only
  let M := max4Subgroup.map (MulAut.conj g).toMonoidHom
  have hNM : normalizer (P : Set Model) ≤ M := by
    have h := hNX.trans hNZ
    rw [hZ, conjugate_eight_normalizer] at h
    exact h
  have hPM : P ≤ M := P.le_normalizer.trans hNM
  have hNN := hNM.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hNN
  refine ⟨max4_isTwoLocal.map_equiv (MulAut.conj g), hNM, hPM, ?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hNN, hcore, ?_⟩
  · rw [← subgroupOf_normalizer_eq hPM, map_subgroupOf_eq_of_le hNM]
  · rw [hcore, map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.PureFirstNormalizers
