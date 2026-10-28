module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.MixedIntersection
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.Line

/-!
# Whole-normalizer endpoints for all twenty-six native rows

The line row uses its certified full max4 normalizer. Every other row uses a
second-class member of its canonical F intersection. Actual ambient conjugation
transports these endpoints and the arbitrary-radical restriction. The independent
finite census must still supply an actual row for an arbitrary all-row-two pure
subgroup; this module does not assume or assert that exhaustive classification.
Source: Kleidman--Wilson (1988), Corollary 1.2.2(a), Section 2.1 and Proposition
2.2.3, pp.488--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open FiniteConfigurations LargeCenterRadicals
attribute [local irreducible] modelGroup matrixA matrixB

/-- Whole-normalizer placement for every one of the twenty-six literal rows. -/
theorem row_nativeLocalPlacement (i : Fin 26)
    (hmax : IsMaximalTwoLocal (normalizer (row i : Set Model))) :
    NativeLocalPlacement (normalizer (row i : Set Model)) := by
  by_cases hi : i = 5
  · subst i
    exact line_row_nativeLocalPlacement
  · exact nonline_row_whole_normalizer i hi hmax

/-- A literal conjugate-row identification transports the whole normalizer.
The independent finite census must supply this identification for an arbitrary
pure all-row-two subgroup. -/
theorem conjugate_row_nativeLocalPlacement (X : Subgroup Model)
    (g : Model) (i : Fin 26) (hX : X.map (MulAut.conj g).toMonoidHom = row i)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    NativeLocalPlacement (normalizer (X : Set Model)) := by
  have hmap : (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
      normalizer (row i : Set Model) := by rw [map_equiv_normalizer_eq,hX]
  have hi : IsMaximalTwoLocal (normalizer (row i : Set Model)) :=
    hmap ▸ isMaximalTwoLocal_map (MulAut.conj g) hmax
  have h := (row_nativeLocalPlacement i hi).map_conj g⁻¹
  rw [← hmap,map_map] at h
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Model := by ext x; simp [mul_assoc]
  rwa [he,map_id] at h

/-- Actual arbitrary-radical restriction once the independent census supplies
its row. No F incidence, mixed witness or normalizer-placement premise remains;
the subgroup inclusions are the literal original ambient ones. -/
theorem radical_local_of_conjugate_row (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (hPX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (g : Model) (i : Fin 26) (hX : X.map (MulAut.conj g).toMonoidHom = row i) :
    ∃ H : Subgroup Model, IsTwoLocal H ∧ NativeLocalPlacement H ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  let H := normalizer (X : Set Model)
  have hPH : P ≤ H := P.le_normalizer.trans hPX
  have hN := hPX.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨H,hmax.1,conjugate_row_nativeLocalPlacement X g i hX hmax,hPX,hPH,?_,
    hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hPX]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
