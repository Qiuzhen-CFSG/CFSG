module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded.Quotients
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.RowExclusions

/-!
# Actual Mathieu radical rows excluded in the original binary configuration

The existing original map supplies the radical and its full-normalizer quotient
exclusions. The native M24 and A8 row calculations now exclude every ambient
conjugate of E and of the octad preimage, preserving that very same map and
radical. Arbitrary radical coverage remains necessary for the terminal J4
exclusion; the Ru and maximal-pushing-up alternatives are unaffected.

Source: Aschbacher--Smith 4.4.3, pp.622--623; An--O'Brien--Wilson (2003),
Section 4 and Table 1, pp.122,124.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Both computed rows are excluded for the actual radical supplied by the
original native geometry, retaining the original quotient marking. -/
theorem native_janko_geometry_not_mathieu_rows
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      let M := normalizer (r.range : Set Janko4.Model)
      let P := M.pCoreIn 2
      IsPRadical 2 P ∧ normalizer (P : Set Janko4.Model) = M ∧
        64 ≤ Nat.card (center P) ∧
        (∀ g : Janko4.Model, P ≠
          Janko4.LocalStructure.ElementaryNormalizerCover.embeddedKernel.map
            (MulAut.conj g).toMonoidHom) ∧
        ∀ (O : Sporadic.Mathieu.M24LocalGeometry.Octad) (g : Janko4.Model),
          P ≠ (octadRadical O).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨m,hm,hP,hN,hlarge,hq⟩ := D.native_janko_geometry_quotients_excluded A K hr e hg
  refine ⟨m,hm,hP,hN,hlarge,?_⟩
  apply not_mathieu_rows_of_quotients_excluded
  dsimp only
  rw [hN]
  exact hq

/-- The original chosen-module hypotheses discharge the geometry for the same
component and exclude both computed native row families. -/
theorem sourceOrbit_binary_oddNormalizer_janko_not_mathieu_rows
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      let M := normalizer (r.range : Set Janko4.Model)
      let P := M.pCoreIn 2
      IsPRadical 2 P ∧ normalizer (P : Set Janko4.Model) = M ∧
        64 ≤ Nat.card (center P) ∧
        (∀ g : Janko4.Model, P ≠
          Janko4.LocalStructure.ElementaryNormalizerCover.embeddedKernel.map
            (MulAut.conj g).toMonoidHom) ∧
        ∀ (O : Sporadic.Mathieu.M24LocalGeometry.Octad) (g : Janko4.Model),
          P ≠ (octadRadical O).map (MulAut.conj g).toMonoidHom := by
  apply D.native_janko_geometry_not_mathieu_rows A K hr e
  exact D.sourceOrbit_binary_oddNormalizer_native_placement h hd F hF hmodel A hAC ho hu
    K hK hcore hr .j4 (Or.inl rfl) e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
