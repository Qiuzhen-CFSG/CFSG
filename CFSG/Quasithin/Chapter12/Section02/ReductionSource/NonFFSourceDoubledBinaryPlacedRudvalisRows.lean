module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedNative
public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.ElementarySixtyFour

/-!
# Four native Rudvalis placements for the original doubled orbit

The original component marking sends the complete natural--dual orbit to an
elementary subgroup of order sixty-four. The native Sylow certificate now
places that actual image in one of four explicit rows, by ambient conjugacy.
No ambient Sylow normalizes the orbit and no odd-index assumption is used.

This discharges the elementary-subgroup placement needed for the Ru line of
Aschbacher--Smith 4.4.3, printed pp.622--623. The normalizer action on these
rows and the final natural--dual exclusion remain separate obligations.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
/-- The same native marking puts the whole original orbit in a certified row. -/
theorem native_geometry_rudvalis_elementary_row
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Rudvalis.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Rudvalis.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      ∃ hWK : D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype,
        let w := m.toMonoidHom.comp (inclusion hWK)
        ∃ g : Rudvalis.Model, ∃ j : Fin 4,
          w.range.map (MulAut.conj g).toMonoidHom =
            Rudvalis.BinaryThreeModules.ElementarySixtyFour.row j := by
  obtain ⟨_,_,m,hm,_,_,hWK,hcard,_⟩ := hg
  let w := m.toMonoidHom.comp (inclusion hWK)
  let : IsElementaryAbelian 2 w.range :=
    IsElementaryAbelian.of_surjective w.rangeRestrict w.rangeRestrict_surjective
  exact ⟨m,hm,hWK,
    Rudvalis.BinaryThreeModules.ElementarySixtyFour.exists_conjugate_row w.range hcard⟩

/-- Original chosen-module hypotheses provide the actual orbit placement. -/
theorem sourceOrbit_binary_rudvalis_elementary_row
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Rudvalis.Model) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Rudvalis.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      ∃ hWK : D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype,
        let w := m.toMonoidHom.comp (inclusion hWK)
        ∃ g : Rudvalis.Model, ∃ j : Fin 4,
          w.range.map (MulAut.conj g).toMonoidHom =
            Rudvalis.BinaryThreeModules.ElementarySixtyFour.row j := by
  exact D.native_geometry_rudvalis_elementary_row A K hr e
    (D.sourceOrbit_binary_oddNormalizer_native_placement
      h hd F hF hmodel A hAC ho hu K hK hcore hr .ru (Or.inr rfl) e)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
