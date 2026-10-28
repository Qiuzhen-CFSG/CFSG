module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedNative
public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.EvenIndex

/-!
# The original Rudvalis native local has even index

The original native equivalence maps the complete doubled orbit to an
elementary subgroup of order 64. The fixed-Sylow elementary catalogue bounds
every Sylow-normalized elementary subgroup by 32, so this orbit's native
normalizer has even index. Relative normality places every two-local over
the same residual inside that normalizer; all these locals have even index.
The original equality of the orbit and residual normalizers is retained.

This proves that the odd-index maximal-subgroup cover cannot apply to the
actual native branch, even after obtaining subgroup maximality. It leaves
the specialized even-index local inspection and both native exclusions open,
and does not alter the separate maximal pushing-up alternative.
Source: the final inspection in Aschbacher–Smith 4.4.3, printed pp.622–623
of `refs/quasithin.pdf`. All maps come from the original component marking.
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
/-- The same native residual normalizer, and every two-local over that
residual, have even index in the original Rudvalis model. -/
theorem native_geometry_rudvalis_even_index
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Rudvalis.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Rudvalis.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      2 ∣ (normalizer (r.range : Set Rudvalis.Model)).index ∧
      ∀ B : Subgroup Rudvalis.Model, IsTwoLocal B → r.range ≤ B → 2 ∣ B.index := by
  obtain ⟨_,_,m,hm,_,_,hWK,hcard,_,_,_,hN,hnormal,_⟩ := hg
  let w := m.toMonoidHom.comp (inclusion hWK)
  let : IsElementaryAbelian 2 w.range :=
    IsElementaryAbelian.of_surjective w.rangeRestrict w.rangeRestrict_surjective
  have hi := Rudvalis.BinaryThreeModules.elementary_normalizer_even_index w.range
    (by rw [hcard]; decide)
  refine ⟨m,hm,hN ▸ hi,?_⟩
  intro B hB hRB
  obtain ⟨_,hWB,hn⟩ := hnormal B hB hRB
  exact hi.trans (index_dvd_of_le ((normal_subgroupOf_iff_le_normalizer hWB).mp hn))

/-- Original chosen-module hypotheses supply the even-index obstruction on
the actual chosen component and quotient marking, without additional premises. -/
theorem sourceOrbit_binary_rudvalis_even_index
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
      let r := m.toMonoidHom.comp (inclusion hr)
      2 ∣ (normalizer (r.range : Set Rudvalis.Model)).index ∧
      ∀ B : Subgroup Rudvalis.Model, IsTwoLocal B → r.range ≤ B → 2 ∣ B.index := by
  exact D.native_geometry_rudvalis_even_index A K hr e
    (D.sourceOrbit_binary_oddNormalizer_native_placement
      h hd F hF hmodel A hAC ho hu K hK hcore hr .ru (Or.inr rfl) e)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
