module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded.MathieuRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.MaximalLocal
/-!
# The original binary J4 configuration cannot lie in a Mathieu local

The literal native geometry makes the original residual normalizer maximal
among two-locals. Its full-core quotient obstruction therefore excludes
containment in any conjugate of max1: maximality would give equality and the
proved native quotient would be M24. The same original quotient map and all
source witnesses are retained. Coverage and the other native local branches
remain necessary for the terminal J4 exclusion.

Source: Aschbacher--Smith 4.4.3, pp.622--623, and the original binary
application in 12.2; An--O'Brien--Wilson (2003), Section 4, p.122.
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

/-- Source maximality excludes the entire Mathieu local, for the same marked
native map. No full-Sylow containment or ambient coatom premise is used. -/
theorem native_janko_geometry_not_mathieu_local
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      ∀ g : Janko4.Model, ¬ normalizer (r.range : Set Janko4.Model) ≤
        Janko4.LocalStructure.ElementaryNormalizerCover.max1.map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨m,hm,_,_,_,hq⟩ := D.native_janko_geometry_quotients_excluded A K hr e hg
  obtain ⟨_,_,m',hm',hu,_⟩ := hg
  have he : m' = m := by
    ext x
    exact (hm' x).trans (hm x).symm
  subst m'
  exact ⟨m,hm,fun g => maximal_local_not_le_mathieu _ hu.1 hq g⟩

/-- The original doubled binary configuration excludes every conjugate Mathieu
local while retaining its original component, actor and quotient marking. -/
theorem sourceOrbit_binary_oddNormalizer_janko_not_mathieu_local
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
      ∀ g : Janko4.Model, ¬ normalizer (r.range : Set Janko4.Model) ≤
        Janko4.LocalStructure.ElementaryNormalizerCover.max1.map
          (MulAut.conj g).toMonoidHom := by
  apply D.native_janko_geometry_not_mathieu_local A K hr e
  exact D.sourceOrbit_binary_oddNormalizer_native_placement h hd F hF hmodel A hAC ho hu
    K hK hcore hr .j4 (Or.inl rfl) e
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
