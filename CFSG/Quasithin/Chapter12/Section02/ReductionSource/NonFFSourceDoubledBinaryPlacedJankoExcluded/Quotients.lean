module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded.Radical
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.ResidualQuotients

/-!
# The original binary J₄ geometry excludes the three simple radical quotients

Keep the native map of the original component and residual. Relative normality
makes the residual's full two-core quotient a normal image in the quotient of
its whole normalizer. Its order 168 excludes each of the simple groups SL₅(2),
M₂₄ and A₈. The radical and its center bound are retained for the missing global
coverage step; this module does not assert that coverage or the J₄ exclusion.

Source: Aschbacher--Smith 4.4.3, pp.622--623; An--O'Brien--Wilson (2003),
Section 4 and Table 1, pp.122,124.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The same native map gives the large-center radical and excludes every
candidate simple quotient of its full normalizer. -/
theorem native_janko_geometry_quotients_excluded
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
        ¬ (Nonempty ((M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
           Nonempty ((M ⧸ pCore 2 M) ≃* Sporadic.Mathieu.M24) ∨
           Nonempty ((M ⧸ pCore 2 M) ≃* alternatingGroup (Fin 8))) := by
  obtain ⟨m,hm,hP,hN,hlarge,hn,⟨a⟩⟩ := D.native_janko_geometry_radical A K hr e hg
  refine ⟨m,hm,hP,hN,hlarge,?_⟩
  let := hn
  exact Janko4.LocalStructure.LargeCenterRadicals.binaryThree_normal_residual_quotients_excluded _ a

/-- Original chosen-module hypotheses discharge the native geometry on the
same component; no extra quotient, module or normality premise is assumed. -/
theorem sourceOrbit_binary_oddNormalizer_janko_quotients_excluded
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
        ¬ (Nonempty ((M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
           Nonempty ((M ⧸ pCore 2 M) ≃* Sporadic.Mathieu.M24) ∨
           Nonempty ((M ⧸ pCore 2 M) ≃* alternatingGroup (Fin 8))) := by
  apply D.native_janko_geometry_quotients_excluded A K hr e
  exact D.sourceOrbit_binary_oddNormalizer_native_placement h hd F hF hmodel A hAC ho hu
    K hK hcore hr .j4 (Or.inl rfl) e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
