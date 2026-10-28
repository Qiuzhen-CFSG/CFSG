module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded.MathieuLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveLocal
/-!
# The original binary configuration excludes the linear-five local

The original maximal-two-local normalizer cannot lie in a conjugate of N(F)
whose full intrinsic quotient is SL₅(2): equality would contradict its marked
normal SL₃(2) residual. The same component map and original hypotheses are
retained. The precise native quotient remains the independent F producer's
input; construction of F itself already supplies the two-local witness.

Source: Aschbacher--Smith 4.4.3 and the original binary application in 12.2;
Kleidman--Wilson (1988), Lemma 1.1.1, p.485. This conditional branch exclusion
does not assert the global native cover or the terminal J₄ exclusion.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Source maximality excludes every conjugate linear-five placement once the
independent native full-core quotient is supplied. -/
theorem native_janko_geometry_not_linearFive_local
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e)
    (eF : ((normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)) ⧸
      pCore 2 (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model))) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      ∀ g : Janko4.Model, ¬ normalizer (r.range : Set Janko4.Model) ≤
        (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨m,hm,_,_,_,hq⟩ := D.native_janko_geometry_quotients_excluded A K hr e hg
  obtain ⟨_,_,m',hm',hu,_⟩ := hg
  have he : m' = m := by
    ext x
    exact (hm' x).trans (hm x).symm
  subst m'
  exact ⟨m,hm,fun g => maximal_local_not_le_native_conjugate _ hu.1
    (fun h => hq (Or.inl h)) eF g⟩

/-- Apply the conditional local exclusion to the literal original doubled
binary configuration, retaining its component, actor and quotient marking. -/
theorem sourceOrbit_binary_oddNormalizer_janko_not_linearFive_local
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (eF : ((normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)) ⧸
      pCore 2 (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model))) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      ∀ g : Janko4.Model, ¬ normalizer (r.range : Set Janko4.Model) ≤
        (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)).map
          (MulAut.conj g).toMonoidHom := by
  apply D.native_janko_geometry_not_linearFive_local A K hr e (eF := eF)
  exact D.sourceOrbit_binary_oddNormalizer_native_placement h hd F hF hmodel A hAC ho hu
    K hK hcore hr .j4 (Or.inl rfl) e
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
