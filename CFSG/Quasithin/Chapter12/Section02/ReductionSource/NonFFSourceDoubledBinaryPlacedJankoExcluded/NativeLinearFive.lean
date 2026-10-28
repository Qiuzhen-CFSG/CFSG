module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveRows.Classification
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded.LinearFiveLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.NativeLinearFive
/-!
# Discharging the original binary linear-five quotient premise

Use the native normalizer recognition with the same original component map,
whole module and normal residual. The arbitrary large-center radical quotient
calculation excludes every conjugate of N(F). Original maximality supplies the
radical and its full normalizer; the quotient calculation needs no further
maximality hypothesis. The earlier conditional interfaces remain available.

Source: Aschbacher--Smith 4.4.3 and its binary application in 12.2;
Kleidman--Wilson (1988), Lemma 1.1.1, p.485.
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

/-- The original radical center and residual marking exclude every conjugate
linear-five placement through its proved full normalizer quotient. -/
theorem native_janko_geometry_not_recognized_linearFive_local
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e) :
    ∃ m : K.map (normalizer (A : Set G)).subtype ≃* Janko4.Model,
      (∀ x, m x = e (QuotientGroup.mk' (center K)
        ((K.equivMapOfInjective _ (normalizer (A : Set G)).subtype_injective).symm x))) ∧
      let r := m.toMonoidHom.comp (inclusion hr)
      ∀ g : Janko4.Model, ¬ normalizer (r.range : Set Janko4.Model) ≤
        (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨m,hm,hP,hN,hlarge,hq⟩ := D.native_janko_geometry_quotients_excluded A K hr e hg
  refine ⟨m,hm,?_⟩
  dsimp only
  intro g
  have h := Janko4.LocalStructure.LargeCenterRadicals.LinearFiveRows.not_le_conjugate_of_quotients_excluded
    _ hP hlarge (by dsimp only; rw [hN]; exact hq) g
  simpa only [hN] using h

/-- Apply the recognized local exclusion to the literal original doubled
binary configuration, retaining its component, actor and quotient marking. -/
theorem sourceOrbit_binary_oddNormalizer_janko_not_recognized_linearFive_local
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
        (normalizer (Janko4.LocalStructure.LinearFive.F : Set Janko4.Model)).map
          (MulAut.conj g).toMonoidHom := by
  apply D.native_janko_geometry_not_recognized_linearFive_local A K hr e 
  exact D.sourceOrbit_binary_oddNormalizer_native_placement h hd F hF hmodel A hAC ho hu
    K hK hcore hr .j4 (Or.inl rfl) e
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
