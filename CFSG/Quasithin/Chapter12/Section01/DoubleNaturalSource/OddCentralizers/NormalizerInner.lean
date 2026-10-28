module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerComponentModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterUnitary

/-!
# Inner action in the degree-five odd normalizer

The actual fixed residual has its original GL₅(2) quotient. The complete
outer-section exclusion applies through the canonical GL₅(2)-to-PSL₅(2)
comparison, retaining the full central cover of the selected component.
Thus the component is normal, contains the whole doubled orbit and the
residual, and has central quotient J₄. Residual uniqueness is still the
explicit branch premise; the pushing-up branch remains separate.

Source: Aschbacher--Smith, 4.4.10--12 and 12.1.9(1), pp.621--623,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter12.Section05.NaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include D h

/-- The original fixed residual acts inner on every selected component.
The full B-catalogue and the literal quotient marking discharge all outer cases. -/
theorem doubledFive_oddNormalizer_inner (B : DoubledBranch T L V 5)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) :
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))) := by
  rcases D.doubledOrbit_oddNormalizer_inner_or_outer_section h B A hA ho K hK with hi | he
  · exact hi
  · let := hK.2
    obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK h.simpleQTKE A hne
    have hm := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
      (hqt.subgroup K) (hkg.subgroup K)
    obtain ⟨U,f,hf⟩ := he
    let e := (projectiveEquivLinear (by decide : 0 < 5)).symm.trans
      Representation.SL5TenDimensional.projectiveEquiv.symm
    exact (exterior_no_outer_section hm
      ⟨U,e.toMonoidHom.comp f,e.surjective.comp hf⟩).elim

/-- Under residual uniqueness the selected normal component is an actual
J₄ cover containing the full orbit; no outer-section alternative survives. -/
theorem doubledFive_oddNormalizer_janko_of_unique (B : DoubledBranch T L V 5)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
      componentOrbit V (T : Subgroup G) ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  obtain ⟨K,hK,hm,houtK,hcore,hcases⟩ :=
    D.doubledFive_oddNormalizer_component_of_unique h B A hne hA ho hu hout
  rcases hcases with he | hi
  · let := hK.2
    obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK h.simpleQTKE A hne
    have hb := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
      (hqt.subgroup K) (hkg.subgroup K)
    obtain ⟨U,f,hf⟩ := he.1
    let e := (projectiveEquivLinear (by decide : 0 < 5)).symm.trans
      Representation.SL5TenDimensional.projectiveEquiv.symm
    exact (exterior_no_outer_section hb
      ⟨U,e.toMonoidHom.comp f,e.surjective.comp hf⟩).elim
  · exact ⟨K,hK,hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
