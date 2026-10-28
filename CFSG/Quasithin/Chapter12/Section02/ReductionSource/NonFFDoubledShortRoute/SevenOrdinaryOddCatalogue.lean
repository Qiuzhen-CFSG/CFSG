module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryLieB
-- Reuse the full-orbit component detector and actual central-quotient marking.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticOddAction
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryPlacement

/-!
# The original A7 odd-normalizer component is J4

Residual uniqueness and an escaping abelian odd normalizer produce a moved
ordinary component. Inner action places the actual perfect residual and the
whole rank-eight orbit in it. The full Theorem B catalogue, with the actual
residual maps into each parabolic, leaves only the J4 central quotient.
Source: Aschbacher--Smith 4.4.7--12, printed pp.620--623, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl ChapterA.Section02

private theorem seven_residual_janko
    {G : Type*} [Group G] [Finite G]
    (F K U : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (π : F →* alternatingGroup (Fin 7)) (hπ : Function.Surjective π)
    (hm : IsTheoremBModel (K ⧸ center K)) (hr : 8 ≤ primeRank 2 (K ⧸ center K)) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  rcases hm.remaining_of_twoRank_ge_eight hr with ho | hb | ⟨n,hb⟩ | hs | hj
  · exact (no_theoremB_odd_model_of_twoRank_ge_eight hr ho).elim
  · exact (no_bender_of_residual_module K F U hFK hUF hne hcomm hb).elim
  · exact (no_BrankTwo_of_seven_residual_module F K U hFK hUF hne hcomm π hπ hb).elim
  · exact (no_binary_symplectic_six_of_seven_residual_module
      F K U hFK hUF hne hcomm π hπ hs).elim
  · exact hj

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The same component selected by the original odd-normalizer escape has
central quotient J4 and contains the entire original orbit and residual. -/
theorem sourceOrbit_seven_oddNormalizer_janko_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  have hsize : 8 < Nat.card D.sourceOrbit := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_seven_dimension h hd σ hmodel] at hh
    rw [hh]
    decide
  obtain ⟨K,hK,_,houtK,hcore,hqt,_,_,_⟩ :=
    D.sourceOrbit_whole_oddNormalizer_component_of_large h hd hsize A hne hAC ho hu hout
  obtain ⟨hKn,hWK,hRK,hcent,hr⟩ :=
    D.sourceOrbit_seven_oddNormalizer_placement h hd σ hmodel A hne hAC ho hu hout K hK houtK
  refine ⟨K,hK,hKn,houtK,hcore,hWK,hRK,hcent,?_⟩
  let := hK.2
  have hkg := ((oddNormalizer_properQTK h.simpleQTKE A hne).2.2).subgroup K
  have hm := quasisimple_centralQuotient_theoremBModel theoremA_knownSimple theoremB_knownSimple hqt hkg
  let N := normalizer (A : Set G)
  let K₀ := K.map N.subtype
  let F := oddActorResidual L A
  let e := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let z := QuotientGroup.congr (center K₀) (center K) e
    (Theory.GroupTheory.FixedElementary.map_center e)
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  obtain ⟨_,hmove,hUF,_⟩ := D.doubledOrbit_oddActorResidual_cover h A hA ho
  rw [←D.sourceOrbit_eq] at hmove hUF
  obtain ⟨b,_⟩ := chosen_oddActorResidual_quotient h.toHypothesis1221 D A
    (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T)))
  obtain ⟨eL⟩ := D.doubled_seven_simple_quotient h σ hmodel
  let π : F →* alternatingGroup (Fin 7) := eL.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))))
  have hπ : Function.Surjective π := eL.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (b.surjective.comp (QuotientGroup.mk'_surjective _)))
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  obtain ⟨a⟩ := seven_residual_janko F K₀ D.sourceOrbit hRK hUF
    D.sourceOrbit_weakClosure_setup.nontrivial hmove π hπ (hm.of_mulEquiv z)
    (by rwa [primeRank_equiv 2 z])
  exact ⟨z.symm.trans a⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
