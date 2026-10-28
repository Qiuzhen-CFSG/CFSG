module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallPlaced
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallSymplectic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixOrdinaryLie
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFourLocal
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticOddAction
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallPlacement
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixOrdinaryLie

/-!
# The actual alternating-six Hall component has J4 central quotient

The complete outer-section obstruction places the whole rank-eight orbit
and original perfect residual in the selected Hall component. Its genuine
A6 quotient and nontrivial moved two-core rule out every linear-Levi row.
The independently proved PSU5(4) and Sp6(2) source exclusions close the
remaining Theorem B families, leaving the actual J4 central quotient.
Source: Aschbacher--Smith 4.4.7--12, printed pp.620--623, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl ChapterA.Section02

private theorem no_unitary_four_of_six_residual_module
    {G : Type*} [Group G] [Finite G]
    (F K U : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (π : F →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) := Group.IsPerfect.ofSurjective hπ
  have hS := Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
  obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  let : CharP E 2 := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.charP_two
    n (by omega) hcard
  obtain ⟨a⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J n (by omega) hcard hconj
  let t := e.trans a
  let r := residualQuotientMap hFK t
  let := residualQuotientMap_kernel_solvable hFK t
  obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm t
  exact no_unitary_four_local hS six_not_two_exponent π hπ J.conj J.conj_involutive
    n (by omega) hcard hconj _ hp hpne r hnorm

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The same component selected by the original odd-normalizer escape has
central quotient J4 and contains the entire original orbit and residual. -/
theorem sourceOrbit_six_oddNormalizer_janko_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  have hu := D.sourceOrbit_six_residual_uniqueness h hd hmodel A hAC ho
  have hsize : 8 < Nat.card D.sourceOrbit := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_six_dimension h hd hmodel] at hh
    rw [hh]
    decide
  obtain ⟨K,hK,_,houtK,hcore,hqt,_,_,_⟩ :=
    D.sourceOrbit_whole_oddNormalizer_component_of_large h hd hsize A hne hAC ho hu hout
  obtain ⟨hKn,hWK,hRK,hcent,hr⟩ :=
    D.sourceOrbit_six_oddNormalizer_placement h hd hmodel A hne hAC ho hout K hK houtK
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
  obtain ⟨eL⟩ := D.doubled_six_simple_quotient h hmodel
  let π : F →* alternatingGroup (Fin 6) := eL.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))))
  have hπ : Function.Surjective π := eL.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (b.surjective.comp (QuotientGroup.mk'_surjective _)))
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  rcases hm.remaining_of_twoRank_ge_eight hr with hodd | hb | ⟨n,hb⟩ | hs | hj
  · exact (no_theoremB_odd_model_of_twoRank_ge_eight hr hodd).elim
  · exact (no_bender_of_residual_module K₀ F D.sourceOrbit hRK hUF
      D.sourceOrbit_weakClosure_setup.nontrivial hmove (hb.of_mulEquiv z)).elim
  · have hc (hc : IsTheoremCRankTwoModel (K ⧸ center K) n) : False :=
      no_CrankTwo_of_six_residual_module F K₀ D.sourceOrbit hRK hUF
        D.sourceOrbit_weakClosure_setup.nontrivial hmove π hπ (hc.of_mulEquiv z)
    cases hb with
    | linear hn he => exact (hc (.linear hn he)).elim
    | symplectic hn he => exact (hc (.symplectic hn he)).elim
    | g2 hn he => exact (hc (.g2 hn he)).elim
    | triality hn he => exact (hc (.triality hn he)).elim
    | ree_f4 m hm hn he => exact (hc (.ree_f4 m hm hn he)).elim
    | symplectic_derived hn he => exact (hc (.symplectic_derived hn he)).elim
    | g2_derived hn he => exact (hc (.g2_derived hn he)).elim
    | tits hn he => exact (hc (.tits hn he)).elim
    | unitary_four hn he =>
      exact (no_unitary_four_of_six_residual_module F K₀ D.sourceOrbit hRK hUF
        D.sourceOrbit_weakClosure_setup.nontrivial hmove π hπ hn
        (he.of_mulEquiv z)).elim
    | unitary_five hn he =>
      exact (D.sourceOrbit_six_oddNormalizer_not_unitary_five h hd hmodel A hne hAC ho
        hout K hK houtK (by simpa [hn] using he)).elim
  · exact (D.sourceOrbit_six_oddNormalizer_not_symplectic h hd hmodel A hne hAC ho
      hout K hK houtK hs).elim
  · exact hj

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
