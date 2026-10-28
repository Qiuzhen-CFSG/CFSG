module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallUnitaryLocals

/-!
# The original A₆ Hall component cannot be an inner PSU₅(4) row

If the selected component is PSU₅(4), actual residual placement would put its
nonidentity two-core image in a native two-local normalizer. The original A₆
quotient and full central representation kernel then contradict the proved
perfect-local calculation. Hence this row forces an actual A₆ section of the
full outer group. That remaining outer duty is retained explicitly.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
open Theory.SpecificGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal PSU₅(4) Hall component forces an actual outer A₆ section.
No residual-containment, kernel or parabolic premise is added. -/
theorem sourceOrbit_six_oddNormalizer_unitary_five_outer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 5 4) :
    ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 6),
      Function.Surjective f := by
  rcases D.sourceOrbit_six_oddNormalizer_placement_or_outer
      h hd hmodel A hne hAC ho hout K hK houtK with hplaced | houter
  · obtain ⟨_,_,hRK,_,_⟩ := hplaced
    let N := normalizer (A : Set G)
    let K₀ := K.map N.subtype
    let R := oddActorResidual L A
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
    obtain ⟨m⟩ := hmodel
    let eL := (D.componentCentralQuotientEquiv h.quasisimple).trans
      ((QuotientGroup.congr _ _ m.groupEquiv
        (Theory.GroupTheory.FixedElementary.map_center m.groupEquiv)).trans
        ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
          QuotientGroup.quotientBot))
    let π : R →* alternatingGroup (Fin 6) := eL.toMonoidHom.comp
      ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
        (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))))
    have hπ : Function.Surjective π := eL.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (b.surjective.comp (QuotientGroup.mk'_surjective _)))
    let : Group.IsPerfect R := oddActorResidual_isPerfect L A
    obtain ⟨E,hE,hfin,J,hcard,hconj,⟨eK⟩⟩ := hm
    let : CharP E 2 := UnitaryFive.charP_two_of_card_sixteen hcard
    obtain ⟨a⟩ := UnitaryFive.projective_equiv_identity_four J hcard hconj
    let t := (z.trans eK).trans a
    let r := residualQuotientMap hRK t
    let := residualQuotientMap_kernel_solvable hRK t
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hRK hUF
      D.sourceOrbit_weakClosure_setup.nontrivial hmove t
    exact (no_six_unitary_five_local π hπ
      (BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J)
      hcard hconj rfl _ hp hpne r hnorm).elim
  · exact houter

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
