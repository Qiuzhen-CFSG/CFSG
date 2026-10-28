module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Alternating
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SymplecticCubicResidual
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
public import Theory.SpecificGroups.G2.MultiplierFourTwoGroup
public import Theory.SpecificGroups.G2.MultiplierOrdinary.NondefiningPrimes
public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryLocalResidual
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.SpecificGroups.PSL5Two.UniversalCover

/-!
# Lie-family cubic exclusions for the original plane component

The second cubic in N_G(A) survives outside C_G(A) after quotienting by
O₂(J). The actual C.2.7 comparison J/O₂(J) → J* is a perfect central
cover. The symplectic, G₂ and binary degree-five covering calculations
make its kernel a two-group, hence trivial in the original two-core
quotient. This includes the exceptional G₂(4) multiplier without assuming
that multiplier trivial.

The full cubic residual theorems then exclude the large symplectic and G₂
families. For G₂(2)′ and SL₅(2), their elementary nines and two-group outer
automorphism quotients give the same cubic containment. All four exclusions
are applied to the genuine C.2.7 catalogue, leaving the two linear families
and the A₅ alias. Field reductions and the final chief-factor argument remain
separate obligations of the original plane-centralizer assembly.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890; A.3.18, pp.51--53;
C.2.7, pp.145--147; I.1.3--4, pp.407--408.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction
open PerfectCentralCovering ChapterB.QuasisimpleSource
open ChapterA.Section03.OddPrime.SourceModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

private noncomputable def modelCover (d : MarkedPlane V) (J : Subgroup G)
    (j : LocalData T L d J) {S : Type*} [Group S]
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* S) :
    Cover (J ⧸ pCore 2 J) S where
  toMonoidHom := e.toMonoidHom.comp (coreToStar j.input.normalizes)
  surjective := e.surjective.comp (coreToStar_surjective j.input.normalizes)
  isPerfect := j.input.quasisimple.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact ChapterC.C27Source.coreToStar_ker_central_from_source j.input

private noncomputable def modelEquiv (d : MarkedPlane V) (J : Subgroup G)
    (j : LocalData T L d J) {S : Type*} [Group S]
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* S)
    (hk : IsPGroup 2 (modelCover d J j e).toMonoidHom.ker) :
    (J ⧸ pCore 2 J) ≃* S := by
  let c := modelCover d J j e
  apply MulEquiv.ofBijective c.toMonoidHom
  refine ⟨c.toMonoidHom.ker_eq_bot_iff.mp ?_,c.surjective⟩
  exact bot_unique ((show c.toMonoidHom.ker ≤ pCore 2 (J ⧸ pCore 2 J) from
    le_sSup ⟨inferInstance,hk⟩).trans_eq (pCore_quotient_pCore_eq_bot 2))

private theorem center_bot_transport {S B : Type*} [Group S] [Group B] (e : B ≃* S)
    (hz : center S = ⊥) : center B = ⊥ := by
  apply bot_unique
  intro x hx
  have hh := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center S at hh
  rw [hz,mem_bot] at hh
  exact e.map_eq_one_iff.mp hh

private theorem no_outer_two (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    {S : Type*} [Group S] [Finite S] (e : (J ⧸ pCore 2 J) ≃* S)
    (hz : center S = ⊥) (hr : 2 ≤ primeRank 3 S)
    (ho : IsPGroup 2 (MulAut.Outer S)) : False := by
  apply s.no_cubic_capture d J j
  intro B _ _ hB D hD eD x hx
  let a := eD.symm.trans e
  have hzD := center_bot_transport a hz
  let q : D ⧸ center D ≃* S :=
    ((QuotientGroup.quotientMulEquivOfEq hzD).trans QuotientGroup.quotientBot).trans a
  have hrD : 2 ≤ primeRank 3 D := by rwa [primeRank_congr 3 a]
  rw [(Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    hD (by rw [hzD]; simp) hrD (hB.stronglyQuasithin 3 (by decide) (by decide))
    q (by decide) ho).1]
  exact subset_closure hx

private theorem binary_field_large (F : BinaryField) (large : 1 < F.degree) :
    2 < Nat.card F.Carrier := by
  rw [F.card_eq]
  exact (show 2^1 < 2^F.degree from pow_lt_pow_right₀ (by decide) large)

/-- The original component cannot have a large symplectic star model. -/
theorem Context.not_symplectic_star (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) (F : BinaryField) (large : 1 < F.degree)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  let c := modelCover d J j e
  have hk : IsPGroup 2 c.toMonoidHom.ker := by
    let := c.isPerfect
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
    intro p hp
    obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    have heq : p = 2 := by
      by_contra hp2
      let : Fact p.Prime := ⟨hpp⟩
      exact Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.not_dvd_card_kernel
        hp2 c.toMonoidHom c.surjective c.ker_le_center hpd
    norm_num [heq]
  let eq := modelEquiv d J j e hk
  apply s.no_cubic_capture d J j
  intro B _ _ hB D hD eD x hx
  let a := eD.symm.trans eq
  have hz := center_bot_transport a
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
  let q : D ⧸ center D ≃* Matrix.symplecticGroup (Fin 2) F.Carrier :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans a
  rw [(SymplecticCubicResidual.component_eq_primeClosure_and_residual
    hB hD (by rw [hz]; exact IsPGroup.of_subsingleton 2 _) (binary_field_large F large) q).1]
  exact subset_closure hx

/-- The original component cannot have a large G₂ star model, including field four. -/
theorem Context.not_g2_star (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) (F : BinaryField) (large : 1 < F.degree)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* Atlas.G2.Model F.Carrier) : False := by
  have hF := binary_field_large F large
  let : Fact (2 < Nat.card F.Carrier) := ⟨hF⟩
  let c := modelCover d J j e
  have hp : IsPGroup 2 (universalProjection (Atlas.G2.Model F.Carrier)).ker := by
    have hfour : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (show 2^2 ≤ 2^F.degree from pow_le_pow_right₀ (by decide) (by omega))
    rcases eq_or_lt_of_le hfour with h | h
    · exact Atlas.G2.FiniteCover.MultiplierFourBound.universalKernel_isPGroup_of_card_four h.symm
    · exact Atlas.G2.MultiplierOrdinary.Nondefining.universalKernel_isPGroup h
  have hk := c.ker_isPGroup_of_universal
    (universalCover (Atlas.G2.Model F.Carrier)) (universalCover_isUniversal) hp
  let eq := modelEquiv d J j e hk
  apply s.no_cubic_capture d J j
  intro B _ _ hB D hD eD x hx
  let a := eD.symm.trans eq
  have hz := center_bot_transport a (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hF)
  let q : D ⧸ center D ≃* Atlas.G2.Model F.Carrier :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans a
  rw [(G2CubicResidual.component_eq_primeClosure_and_residual
    hB hD (by rw [hz]; exact IsPGroup.of_subsingleton 2 _) hF q).1]
  exact subset_closure hx

/-- The actual binary derived G₂ model is excluded through its central cover. -/
theorem Context.not_g2DerivedTwo_star (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup
    (modelCover d J j e)
  apply no_outer_two s d J j (modelEquiv d J j e hk)
    Atlas.G2.BinaryLocalResidual.center_eq_bot Atlas.G2.EvenThreeRank.two_le_primeRank_derived
  rcases (Nat.dvd_prime Nat.prime_two).mp Atlas.G2.BinaryLocalResidual.outer_card_dvd_two with h | h
  · exact IsPGroup.of_card (n := 0) (by simpa using h)
  · exact IsPGroup.of_card (n := 1) (by simpa using h)

/-- The actual degree-five binary linear model is excluded through its universal cover. -/
theorem Context.not_linearFive_star (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* SL(5,ZMod 2)) : False := by
  let a := e.trans Theory.SpecificGroups.PSL5Two.UniversalCover.projectiveEquivSL.symm
  let c := modelCover d J j a
  let := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple (ZMod 2)
  have hp : IsPGroup 2 (universalProjection PSL(5,ZMod 2)).ker := by
    rw [Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot]
    exact IsPGroup.of_subsingleton 2 _
  have hk := c.ker_isPGroup_of_universal
    (universalCover PSL(5,ZMod 2)) (universalCover_isUniversal) hp
  let eq := (modelEquiv d J j a hk).trans Theory.SpecificGroups.PSL5Two.UniversalCover.projectiveEquivSL
  exact no_outer_two s d J j eq (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide))
    BinaryLinear.SmallCubicRank.five (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup (Or.inr rfl))

/-- The original C.2.7 component now has only the two linear families or A₅. -/
inductive LinearStarModel (B : Type*) [Group B] : Prop
  | linearTwo (F : BinaryField) (equiv : B ≃* SL(2,F.Carrier))
  | linearThree (F : BinaryField) (equiv : B ≃* SL(3,F.Carrier))
  | alternatingFive (equiv : B ≃* alternatingGroup (Fin 5))

/-- Apply the four cubic exclusions to the same plane, component and radical. -/
theorem Context.linear_star_model (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    LinearStarModel (starImage J ((L ⊔ T).pCoreIn 2) J) := by
  cases s.inspected_star_model d J j with
  | linearTwo F e => exact .linearTwo F e
  | linearThree F e => exact .linearThree F e
  | alternatingFive e => exact .alternatingFive e
  | symplectic F hF e => exact (s.not_symplectic_star d J j F hF e).elim
  | g2 F hF e => exact (s.not_g2_star d J j F hF e).elim
  | g2DerivedTwo e => exact (s.not_g2DerivedTwo_star d J j e).elim
  | linearFiveTwo e => exact (s.not_linearFive_star d J j e).elim

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
