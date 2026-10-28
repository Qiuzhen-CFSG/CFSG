module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearPlacement
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearPlacement
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.MatchingParabolics

/-!
# Odd-normalizer control for the original nonbinary linear-three pair

Reciprocal uniqueness and the actual inner action place the whole orbit in
an outside component with central-quotient rank at least twelve. Original
residual local structure leaves only PSU5(4) or Ree. Literal parabolic orders
exclude PSL3(2^n), retaining its scalar center, and the cubic prime excludes
Ree. Thus every abelian odd actor centralizing the source orbit has its
normalizer in N(L).
Source: Aschbacher--Smith 4.4.10--12 and 7.3.4, printed pp.621--622,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
open scoped MatrixGroups

private theorem linear_three_card_not_dvd_unitary_five_parabolic
    (F : BinaryField) (hn : 1 < F.degree) (plane : Bool) :
    ¬ Nat.card PSL(3,F.Carrier) ∣
      2 ^ 20 * (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13) := by
  rw [Matrix.PSL3.LinearThree.card_projective,F.card_eq]
  intro hd
  have hle := Nat.le_of_dvd (by cases plane <;> norm_num :
    0 < 2 ^ 20 * (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13)) hd
  have hf : F.degree ≤ 4 := by
    by_contra! hf
    have hq : 32 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf
    have hl := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    have hden : Nat.gcd 3 (2 ^ F.degree - 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
    have hb := (Nat.div_le_div_right hl (c := 3)).trans
      (Nat.div_le_div_left hden (Nat.gcd_pos_of_pos_left _ (by decide)))
    cases plane <;> norm_num at hb hle <;> omega
  interval_cases he : F.degree <;> cases plane <;> norm_num [he] at hd

private theorem no_linear_three_unitary_five_local
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (π : A →* S) (hπ : Function.Surjective π)
    (E : BinaryField) (hE : 1 < E.degree) (e : S ≃* PSL(3,E.Carrier))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ProjectiveSpecialUnitaryMatrixGroup J) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Theory.SpecificGroups.UnitaryFive.finite_projective J
  obtain ⟨W,hn,hi,_,hNW⟩ :=
    Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
      J hJ (normalizer (P : Set _)) ⟨P,hne,hp,rfl⟩
  obtain ⟨b,g,hg⟩ := Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.transitive
    J hcard hconj hJ W hn hi
  have he : Theory.SpecificGroups.UnitaryFive.parabolic J W =
      (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
        else Theory.SpecificGroups.UnitaryFive.lineParabolic J).map
          (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)).toMonoidHom := by
    rw [hg, Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hNW
  let j := (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).toMonoidHom.comp r
  have hj : j.range ≤ (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
      else Theory.SpecificGroups.UnitaryFive.lineParabolic J) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hNW (hr ⟨x,rfl⟩)
    change (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹ * r x *
      ((Theory.SpecificGroups.UnitaryFive.project J g)⁻¹)⁻¹ ∈ _
    rw [← he]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show k.ker ≤ r.ker from fun x hx => by
      have he : j x = 1 := congrArg Subtype.val hx
      exact (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).injective
        (he.trans (map_one _).symm))) (inclusion_injective _)
  have hd := SimpleSection.card_dvd_of_solvable_representation hS π hπ k
  rw [Nat.card_congr e.toEquiv] at hd
  apply linear_three_card_not_dvd_unitary_five_parabolic E hE b
  cases b
  · simpa only [Bool.false_eq_true, ↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J hcard hconj hJ] using hd
  · simpa only [↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J hcard hconj hJ] using hd

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal abelian odd normalizer in the nonbinary doubled linear-three
row lies in N(L). Both reciprocal pushing up and the whole-orbit outside
component are excluded from the original source hypotheses. -/
theorem sourceOrbit_linear_oddNormalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨K,hK,_,houtK,_,hqt,_,_,_⟩ :=
    D.sourceOrbit_linear_oddNormalizer_component h hd F hn hmodel A hne hAC ho hout
  obtain ⟨_,hw,hr,_,hrank⟩ := D.sourceOrbit_linear_oddNormalizer_placement
    h hd F hn hmodel A hne hAC ho hout K hK houtK
  let R := oddActorResidual L A
  let N := normalizer (A : Set G)
  let J := K.map N.subtype
  let z := centerQuotientCongr (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let := hK.2
  have hkg := ((oddNormalizer_properQTK h.simpleQTKE A hne).2.2).subgroup K
  have hb := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple hqt hkg
  have hrJ : 12 ≤ primeRank 2 (J ⧸ center J) := by
    rw [primeRank_equiv 2 z]
    omega
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  obtain ⟨_,hcomm,hcore,_⟩ := D.doubledOrbit_oddActorResidual_cover h A hA ho
  rw [←D.sourceOrbit_eq] at hcomm hcore
  let : Group.IsPerfect R := oddActorResidual_isPerfect L A
  rcases bender_or_rankTwo_of_rank_twelve (hb.of_mulEquiv z) hrJ with hbender | ⟨n,hrankTwo⟩
  · exact no_bender_of_residual_module J R D.sourceOrbit hr hcore
      D.sourceOrbit_weakClosure_setup.nontrivial hcomm hbender
  obtain ⟨b,_⟩ := chosen_oddActorResidual_quotient h.toHypothesis1221 D A
    (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T)))
  obtain ⟨eL⟩ := D.linear_central_quotient h F hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (PSL(3,F.Carrier)) := eL.symm.isSimpleGroup
  let : Group.IsPerfect (PSL(3,F.Carrier)) := Group.IsPerfect.ofSurjective
    (f := eL.toMonoidHom) eL.surjective
  let π : R →* PSL(3,F.Carrier) := eL.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))))
  have hπ : Function.Surjective π := eL.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (b.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hS := Group.IsPerfect.not_isSolvable (PSL(3,F.Carrier))
  have hexp := Matrix.PSL3.LinearThree.not_two_exponent (MulEquiv.refl _) F.card_eq
  have hremaining := unitary_five_or_ree_of_residual_module R J D.sourceOrbit
    hr hcore D.sourceOrbit_weakClosure_setup.nontrivial hcomm hS hexp π hπ hrJ hrankTwo
  rcases hremaining with hunitary | ⟨m,hm,⟨e⟩⟩
  · obtain ⟨E,_,_,B,hcard,hconj,⟨e⟩⟩ := hunitary
    let := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
    obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four B hcard hconj
    let t := e.trans a
    let r := residualQuotientMap hr t
    let := residualQuotientMap_kernel_solvable hr t
    obtain ⟨hp,hpne,hpar⟩ := residualQuotientMap_two_local hr hcore
      D.sourceOrbit_weakClosure_setup.nontrivial hcomm t
    exact no_linear_three_unitary_five_local hS π hπ F hn (MulEquiv.refl _)
      (HermitianForm.IdentityGram.identityGram B) hcard hconj rfl _ hp hpne r hpar
  · let r := residualQuotientMap hr e
    let := residualQuotientMap_kernel_solvable hr e
    obtain ⟨hp,hpne,hpar⟩ := residualQuotientMap_two_local hr hcore
      D.sourceOrbit_weakClosure_setup.nontrivial hcomm e
    have hthree : 3 ∣ Nat.card PSL(3,F.Carrier) :=
      (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
        (F := F.Carrier) (show (0 : Fin 3) ≠ 1 from by decide)).trans
          (commutator PSL(3,F.Carrier)).card_subgroup_dvd_card
    exact no_ree_local_of_three_dvd hS hexp hthree π hπ hm _ hp hpne r hpar

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
