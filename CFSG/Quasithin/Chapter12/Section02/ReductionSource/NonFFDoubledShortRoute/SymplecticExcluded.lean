module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SymplecticPlacement
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SymplecticPlacement
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.MatchingParabolics
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledAssembly

/-!
# Excluding the nonbinary doubled symplectic row

The full orbit has rank 8n, so the component containing the original odd fixed
residual must be a Bender or rank-two component. The residual action excludes
Bender components and all rank-two rows except PSU5(4) and general Ree groups.
The original quotient map sends a nontrivial two-core image into a parabolic:
Sp4(2^n), n > 1, cannot occur in either surviving parabolic. Thus every abelian
odd actor centralizing the whole orbit has its normalizer in N(L).

The original Hall/Cartan actor supplied by 7.3.4 contradicts that bound,
completing the nonbinary row of 7.3.5. The final application removes precisely
this premise from the doubled assembly; the binary, nonbinary linear, A6,
and A7 inputs remain obligations of the same short-route owner.
Source: Aschbacher--Smith 4.4.3, 4.4.10--12, 7.3.4--5 and 12.2.2,
refs/quasithin.pdf. All maps retain the full two-core and covering center.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
open Theory.SpecificGroups.SymplecticFour

private theorem symplectic_card_not_dvd_unitary_five_parabolic
    (F : BinaryField) (hn : 1 < F.degree) (plane : Bool) :
    ¬ Nat.card (Sp F.Carrier) ∣
      2 ^ 20 * (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13) := by
  rw [card_sp,F.card_eq]
  intro hd
  have hle := Nat.le_of_dvd (by cases plane <;> norm_num :
    0 < 2 ^ 20 * (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13)) hd
  have hf : F.degree ≤ 3 := by
    by_contra! hf
    have hq : 16 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf
    have hl := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
    cases plane <;> norm_num at hl hle <;> omega
  interval_cases he : F.degree <;> cases plane <;> norm_num [he] at hd

private theorem no_symplectic_unitary_five_local
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (π : A →* S) (hπ : Function.Surjective π)
    (E : BinaryField) (hE : 1 < E.degree) (e : S ≃* Sp E.Carrier)
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
  apply symplectic_card_not_dvd_unitary_five_parabolic E hE b
  cases b
  · simpa only [Bool.false_eq_true, ↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J hcard hconj hJ] using hd
  · simpa only [↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J hcard hconj hJ] using hd

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal abelian odd normalizer in the nonbinary doubled symplectic
row lies in N(L). Both reciprocal pushing up and the whole-orbit outside
component are excluded from the original source hypotheses. -/
theorem sourceOrbit_symplectic_oddNormalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨K,hK,_,houtK,_,hqt,_,_,_⟩ :=
    D.sourceOrbit_symplectic_oddNormalizer_component h hd hmany hnon F hn hmodel A hne hAC ho hout
  obtain ⟨_,hw,hr,_,hrank⟩ := D.sourceOrbit_symplectic_oddNormalizer_placement
    h hd hmany hnon F hn hmodel A hne hAC ho hout K hK houtK
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
  obtain ⟨eL⟩ := D.doubled_symplectic_simple_quotient h F hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (Sp F.Carrier) := eL.symm.isSimpleGroup
  let : Group.IsPerfect (Sp F.Carrier) := Group.IsPerfect.ofSurjective
    (f := eL.toMonoidHom) eL.surjective
  let π : R →* Sp F.Carrier := eL.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))))
  have hπ : Function.Surjective π := eL.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (b.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hS := Group.IsPerfect.not_isSolvable (Sp F.Carrier)
  have hexp := doubledSymplectic_not_two_exponent F.card_eq
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
    exact no_symplectic_unitary_five_local hS π hπ F hn (MulEquiv.refl _)
      (HermitianForm.IdentityGram.identityGram B) hcard hconj rfl _ hp hpne r hpar
  · let r := residualQuotientMap hr e
    let := residualQuotientMap_kernel_solvable hr e
    obtain ⟨hp,hpne,hpar⟩ := residualQuotientMap_two_local hr hcore
      D.sourceOrbit_weakClosure_setup.nontrivial hcomm e
    have hthree : 3 ∣ Nat.card (Sp F.Carrier) := by
      by_contra hh
      have hz : primeRank 3 (Sp F.Carrier) = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
      have hl := OddFieldActors.cubic_rank (F := F.Carrier)
      omega
    exact no_ree_local_of_three_dvd hS hexp hthree π hπ hm _ hp hpne r hpar

/-- The original Hall actor contradicts the completed odd-normalizer bound.
This closes the nonbinary paired symplectic row on the unchanged source orbit,
with its original Cartan data and both seed orientations retained. -/
theorem sourceOrbit_symplectic_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))) : False := by
  obtain ⟨_,_,_,p,A,hp,hodd,hne,he,_,_,hAC,_,hout,_⟩ :=
    D.sourceOrbit_symplectic_hall_escaping_component h hd hmany hnon F hn hmodel
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact hodd.pow
  exact hout (D.sourceOrbit_symplectic_oddNormalizer_le h hd hmany hnon F hn hmodel A hne hAC ho)

/-- The nonbinary symplectic premise of the original doubled assembly is now
proved. The four remaining literal bounds stay explicit for final discharge
by this source-family owner. -/
theorem sourceOrbit_false_of_remaining_markedDoubled_bounds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hlinear : ∀ F : BinaryField, 1 < F.degree →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
        (linearNatural F 3)) → DoubledLinearBounds D.sourceOrbit T F.degree)
    (hbinary : ∀ F : BinaryField, F.degree = 1 →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
        (linearNatural F 3)) → DoubledBinaryGeometry D.sourceOrbit)
    (hsix : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)) → DoubledSymplecticBounds D.sourceOrbit T 1)
    (hseven : ∀ σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2),
      Function.Injective σ →
      Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ) →
      DoubledSevenBounds D.sourceOrbit T) : False :=
  D.sourceOrbit_false_of_markedDoubled_bounds h hd hnon hlinear hbinary
    (fun F hn hm => (D.sourceOrbit_symplectic_excluded h hd hmany hnon F hn hm).elim)
    hsix hseven

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
