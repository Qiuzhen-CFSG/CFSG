module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreePrimeExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergExclusion
public import Theory.SpecificGroups.GL2.ThreeSolvable

/-!
# Excluding every original solvable local

The minimal solvable local supplies a Heisenberg residual normal in the
full point normalizer. Its characteristic point cubic is normal there.
Source 14.7.7 now gives the missing three-prime-core vanishing without
assuming that the full point normalizer is solvable. Consequently the
Heisenberg image is self-centralizing, and its outer action in GL₂(3)
forces full-point solvability, contradicting the previously proved
full-point exclusion. The final application gives the literal 14.7.29
containment for every solvable point-parabolic overgroup.

Source: Aschbacher–Smith, 14.7.7, 14.7.14 and 14.7.29, printed
pp.1045,1047–1055, refs/quasithin.pdf. This does not yet prove the
component and module classification through 14.7.52.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem fullStar_image
    (I : Subgroup G) (hIH : I ≤ F.H)
    (hn : (((pResidual 2 I).map I.subtype).subgroupOf F.H).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    (star F ((pResidual 2 I).map I.subtype)).Normal ∧
      Nonempty (star F ((pResidual 2 I).map I.subtype) ≃* HeisenbergPrime 3) := by
  let R := (pResidual 2 I).map I.subtype
  let A := R.subgroupOf F.H
  let := hn
  let eR := (pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective
  let eA : A ≃* pResidual 2 I :=
    (subgroupOfEquivOfLe ((map_subtype_le _).trans hIH)).trans eR.symm
  let eLocal := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  let e := (coreQuotientEquivImage 2 A).symm.trans
    ((QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans (eLocal.trans he.some))
  exact ⟨hn.map (starMap F) (QuotientGroup.mk'_surjective _),⟨e⟩⟩

private theorem fullStar_three_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    primeRank 3 (HStar F.H) ≤ 2 := by
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 F.H) pCore_isPGroup).trans
    ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 3 (by decide) (by decide))

theorem local_solvable_heisenberg_full_star_of_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hIs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    let R := star F ((pResidual 2 I).map I.subtype)
    R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
      R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
      star F (F.Li L 1) = (center R).map R.subtype ∧
      IsPGroup 3 (centralizer (R : Set (HStar F.H))) ∧
      IsCyclic (centralizer (R : Set (HStar F.H))) := by
  let R₀ := (pResidual 2 I).map I.subtype
  let R := star F R₀
  have hIH : I ≤ F.H := hI.2.1
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  obtain ⟨hRn,⟨e⟩⟩ := fullStar_image I hIH
    (local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
      I hI hIs hn he F.H hH hIH) he
  let : R.Normal := hRn
  have hR3 : IsPGroup 3 R :=
    (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).of_equiv e.symm
  have hRres : R ≤ pResidual 2 (HStar F.H) := by
    have hh : R₀ ≤ K F := embedded_pResidual_mono 2 hIH
    have hh' : R₀.subgroupOf F.H ≤ pResidual 2 F.H := by
      rw [←residual_subgroupOf F]
      exact subgroupOf_mono F.H hh
    exact (map_mono hh').trans (map_pResidual_le 2 (starMap F))
  have hnH := local_solvable_heisenberg_point_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn he F.H hH hIH
  let Z := star F (F.Li L 1)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hnH
  let : Z.Normal := hnH.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZR₀ : F.Li L 1 ≤ R₀ := by
    have hh := embedded_pResidual_mono 2 (F.Li_one_le_of_mem_Hz hI)
    rw [(pResidual_eq_top_iff 2 (F.Li L 1)).mpr (isPPerfect_embedded_pResidual 2 _),
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hZR : Z ≤ R := map_mono (subgroupOf_mono F.H hZR₀)
  have hZcard : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hnH
  have hZRc : Nat.card (Z.subgroupOf R) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv).trans hZcard
  have hcenter : Z = (center R).map R.subtype := by
    have hh : Z.subgroupOf R = center R := eq_of_le_of_card_ge
      (hR3.normal_le_center_of_card_dvd_prime _ (by rw [hZRc]))
      (by rw [hZRc,Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center])
    simpa only [map_subgroupOf_eq_of_le hZR] using congrArg (map R.subtype) hh
  have hcore : pPrimeCore 3 (HStar F.H) = ⊥ :=
    local_threePrimeCore_eq_bot_of_point_normal h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) inferInstance
  exact ⟨hRn,⟨e⟩,le_sSup ⟨hRn,hR3⟩,hRres,hcenter,
    heisenberg_centralizer_isCyclic_threeGroup R e (fullStar_three_rank h) hcore⟩

/-- The original proper-local Heisenberg centralizer argument, using only
solvability of that local subgroup, not of the full point normalizer. -/
theorem local_solvable_heisenberg_full_star_centralizer_of_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hIs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    let R := star F ((pResidual 2 I).map I.subtype)
    R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
      R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
      star F (F.Li L 1) = (center R).map R.subtype ∧
      centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) := by
  obtain ⟨hRn,heR,hR3,hRres,hZ,hC3,hCc⟩ :=
    local_solvable_heisenberg_full_star_of_local h hab structural previous faithful I hI hIs hn he
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hZC : star F (F.Li L 1) ≤ centralizer (R : Set (HStar F.H)) := by
    rw [hZ,map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hb
    have hc := F.card 1 (by decide)
    rw [hb,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hnH := local_solvable_heisenberg_point_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn he F.H hH hI.2.1
  exact ⟨hRn,heR,hR3,hRres,hZ,full_star_normal_cyclic_three_eq_point
    h hab structural previous hnH (centralizer (R : Set (HStar F.H))) hC3 hCc hZC⟩

/-- Source 14.7.14: the normal Heisenberg residual of a solvable local
would make the full point normalizer solvable through its GL₂(3) outer action. -/
theorem local_solvable_heisenberg_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hIs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) : False := by
  obtain ⟨hRn,⟨e⟩,_,_,hZ,hC⟩ := local_solvable_heisenberg_full_star_centralizer_of_local
    h hab structural previous faithful I hI hIs hn he
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hc : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  have hR3 : IsPGroup 3 R :=
    (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).of_equiv e.symm
  let : Group.IsNilpotent R := hR3.isNilpotent
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    Matrix.GeneralLinearGroup.three_isSolvable
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp
    (MulAut.conjNormal : HStar F.H →* MulAut R)
  let : Group.IsSolvable (HStar F.H) := Group.isSolvable_of_ker_le_range R.subtype f (by
    rw [range_subtype,heisenberg_outerAction_ker R e hc])
  let : Group.IsNilpotent (pCore 2 F.H) := pCore_isPGroup.isNilpotent
  have hs : Group.IsSolvable F.H :=
    Group.isSolvable_of_ker_le_range (pCore 2 F.H).subtype (starMap F) (by
      rw [range_subtype]
      change (QuotientGroup.mk' (pCore 2 F.H)).ker ≤ pCore 2 F.H
      rw [QuotientGroup.ker_mk'])
  exact original_point_not_solvable d h hab structural previous faithful earlier hs

/-- Source 14.7.29: every member of the original H_z is nonsolvable.
The selected minimal Heisenberg residual is lifted to the full point
normalizer using 14.7.7, with no full-point solvability assumption. -/
theorem local_not_solvable
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ Group.IsSolvable J := by
  intro hs
  obtain ⟨I,_,hI,hIs,_,hn,_,_,⟨e⟩,_⟩ :=
    local_solvable_minimal_heisenberg_residual h hab structural previous faithful J hJ hs
  let eLocal := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  exact local_solvable_heisenberg_impossible d h hab structural previous faithful earlier
    I hI hIs hn ⟨eLocal.symm.trans e⟩

/-- Source 14.7.29 in its literal overgroup form: every solvable subgroup
of the point normalizer containing the point parabolic lies in N_G(L). -/
theorem solvable_point_overgroup_le_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hIH : I ≤ F.H)
    (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hs : Group.IsSolvable I) : I ≤ normalizer (L : Set G) := by
  by_contra hout
  have hI : I ∈ F.Hz L (normalizer (L : Set G)) := by
    refine ⟨⟨?_,fun _ hx => hBI (hx.elim mem_sup_left mem_sup_right)⟩,hIH,hout⟩
    have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hp : F.Vi 1 ≤ I.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hc))
        ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hBI))) hIH
    intro he
    have hb := le_bot_iff.mp (he ▸ hp)
    simp [hb] at hc
  exact local_not_solvable d h hab structural previous faithful earlier I hI hs

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
