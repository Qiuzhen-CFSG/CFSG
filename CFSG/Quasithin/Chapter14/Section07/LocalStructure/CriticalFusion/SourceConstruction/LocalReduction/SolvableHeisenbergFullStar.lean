module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergPoint
public import Theory.GroupTheory.HeisenbergCentralizer

public import Theory.GroupTheory.PResidual.NormalThreeLift
public import Theory.GroupTheory.DetectedNormalCubic
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.SylowThreeCubic
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# The proper local Heisenberg residual in the full point quotient

The selected local residual embeds normally in the original full point
quotient, with the same marked central cubic L₁*. The ambient three-rank
bound and vanishing three-prime core make its centralizer a cyclic
three-group. Lifting that group and using its actual action on L/O₂(L)
then makes its order exactly three; the centralizer is precisely L₁*.

The applications retain the original group, flag, quotient kernels and
potentially proper local witness. They do not identify the local residual
with O²(H). Source: Aschbacher–Smith 14.7.15(3) and 14.7.27–29,
printed pp.1047,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
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

theorem local_solvable_heisenberg_full_star
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
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
  let := hs
  have hIs : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective (inclusion_injective hIH)
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
    pPrimeCore_eq_bot_of_fitting_isPGroup inferInstance 3
      (local_fitting_isThreeGroup h hab structural previous faithful F.H
        (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)))
  exact ⟨hRn,⟨e⟩,le_sSup ⟨hRn,hR3⟩,hRres,hcenter,
    heisenberg_centralizer_isCyclic_threeGroup R e (fullStar_three_rank h) hcore⟩

/-- Apply the full-star centralizer argument to the actual proper local
provided by the original solvable hypothesis. -/
theorem original_solvable_full_star_heisenberg
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      let R := star F ((pResidual 2 I).map I.subtype)
      R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
        R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
        star F (F.Li L 1) = (center R).map R.subtype ∧
        IsPGroup 3 (centralizer (R : Set (HStar F.H))) ∧
        IsCyclic (centralizer (R : Set (HStar F.H))) := by
  obtain ⟨I,hIH,hI,_,_,hn,he,_⟩ := original_solvable_proper_heisenberg_normal
    d h hab structural previous faithful earlier hs
  exact ⟨I,hIH,hI,local_solvable_heisenberg_full_star
    h hab structural previous faithful hs I hI hn he⟩

private theorem full_quotient_aut_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  rw [Nat.card_congr (MulAut.congr (e.trans Matrix.PSL3Two.equiv)).toEquiv]
  exact Matrix.PSL3Two.Automorphisms.card_aut

private theorem full_quotient_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  apply bot_unique
  intro x hx
  have hz : e x ∈ center Matrix.PSL3Two.SL := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  rw [Matrix.PSL3Two.center_eq_bot] at hz
  exact e.injective (hz.trans e.map_one.symm)

private theorem cyclic_three_lift_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (E : Subgroup G) (hAE : F.Li L 1 ≤ E)
    (hEA : E ≤ normalizer (F.Li L 1 : Set G))
    (hEM : E ≤ normalizer (L : Set G))
    (hcyc : IsCyclic (E ⧸ pCore 2 E))
    (h3 : IsPGroup 3 (E ⧸ pCore 2 E)) :
    Nat.card (E ⧸ pCore 2 E) = 3 := by
  let S : Sylow 3 E := default
  let q := QuotientGroup.mk' (pCore 2 E)
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := E)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let : IsCyclic (E ⧸ pCore 2 E) := hcyc
  let : IsCyclic S := isCyclic_of_injective (q.comp (S : Subgroup E).subtype)
    (injective_comp_subtype_of_coprime_ker q hk _ S.isPGroup')
  let B := (S : Subgroup E).map E.subtype
  let : IsCyclic B := isCyclic_of_surjective (E.subtype.subgroupMap (S : Subgroup E))
    (E.subtype.subgroupMap_surjective _)
  have hB : IsPGroup 3 B := S.isPGroup'.map E.subtype
  obtain ⟨A₀,hA₀⟩ := S.exists_map_subtype_eq_inf_of_normalizes hAE hEA
  have hAc : Nat.card (B ⊓ F.Li L 1 : Subgroup G) = 3 := by
    rw [←hA₀,card_map_of_injective (F.Li L 1).subtype_injective]
    exact card_sylow_three_of_two_group_index_three (pCore 2 (F.Li L 1)) pCore_isPGroup
      (pointResidual_core_quotient_card h structural) A₀
  let A := (B ⊓ F.Li L 1).subgroupOf B
  have hAc' : Nat.card A = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).trans hAc
  have hBM : B ≤ normalizer (L : Set G) := (map_subtype_le _).trans hEM
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hBM)
  have hi : Function.Injective (f.comp A.subtype) := by
    have hd : Disjoint B (L.pCoreIn 2) :=
      hB.disjoint_of_coprime (isPGroup_pCoreIn 2 L) (by decide)
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hm : ((x : B) : G) ∈ pCoreActionKernelIn 2 L (normalizer (L : Set G)) ⊓ L := by
      exact ⟨⟨hBM x.val.property,inclusion hBM x.val,hx,rfl⟩,
        (inf_le_right.trans ((F.Li_le L 1).trans inf_le_left)) x.property⟩
    rw [pCoreActionKernelIn_inf_eq_core L (normalizer (L : Set G)) L.le_normalizer
      (full_quotient_center h)] at hm
    exact Subtype.ext (Subtype.ext (hd.le_bot ⟨x.val.property,hm⟩))
  have hr : Nat.card f.range ≤ 3 := by
    obtain ⟨P,hP⟩ := (hB.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
    have hc : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity,full_quotient_aut_card h]
      decide +kernel
    exact (Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective hP)).trans_eq hc
  have heq : (⊤ : Subgroup B) = A :=
    cyclic_eq_detected_cubic hB A hAc' f hi hr ⊤ le_top
  have hcB : Nat.card B = 3 := by
    rw [←card_top (G := B),heq]
    exact hAc'
  have hStop : (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 E)) :
      Subgroup (E ⧸ pCore 2 E)) = ⊤ := by
    apply top_unique
    exact (h3.to_subgroup ⊤).le_sylow_of_normal _
  let e := Sylow.equivOfSurjectiveCoprime q (QuotientGroup.mk'_surjective _) hk S
    (S.mapSurjective (QuotientGroup.mk'_surjective _))
  calc
    Nat.card (E ⧸ pCore 2 E) = Nat.card S := by
      rw [Nat.card_congr e.toEquiv,hStop,card_top]
    _ = Nat.card B := (card_map_of_injective E.subtype_injective).symm
    _ = 3 := hcB

/-- Every normal cyclic three-subgroup containing the marked point cubic
is precisely that cubic, using the original quotient action on L/O₂(L). -/
theorem full_star_normal_cyclic_three_eq_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (X : Subgroup (HStar F.H)) [X.Normal]
    (hX : IsPGroup 3 X) (hcyc : IsCyclic X)
    (hZX : star F (F.Li L 1) ≤ X) :
    X = star F (F.Li L 1) := by
  let q := starMap F
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 F.H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨W,hWn,hWp,_,hWm,_,⟨eW⟩⟩ :=
    exists_normal_three_residual_lift q hq hk X hX
  let : W.Normal := hWn
  let A := (F.Li L 1).subgroupOf F.H
  have hAH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hAp : IsPPerfect 2 A :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hAW : A ≤ W := isPPerfect_le_of_map_le_of_kernel_normalizes q A W hAp hk
    le_normalizer_of_normal (by rw [hWm]; exact hZX)
  have hEpoint : F.Li L 1 ≤ W.map F.H.subtype := by
    have hh := map_mono (f := F.H.subtype) hAW
    rwa [map_subgroupOf_eq_of_le hAH] at hh
  let := hn
  have hEA : W.map F.H.subtype ≤ normalizer (F.Li L 1 : Set G) := by
    rintro _ ⟨w,hw,rfl⟩
    exact (normal_subgroupOf_iff_le_normalizer hAH).mp hn w.property
  have hTW : (T : Subgroup G) ≤ normalizer (W.map F.H.subtype : Set G) := by
    have hh := W.le_normalizer_map F.H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact (F.invariant 1).trans hh
  let := hcyc
  have hWcyc : IsCyclic (W ⧸ pCore 2 W) := eW.isCyclic.mpr hcyc
  have hW3 : IsPGroup 3 (W ⧸ pCore 2 W) := hX.of_equiv eW.symm
  have hWM : W.map F.H.subtype ≤ normalizer (L : Set G) :=
    local_cyclic_three_lift_containment h hab structural F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) W hWp hTW hAW hWcyc hW3
  let eE := (equivMapOfInjective W F.H.subtype F.H.subtype_injective).symm
  let eQ := (QuotientGroup.congr _ _ eE (pCore_map_iso 2 eE)).trans eW
  have hc : Nat.card X = 3 := by
    rw [←Nat.card_congr eQ.toEquiv]
    exact cyclic_three_lift_card h structural (W.map F.H.subtype) hEpoint hEA hWM
      (eQ.isCyclic.mpr hcyc) (hX.of_equiv eQ.symm)
  have hcZ : Nat.card (star F (F.Li L 1)) = 3 := pointResidual_star_card_of_normal h structural hn
  exact (eq_of_le_of_card_ge hZX (by rw [hc,hcZ])).symm

/-- In the full original quotient, the local Heisenberg residual has precisely
its marked central cubic as centralizer. -/
theorem local_solvable_heisenberg_full_star_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    let R := star F ((pResidual 2 I).map I.subtype)
    R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
      R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
      star F (F.Li L 1) = (center R).map R.subtype ∧
      centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) := by
  obtain ⟨hRn,heR,hR3,hRres,hZ,hC3,hCc⟩ :=
    local_solvable_heisenberg_full_star h hab structural previous faithful hs I hI hn he
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hZC : star F (F.Li L 1) ≤ centralizer (R : Set (HStar F.H)) := by
    rw [hZ,map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  exact ⟨hRn,heR,hR3,hRres,hZ,full_star_normal_cyclic_three_eq_point
    h hab structural previous (original_solvable_point_normal h hab structural previous faithful hs)
    (centralizer (R : Set (HStar F.H))) hC3 hCc hZC⟩

/-- The proper local selected under original solvability has a normal
Heisenberg image in the full quotient whose centralizer is exactly L₁*. -/
theorem original_solvable_full_star_centralizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      let R := star F ((pResidual 2 I).map I.subtype)
      R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
        R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
        star F (F.Li L 1) = (center R).map R.subtype ∧
        centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) := by
  obtain ⟨I,hIH,hI,_,_,hn,he,_⟩ := original_solvable_proper_heisenberg_normal
    d h hab structural previous faithful earlier hs
  exact ⟨I,hIH,hI,local_solvable_heisenberg_full_star_centralizer
    h hab structural previous faithful hs I hI hn he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

