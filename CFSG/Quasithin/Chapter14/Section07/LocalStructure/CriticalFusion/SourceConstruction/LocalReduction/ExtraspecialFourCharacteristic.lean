module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourComponents
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.ThreeFreeControl
public import CFSG.Quasithin.ChapterC.Section02
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.CComponent.UniqueResidual
public import Theory.GroupTheory.CComponent.NormalQuotientActionKernel
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.GroupTheory.GeneralizedFitting.InnerMovingActor

/-!
# Component and automorphism reductions in the outside centralizer

For each original strict overgroup H ∩ C_G(x) < G₀ ≤ C_G(x) of
characteristic two, C.1.29 absorbs the prime-to-three core into H.
The preceding subnormal reduction then makes O₃′(G₀/O₂(G₀)) trivial.
Together with the proved three-core vanishing this kills the solvable
radical of the quotient, and every C-component is divisible by three.
Thus there is a unique normal component, containing the original L₁.

Its quotient by its own two-core is simple. The genuine C.2.7 hypotheses
are constructed in the original ambient group; the central comparison
kernel vanishes, identifying this quotient with the classified star image.
The literal quotient action has kernel exactly O₂(G₀), so the original
Heisenberg subgroup acts faithfully. The action image contains the inner
group, and the actual local intersection has odd index in it and retains
its marked Heisenberg residual modulo its own two-core.

If the full outside centralizer fails characteristic two, its already
proved trivial odd core supplies an ordinary component. The original
1.1.5 data gives its marked model action and escape from H. The model
exclusions in both branches, centralizer containment, TI and the eventual
14.7.52 residual alternatives are not asserted here.

Source: Aschbacher–Smith 14.7.26, printed p.1053, refs/quasithin.pdf;
C.1.29, C.2.5–7 and1.1.5 provide the earlier source inputs.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem extraspecial_H_prime_divisor
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card F.H) : r = 2 ∨ r = 3 := by
  have two_prime {A : Type u} [Group A] [Finite A] (hA : IsPGroup 2 A)
      (hdA : r ∣ Nat.card A) : r = 2 := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn] at hdA
    exact ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hdA)).resolve_left hr.ne_one
  have hcH := (pResidual 2 F.H).card_mul_index
  rw [←hcH] at hd
  rcases hr.dvd_mul.mp hd with hR | hQ
  · have hK : r ∣ Nat.card (K F) := by
      change r ∣ Nat.card ((pResidual 2 F.H).map F.H.subtype)
      rw [card_map_of_injective F.H.subtype_injective]
      exact hR
    have hcK := (pCore 2 (K F)).card_mul_index
    rw [←hcK] at hK
    rcases hr.dvd_mul.mp hK with hcore | hquot
    · exact Or.inl (two_prime (pCore_isPGroup (p := 2) (G := K F)) hcore)
    · obtain ⟨e⟩ := he
      change r ∣ Nat.card ((K F) ⧸ pCore 2 (K F)) at hquot
      rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card] at hquot
      exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
        (hr.dvd_of_dvd_pow hquot)).resolve_left hr.ne_one)
  · change r ∣ Nat.card (F.H ⧸ pResidual 2 F.H) at hQ
    exact Or.inl (two_prime (isPGroup_quotient_pResidual (G := F.H) 2) hQ)

/-- Under characteristic two, the actual strict overgroup has trivial prime-to-three core modulo its two-core. -/
theorem extraspecial_four_primeToThreeCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    pPrimeCore 3 (G₀ ⧸ pCore 2 G₀) = ⊥ := by
  let C := centralizer ({x} : Set G)
  let J := F.H ⊓ C
  let R := (F.H.pCoreIn 2).subgroupOf G₀
  let M := J.subgroupOf G₀
  obtain ⟨_,_,hsetup⟩ := extraspecial_four_overgroup_pushingUp_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG.le hGC
  have hH23 : IsPiGroup twoThreePrimes F.H := (IsPiGroup_iff _ _).mpr
    (fun p hp => extraspecial_H_prime_divisor he p.property hp)
  have hM23 : IsPiGroup twoThreePrimes M :=
    hH23.of_injective ((inclusion (show J ≤ F.H from inf_le_left)).comp
      (subgroupOfEquivOfLe hJG.le).toMonoidHom)
      ((inclusion_injective inf_le_left).comp (subgroupOfEquivOfLe hJG.le).injective)
  have hR : IsPGroup 2 R := hsetup.radical.isPGroup
  have hcore : pCore 2 G₀ ≤ R :=
    ChapterC.twoCore_le_radical R hR hsetup.radical.2
  have hRM : M.pCoreIn 2 ≤ R := by
    rw [pCoreIn_subgroupOf 2 J G₀ hJG.le]
    rw [(extraspecial_four_core_eq d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc hx hxZ hout).1]
  have hS : IsSylowIn 2 ((T : Subgroup G) ⊓ C) G₀ := IsSylowIn.restrict (H := C)
    (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
    ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG.le) hGC
  obtain ⟨P,hP⟩ := hS
  have hPM : (P : Subgroup G₀) ≤ M := by
    intro a ha
    have hh : (a : G) ∈ (T : Subgroup G) ⊓ C := hP ▸ mem_map_of_mem G₀.subtype ha
    exact ⟨F.invariant 1 hh.1,hh.2⟩
  have hNM := ChapterC.Section02Source.primeToThreeCore_le_control hsetup.sqtk
    R M hR hcore hsetup.characteristic_control
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf) hM23 hRM P hPM
  have h3 := extraspecial_four_threeCore_eq_bot d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout G₀ hJG hGC
  have hNcore : pPrimeCore 3 G₀ ≤ pCore 2 G₀ := le_twoCore_of_subnormal_two_three h3 _
    (inferInstance : (pPrimeCore 3 G₀).Normal).isSubnormal (by
      intro p hp hd
      exact (IsPiGroup_iff _ _).mp hM23 ⟨p,hp⟩ (hd.trans (card_dvd_of_le hNM)))
  let q := QuotientGroup.mk' (pCore 2 G₀)
  have hker : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G₀)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  apply le_bot_iff.mp
  have hpre := pPrimeCore_comap_eq_of_surjective_coprime 3 q
    (QuotientGroup.mk'_surjective _) hker
  have hm := map_mono (f := q) (hpre.trans_le hNcore)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _,
    show (pCore 2 G₀).map q = ⊥ from by
      rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']] at hm
  exact hm

/-- The actual characteristic-two overgroup has a unique normal C-component containing L₁, with simple two-core quotient and faithful ambient quotient action. -/
theorem extraspecial_four_characteristicTwo_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ B : Subgroup G₀, B.IsCComponent ∧ B.Normal ∧
      F.Li L 1 ≤ B.map G₀.subtype ∧
      (∀ A : Subgroup G₀, A.IsCComponent → A = B) ∧
      fittingSubgroup (G₀ ⧸ pCore 2 G₀) = ⊥ ∧
      centralizer (B.map (QuotientGroup.mk' (pCore 2 G₀)) : Set (G₀ ⧸ pCore 2 G₀)) = ⊥ ∧
      IsSimpleGroup (B ⧸ pCore 2 B) := by
  let q := QuotientGroup.mk' (pCore 2 G₀)
  have ho := extraspecial_four_primeToThreeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC
  have hfit : fittingSubgroup (G₀ ⧸ pCore 2 G₀) = ⊥ :=
    le_bot_iff.mp ((fitting_le_pPrimeCore_of_pCore_eq_bot 3 h3).trans ho.le)
  have hnsol : ¬ Group.IsSolvable G₀ := by
    intro hs
    let := hs
    have hcardQ := (fitting_eq_bot_iff_card_eq_one_of_solvable (G₀ ⧸ pCore 2 G₀)).mp hfit
    have htop : pCore 2 G₀ = ⊤ := index_eq_one.mp hcardQ
    have hcore := (extraspecial_four_strict_overgroup_geometry
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      G₀ hJG hGC).2.1
    have hGle : G₀ ≤ F.H := by
      intro a ha
      apply (pCoreIn_le 2 F.H) (hcore ?_)
      exact mem_map_of_mem G₀.subtype (show (⟨a,ha⟩ : G₀) ∈ pCore 2 G₀ by
        rw [htop]; exact mem_top _)
    exact hJG.not_ge (le_inf hGle hGC)
  let := (pCore_isPGroup (p := 2) (G := G₀)).isNilpotent
  have hdiv (B : Subgroup G₀) (hB : B.IsCComponent) : 3 ∣ Nat.card B := by
    by_contra hd
    let B₀ := B.map q
    have hB₀ : B₀.IsCComponent := hB.map_quotient _
    have hBthree : ¬ 3 ∣ Nat.card B₀ := fun hh => hd (hh.trans (card_map_dvd B q))
    have hBo : pPrimeCore 3 B₀ = ⊥ := hB₀.subnormal.pPrimeCore_eq_bot ho
    have ht : (⊤ : Subgroup B₀) ≤ pPrimeCore 3 B₀ := le_sSup ⟨inferInstance,by
      simpa only [card_top] using Nat.prime_three.coprime_iff_not_dvd.mpr hBthree⟩
    have heq : (⊤ : Subgroup B₀) = ⊥ := le_bot_iff.mp (ht.trans hBo.le)
    have hbcard : Nat.card B₀ = 1 := by
      simpa only [card_top,card_bot] using congrArg (fun A : Subgroup B₀ => Nat.card A) heq
    exact hB₀.ne_bot ((eq_bot_iff_card B₀).mpr hbcard)
  obtain ⟨B,hB⟩ := exists_isCComponent_of_not_isSolvable hnsol
  have hu (A : Subgroup G₀) (hA : A.IsCComponent) : A = B :=
    extraspecial_four_component_unique
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      G₀ hJG hGC A B hA hB (hdiv A hA) (hdiv B hB)
  have hB₀ : (B.map q).IsCComponent := hB.map_quotient _
  have hu₀ (A : Subgroup (G₀ ⧸ pCore 2 G₀)) (hA : A.IsCComponent) : A = B.map q :=
    hB.unique_map_quotient hu _ hA
  have hs : IsSimpleGroup (B ⧸ pCore 2 B) := by
    let := hB₀.isSimpleGroup_of_solvableRadical_eq_bot (radical_bot_of_fitting_bot hfit)
    exact (cComponentTwoCoreQuotientEquiv hB).isSimpleGroup
  exact ⟨B,hB,hB.normal_of_unique hu,
    extraspecial_four_component_contains_point d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ G₀ hJG.le hGC B hB (hdiv B hB),
    hu,hfit,hB₀.centralizer_bot_of_unique_of_fitting_bot hu₀ hfit,hs⟩

/-- Construct the genuine C.2.7 input and identify the original component quotient with its classified star image. -/
theorem extraspecial_four_characteristicTwo_source_model
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ E : Subgroup G, E ∈ cComponentsIn G₀ ∧ (E.subgroupOf G₀).Normal ∧
      F.Li L 1 ≤ E ∧ IsSimpleGroup (E ⧸ pCore 2 E) ∧
      RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
          (F.H ⊓ centralizer ({x} : Set G)) E ∧
      Nonempty ((E ⧸ pCore 2 E) ≃*
        RadicalExclusions.ModelReduction.starImage E (F.H.pCoreIn 2) E) ∧
      ChapterC.C27Source.StarModels.Model
        (RadicalExclusions.ModelReduction.starImage E (F.H.pCoreIn 2) E) := by
  obtain ⟨B,hB,hn,hLB,hu,hfit,hcen,hs⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  let := hn
  let E := B.map G₀.subtype
  let e : B ≃* E := equivMapOfInjective B G₀.subtype G₀.subtype_injective
  let q := QuotientGroup.mk' (pCore 2 G₀)
  let eQ := QuotientGroup.congr (pCore 2 B) (pCore 2 E) e (pCore_map_iso 2 e)
  have hEB : E.subgroupOf G₀ = B := comap_map_eq_self_of_injective G₀.subtype_injective B
  have hE : E ∈ cComponentsIn G₀ := ⟨map_subtype_le _,hEB ▸ hB⟩
  have hEn : (E.subgroupOf G₀).Normal := hEB ▸ hn
  let : IsSimpleGroup (B ⧸ pCore 2 B) := hs
  have hEs : IsSimpleGroup (E ⧸ pCore 2 E) := eQ.symm.isSimpleGroup
  let := (pCore_isPGroup (p := 2) (G := G₀)).isNilpotent
  have hBq : (B.map q).IsCComponent := hB.map_quotient _
  have hr := radical_bot_of_fitting_bot hfit
  have hq : IsQuasisimple (B.map q) :=
    ((isCComponent_iff_isSubnormal_and_isQuasisimple_of_solvableRadical_eq_bot hr).mp hBq).2
  have hEq : IsQuasisimple (E ⧸ pCore 2 E) := hq.of_mulEquiv
    ((cComponentTwoCoreQuotientEquiv hB).symm.trans eQ)
  have hEf : generalizedFitting E = pCore 2 E := by
    have hBf : generalizedFitting B = pCore 2 B :=
      generalizedFitting_eq_pCore_of_selfCentralizing 2
        (subnormal_core_selfCentralizing ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
          B hB.subnormal)
    have hh := congrArg (map e.toMonoidHom) hBf
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hEout : ¬ E ≤ F.H ⊓ centralizer ({x} : Set G) := by
    intro hEJ
    apply hB.not_isSolvable
    apply isSolvable_of_prime_dvd_card_eq_two_or_three B
    intro p hp hd
    have hdE : p ∣ Nat.card E := (Nat.card_congr e.toEquiv) ▸ hd
    exact extraspecial_H_prime_divisor he hp
      (hdE.trans (card_dvd_of_le (hEJ.trans inf_le_left)))
  obtain ⟨_,_,hsetup⟩ := extraspecial_four_overgroup_pushingUp_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG.le hGC
  have hnorm : F.H.pCoreIn 2 ≤ normalizer (E : Set G) :=
    hsetup.radical_le.trans ((normal_subgroupOf_iff_le_normalizer hE.1).mp hEn)
  have hi : RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
        (F.H ⊓ centralizer ({x} : Set G)) E :=
    ⟨hsetup,hE,hEq,hEf,hEout,hnorm⟩
  have hz : center (E ⧸ pCore 2 E) = ⊥ := by
    let a := eQ.symm.trans (cComponentTwoCoreQuotientEquiv hB)
    have hbz := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hr hBq.subnormal
    have hh : (center (E ⧸ pCore 2 E)).map a.toMonoidHom = center (B.map q) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact (centerCongr a ⟨y,hy⟩).property
      · intro hx
        exact ⟨a.symm x,(centerCongr a.symm ⟨x,hx⟩).property,a.apply_symm_apply x⟩
    exact (map_eq_bot_iff_of_injective _ a.injective).mp (hh.trans hbz)
  have hker : (RadicalExclusions.ModelReduction.coreToStar hnorm).ker = ⊥ :=
    le_bot_iff.mp ((ChapterC.C27Source.coreToStar_ker_central_from_source hi).trans hz.le)
  let es := MulEquiv.ofBijective (RadicalExclusions.ModelReduction.coreToStar hnorm)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hker,RadicalExclusions.ModelReduction.coreToStar_surjective hnorm⟩
  exact ⟨E,hE,hEn,hLB,hEs,hi,⟨es⟩,ChapterC.C27Source.star_model_from_source hi⟩

private theorem four_intersection_product {D : Subgroup G}
    (hDK : D ≤ (center (K F)).map (K F).subtype) {x : G} (hx : x ∈ D) :
    K F ⊔ ((T : Subgroup G) ⊓ centralizer ({x} : Set G)) =
      F.H ⊓ centralizer ({x} : Set G) := by
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  apply le_antisymm
  · exact sup_le (le_inf (K_le_H F) hKC)
      (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)
  · rintro y ⟨hyH,hyC⟩
    rw [residual_product F] at hyH
    have hm : y ∈ (K F : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left (K F) (T : Subgroup G)
        ((F.invariant 1).trans (H_normalizes_K F))]
      exact hyH
    obtain ⟨k,hk,t,ht,rfl⟩ := hm
    have htC := (centralizer ({x} : Set G)).mul_mem
      ((centralizer ({x} : Set G)).inv_mem (hKC hk)) hyC
    rw [inv_mul_cancel_left] at htC
    exact mul_mem (mem_sup_left hk) (mem_sup_right ⟨ht,htC⟩)

/-- Every image of the actual intersection with two-group kernel retains
the marked Heisenberg two-residual after dividing by its own two-core. -/
theorem extraspecial_four_image_residual
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {D : Subgroup G} (hDK : D ≤ (center (K F)).map (K F).subtype)
    {x : G} (hx : x ∈ D)
    {A : Type*} [Group A] [Finite A]
    (f : (F.H ⊓ centralizer ({x} : Set G) : Subgroup G) →* A)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nonempty (pResidual 2 (A ⧸ pCore 2 A) ≃* HeisenbergPrime 3) := by
  let J := F.H ⊓ centralizer ({x} : Set G)
  let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
  have hprod : K F ⊔ S = J := four_intersection_product hDK hx
  have hres : (pResidual 2 J).map J.subtype = K F := by
    rw [←hprod]
    exact embedded_pResidual_join_pGroup (K F) S (K_twoPerfect F)
      (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F)))
  let eR : pResidual 2 J ≃* K F :=
    (equivMapOfInjective (pResidual 2 J) J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hres)
  let eK := QuotientGroup.congr (pCore 2 (pResidual 2 J)) (pCore 2 (K F)) eR
    (pCore_map_iso 2 eR)
  have hcore : pCore 2 (pResidual 2 J) = (pCore 2 J).subgroupOf (pResidual 2 J) :=
    pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 J).Normal).isSubnormal
  let eJ := (QuotientGroup.quotientMulEquivOfEq hcore).trans
    (pResidualQuotientEquiv 2 (pCore 2 J))
  let eA := f.pCoreQuotientEquiv hf hk
  let erA := (eA.subgroupMap (pResidual 2 (J ⧸ pCore 2 J))).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 eA))
  obtain ⟨e⟩ := he
  exact ⟨erA.symm.trans (eJ.symm.trans (eK.trans e))⟩

/-- The original Heisenberg Sylow subgroup acts faithfully on the actual component quotient. -/
theorem extraspecial_four_characteristicTwo_faithful_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ B : Subgroup G₀, B.IsCComponent ∧ ∃ hn : B.Normal,
      letI := hn
      (normalQuotientAction B (pCore 2 B)).ker = pCore 2 G₀ ∧
      ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y F.H ∧
        Nonempty (Y ≃* HeisenbergPrime 3) ∧ ∃ hYG : Y ≤ G₀,
          Function.Injective ((normalQuotientAction B (pCore 2 B)).comp (inclusion hYG)) := by
  obtain ⟨B,hB,hn,_,_,_,hc,_⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  refine ⟨B,hB,hn,?_⟩
  let := hn
  have hk := hB.normalQuotientAction_ker_of_centralizer_eq_bot hc
  refine ⟨hk,?_⟩
  obtain ⟨Y,hYK,_,hYH,⟨e⟩,_,_⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hkk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hkk)
  have hYG : Y ≤ G₀ := hYK.trans ((le_inf (K_le_H F) hKC).trans hJG.le)
  refine ⟨Y,hYK,hYH,⟨e⟩,hYG,?_⟩
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 3)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
  have hcop : Nat.Coprime 3 (Nat.card (normalQuotientAction B (pCore 2 B)).ker) := by
    rw [hk]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G₀)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (injective_comp_subtype_of_coprime_ker (normalQuotientAction B (pCore 2 B))
    hcop (Y.subgroupOf G₀) hYp.comap_subtype).comp (subgroupOfEquivOfLe hYG).symm.injective

/-- The actual automorphism image contains the inner group and the image of the original local intersection has odd index and marked Heisenberg residual. -/
theorem extraspecial_four_characteristicTwo_automorphism_restrictions
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ B : Subgroup G₀, B.IsCComponent ∧ ∃ hn : B.Normal,
      letI := hn
      let a := normalQuotientAction B (pCore 2 B)
      let M := (F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀
      let Mₐ := M.map a.rangeRestrict
      a.ker = pCore 2 G₀ ∧ MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ a.range ∧
        Odd Mₐ.index ∧ Nonempty (pResidual 2 (Mₐ ⧸ pCore 2 Mₐ) ≃* HeisenbergPrime 3) := by
  obtain ⟨B,hB,hn,_,_,_,hc,_⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  refine ⟨B,hB,hn,?_⟩
  let := hn
  let a := normalQuotientAction B (pCore 2 B)
  let C := centralizer ({x} : Set G)
  let J := F.H ⊓ C
  let M := J.subgroupOf G₀
  let Mₐ := M.map a.rangeRestrict
  have hk : a.ker = pCore 2 G₀ := hB.normalQuotientAction_ker_of_centralizer_eq_bot hc
  refine ⟨hk,?_,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    exact ⟨b,normalQuotientAction_inner B (pCore 2 B) b⟩
  · have hS : IsSylowIn 2 ((T : Subgroup G) ⊓ C) G₀ := IsSylowIn.restrict (H := C)
      (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
        D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
      ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG.le) hGC
    obtain ⟨P,hP⟩ := hS
    have hPM : (P : Subgroup G₀) ≤ M := by
      intro b hb
      have hh : (b : G) ∈ (T : Subgroup G) ⊓ C := hP ▸ mem_map_of_mem G₀.subtype hb
      exact ⟨F.invariant 1 hh.1,hh.2⟩
    have hodd : Odd M.index := Nat.not_even_iff_odd.mp (fun heven =>
      P.not_dvd_index (((even_iff_two_dvd).mp heven).trans (index_dvd_of_le hPM)))
    exact hodd.of_dvd_nat (M.index_map_dvd a.rangeRestrict_surjective)
  · let f : J →* Mₐ := (a.rangeRestrict.subgroupMap M).comp
      (subgroupOfEquivOfLe hJG.le).symm.toMonoidHom
    have hf : Function.Surjective f := (a.rangeRestrict.subgroupMap_surjective M).comp
      (subgroupOfEquivOfLe hJG.le).symm.surjective
    have hkf : f.ker = (pCore 2 G₀).comap (inclusion hJG.le) := by
      ext j
      change f j = 1 ↔ inclusion hJG.le j ∈ pCore 2 G₀
      rw [Subtype.ext_iff,Subtype.ext_iff]
      change inclusion hJG.le j ∈ a.ker ↔ inclusion hJG.le j ∈ pCore 2 G₀
      rw [hk]
    have hpf : IsPGroup 2 f.ker := by
      rw [hkf]
      exact pCore_isPGroup.comap_of_injective (inclusion hJG.le) (inclusion_injective hJG.le)
    exact extraspecial_four_image_residual he hDK hx f hf hpf

/-- Failure of characteristic two supplies an actual ordinary component and its original marked 1.1.5 action. -/
theorem extraspecial_four_ordinary_component_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hf : generalizedFitting (centralizer ({x} : Set G)) ≠
      pCore 2 (centralizer ({x} : Set G))) :
    ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      Chapter15.Section03.Candidates.ComponentStructure.HasModelAction115 B z := by
  have ho := extraspecial_four_oddCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨B,hB⟩ := exists_component_of_oddCore_eq_bot ho hf
  obtain ⟨_,_,z,hz,hzp,P,_,hs⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨hm,houtB,hmodel⟩ := Chapter1.lemma_1_1_5_three_knownSimple d.qtke
    (centralizer ({x} : Set G)) P F.H z hs B hB
  exact ⟨B,z,hB,hz,hzp,hm,houtB,hmodel⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
