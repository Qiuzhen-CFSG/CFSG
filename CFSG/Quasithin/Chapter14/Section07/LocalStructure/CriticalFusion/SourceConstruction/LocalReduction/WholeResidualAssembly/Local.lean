module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.ComponentStatement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalComponents
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreConclusion
public import Theory.GroupTheory.CComponent.UniqueResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# From source components to the whole local two-residual

The original point cubic has nonzero image in I/O₂(I). Since it belongs
to every component, and the component quotients have trivial center,
component commutation gives uniqueness. Source 14.7.27–28 and the Fitting
calculation then kill the three-core and hence the component centralizer.
The actual outer two-group bound makes a full Sylow subgroup supplement
the component. Perfectness identifies that component with O²(I), and
L₁-containment moves the entire original conjugate span.

All quotients are intrinsic and all normality is relative to I. The
component input is precisely 14.7.47; the remaining earlier structural,
module and 14.7.10 inputs retain their existing source producers.
Source: Aschbacher–Smith, 14.7.48, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem eq_bot_of_le_and_centralizes {X : Type*} [Group X]
    {A B : Subgroup X} (hz : center B = ⊥) (hAB : A ≤ B)
    (hc : A ≤ centralizer (B : Set X)) : A = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hh : (⟨x,hAB hx⟩ : B) ∈ center B := by
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (mem_centralizer_iff.mp (hc hx) b b.property)
  have he : (⟨x,hAB hx⟩ : B) = 1 := by simpa only [hz,mem_bot] using hh
  exact congrArg Subtype.val he

private theorem local_point_image_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≠ ⊥ := by
  intro he
  have hAQ : (F.Li L 1).subgroupOf I ≤ pCore 2 I := by
    simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
  have hA2 : IsPGroup 2 (F.Li L 1) :=
    (pCore_isPGroup.to_le hAQ).of_equiv (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI))
  have hdiv : 3 ∣ Nat.card (F.Li L 1) := by
    have hd := card_quotient_dvd_card (pCore 2 (F.Li L 1))
    rwa [pointResidual_core_quotient_card h structural] at hd
  obtain ⟨n,hn⟩ := hA2.exists_card_eq
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (hn ▸ hdiv)
  norm_num at h32

/-- Common point containment forces uniqueness and kills the literal quotient centralizer. -/
theorem local_unique_component_and_fitting
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    (∀ D : Subgroup I, D.IsCComponent → D = C) ∧
      fittingSubgroup (HStar I) = ⊥ ∧
      centralizer (C.map (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I)) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let A := ((F.Li L 1).subgroupOf I).map q
  let := pCore_isNilpotent (p := 2) (G := I)
  have hB := local_component_star_isComponent h hab structural previous faithful I hI C hC
  have hz : center B = ⊥ := ((source47 I hI C hC).2.of_equiv
    (cComponentTwoCoreQuotientEquiv hC)).center_and_outer.1
  have hAB : A ≤ B := map_mono (show (F.Li L 1).subgroupOf I ≤ C from by
    intro x hx
    obtain ⟨c,hc,he⟩ := (source47 I hI C hC).1 hx
    exact (show c = x from Subtype.ext he) ▸ hc)
  have hAne : A ≠ ⊥ := local_point_image_ne_bot h structural I hI
  have hu : ∀ D : Subgroup I, D.IsCComponent → D = C := by
    intro D hD
    by_contra hne
    have hD' := local_component_star_isComponent h hab structural previous faithful I hI D hD
    have hne' : D.map q ≠ B := fun he => hne (hD.eq_of_map_quotient_eq hC _ he)
    have hc := hD'.commutator_eq_bot_of_ne hB hne'
    have hAD : A ≤ D.map q := map_mono (show (F.Li L 1).subgroupOf I ≤ D from by
      intro x hx
      obtain ⟨c,hc,he⟩ := (source47 I hI D hD).1 hx
      exact (show c = x from Subtype.ext he) ▸ hc)
    exact hAne (eq_bot_of_le_and_centralizes hz hAB
      (hAD.trans (commutator_eq_bot_iff_le_centralizer.mp hc)))
  have hoddSolv : Group.IsSolvable (pPrimeCore 2 (HStar I)) :=
    odd_order_theorem _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hodd : pPrimeCore 2 (HStar I) = ⊥ := by
    rcases local_oddCore_eq_bot_or_point d h hab structural previous faithful earlier I hI with hb | ha
    · exact hb
    · change pPrimeCore 2 (HStar I) = A at ha
      have hc : ⁅B,pPrimeCore 2 (HStar I)⁆ = ⊥ := by
        rcases hB.normal_dichotomy (pPrimeCore 2 (HStar I)) with hb | hc
        · let := hoddSolv
          exact (hB.isCComponent.not_isSolvable
            (Group.isSolvable_of_isSolvable_injective (inclusion_injective hb))).elim
        · exact hc
      have hAc : A ≤ centralizer (B : Set (HStar I)) := by
        rw [←ha,←commutator_eq_bot_iff_le_centralizer,commutator_comm]
        exact hc
      exact (hAne (eq_bot_of_le_and_centralizes hz hAB hAc)).elim
  have hf : fittingSubgroup (HStar I) = ⊥ := by
    rw [local_fitting_eq_threeCore h hab structural previous faithful I hI,
      ←oddCore_eq_threeCore_of_small_fitting hoddSolv
        (local_fitting_eq_threeCore h hab structural previous faithful I hI)
        (local_threeCore_card_le_three d h hab structural previous faithful earlier I hI),hodd]
  let := pCore_isNilpotent (p := 2) (G := I)
  exact ⟨hu,hf,(hC.map_quotient _).centralizer_bot_of_unique_of_fitting_bot
    (fun _ hD => hC.unique_map_quotient hu _ hD) hf⟩

/-- The source component is the whole two-residual and fully moves the original span. -/
theorem local_component_eq_residual
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    pResidual 2 I = C ∧ C.map I.subtype ⊔ (T : Subgroup G) = I ∧
      ⁅F.UH I,C.map I.subtype⁆ = F.UH I := by
  obtain ⟨hu,hf,_⟩ := local_unique_component_and_fitting
    d h hab structural previous faithful earlier source47 I hI C hC
  let : C.Normal := hC.normal_of_unique hu
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hgen : C ⊔ (S : Subgroup I) = ⊤ :=
    hC.sylow_sup_eq_top_of_outer_twoGroup hu hf
      (source47 I hI C hC).2.center_and_outer.2 S
  have hp : IsPPerfect 2 C := by
    let := hC.perfect
    intro N hN hquot
    let := hN
    have hsub : Subsingleton (C ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (C ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro c _
    exact (QuotientGroup.eq_one_iff c).mp (Subsingleton.elim _ _)
  have hres := pResidual_eq_of_isPPerfect_sup C (S : Subgroup I) hp S.isPGroup' hgen
  have hgenG : C.map I.subtype ⊔ (T : Subgroup G) = I := by
    have he := congrArg (map I.subtype) hgen
    rwa [Subgroup.map_sup,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI),
      ←MonoidHom.range_eq_map,range_subtype] at he
  have hn : I ≤ normalizer (C.map I.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using
      (inferInstance : C.Normal)
  let := h.chosen.elementary
  exact ⟨hres,hgenG,(conjugateSpanBy_eq_commutator_of_seed V I (C.map I.subtype)
    (F.Li L 1) (map_subtype_le C) hn (source47 I hI C hC).1 (seed_commutator h F)).symm⟩


/-- Source 14.7.48 at every original local, with the whole residual identified. -/
theorem source_14_7_48
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ∃ C : Subgroup I, C.IsCComponent ∧
      (∀ D : Subgroup I, D.IsCComponent → D = C) ∧ C.Normal ∧
      centralizer (C.map (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I)) = ⊥ ∧
      pResidual 2 I = C ∧ C.map I.subtype ⊔ (T : Subgroup G) = I ∧
      ⁅F.UH I,C.map I.subtype⁆ = F.UH I := by
  obtain ⟨C,hC,_,_⟩ := local_exists_quasisimple_component d h hab structural previous
    faithful earlier I hI
  obtain ⟨hu,_,hz⟩ := local_unique_component_and_fitting d h hab structural previous
    faithful earlier source47 I hI C hC
  exact ⟨C,hC,hu,hC.normal_of_unique hu,hz,
    local_component_eq_residual d h hab structural previous faithful earlier source47 I hI C hC⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
