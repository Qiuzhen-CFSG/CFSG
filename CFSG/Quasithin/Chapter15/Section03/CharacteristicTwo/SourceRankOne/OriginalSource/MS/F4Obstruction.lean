module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.OriginalAction.F4Input
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications
/-!
# An original F4 obstruction to the universal C.1.34 interface

The explicit binary long-A2 parabolic satisfies every `SmallMSPair` clause,
with its actual component L, positive Sylow U, join P, and SL3(2) quotient.
The carrier comparison and MS3 certification are supplied by `F4Input`.

The nontrivial third lower commutator of Q = [O2(P),L] excludes alternatives
(1), (2), (3), and (5): their specified sections force Q to have class at
most two. Alternative (4) fails because the checked original fixed element
centralizes L but is moved by the original two-core. This proves the negation
of the currently stated universal `EarlierMSClassifications` interface.

No characteristic replacement is substituted for P. The additional ambient
hypotheses of original 15.3.23 are not asserted for this example; its more
specialized conclusion is not refuted here. Repair of the universal source
boundary, or an ambient route for its consumers, is required before assembly.

Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, especially
C.1.34(4)'s original-group centrality; Meierfrankenfeld--Stellmacher (1993),
the F4 examples on printed p.831 and the replacement calculation (4.4)--(4.5).
-/

public noncomputable section
open Subgroup
open Theory.SpecificGroups.LieType.F4LongParabolic.BinaryCoordinates
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.MS.F4Obstruction
private theorem characteristic_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (C : Subgroup G) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y,hy,rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy,?_⟩
  exact e.apply_symm_apply _

/-- The literal component and positive Sylow generate the original parabolic. -/
theorem original_join : L ⊔ Canonical.U = P :=
  le_antisymm (sup_le L_le_P Canonical.U_le_P)
    (sup_le (Canonical.E_le_U.trans le_sup_right) (le_sup_left.trans le_sup_left))

/-- The positive subgroup is a full Sylow of that literal join. -/
theorem original_isSylow : Chapter1.IsSylowIn 2 Canonical.U (L ⊔ Canonical.U) := by
  rw [original_join]
  refine ⟨Canonical.originalSylow, ?_⟩
  rw [Canonical.originalSylow_coe, map_subgroupOf_eq_of_le Canonical.U_le_P]

private theorem smallRankTwo_of_equiv {B : Type*} [Group B]
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.SL) : SmallRankTwoQuotient B := by
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact e.map_eq_one_iff.mp (Matrix.PSL3Two.center_eq_bot.le
      (centerCongr e ⟨x,hx⟩).property)
  have he : Subgroup.centralPreimage (pCore 2 B) = pCore 2 B := by
    change (center (B ⧸ pCore 2 B)).comap (QuotientGroup.mk' _) = _
    rw [hz]
    exact QuotientGroup.ker_mk' _
  let := BinaryMS.binary_perfect
  exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq he).trans
    (e.trans (topEquiv.symm.trans
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)))⟩

/-- Every SmallMSPair hypothesis holds for the same original matrix groups. -/
theorem original_smallMSPair : SmallMSPair KnownSimple.IsKnownSimple L Canonical.U := by
  have hchar : MSNoCharacteristicNormal L Canonical.U := by
    intro C hc hn
    let := hc
    let eU := subgroupOfEquivOfLe Canonical.U_le_P
    let C' := C.map eU.symm.toMonoidHom
    let : C'.Characteristic := @characteristic_map_equiv Canonical.U
      (Canonical.U.subgroupOf P) inferInstance inferInstance eU.symm C hc
    have hm : C'.map (Canonical.U.subgroupOf P).subtype =
        (C.map Canonical.U.subtype).subgroupOf P := by
      apply map_injective P.subtype_injective
      rw [map_subgroupOf_eq_of_le ((map_subtype_le C).trans Canonical.U_le_P)]
      change ((C.map eU.symm.toMonoidHom).map (Canonical.U.subgroupOf P).subtype).map
        P.subtype = C.map Canonical.U.subtype
      rw [map_map,map_map]
      congr 1
    have hc' : ChapterC.MSCharacteristicCondition (Canonical.U.subgroupOf P) := by
      rw [← Canonical.originalSylow_coe]
      exact originalSylow_msCharacteristic
    by_contra hne
    have hne' : C' ≠ ⊥ := fun hh => hne
      ((map_eq_bot_iff_of_injective C eU.symm.injective).mp hh)
    apply hc' C' inferInstance hne'
    rw [hm, ← original_join]
    exact hn
  refine {
    finite := inferInstance
    sqtk := original_join.symm ▸ original_sqtk
    fitting := original_join.symm ▸ QuotientModel.fitting_eq_core
    component := original_join.symm ▸ QuotientModel.L_component
    rankTwo := @smallRankTwo_of_equiv L inferInstance QuotientModel.componentQuotientEquiv
    characteristic := hchar
    product := ?_
    radical := ?_ }
  · intro g hg
    have hgP : g ∈ P := original_join ▸ hg
    obtain ⟨l,hl,r,hr,he⟩ := original_sylow_product Canonical.originalSylow ⟨g,hgP⟩
    have hrU : (r : Matˣ) ∈ Canonical.U := by
      change r ∈ Canonical.U.subgroupOf P
      rwa [← Canonical.originalSylow_coe]
    refine ⟨(l : Matˣ),hl,(r : Matˣ),hrU,?_⟩
    have he' := congrArg (fun a : P => (a : Matˣ)) he
    exact he'
  · apply sylow_msOddIndex original_isSylow
    rw [original_join]
    apply lt_of_le_of_ne Canonical.U_le_P
    intro he
    have ht : (Canonical.originalSylow : Subgroup P) = ⊤ := by
      rw [Canonical.originalSylow_coe,he,subgroupOf_self]
    obtain ⟨H,hH,_,hcore⟩ := original_sylow_radical Canonical.originalSylow
    have hle : (Canonical.originalSylow : Subgroup P) ≤ H := by
      rw [← hcore]
      exact map_subtype_le _
    exact (not_le_of_gt hH) (ht ▸ hle)

private theorem section_commutator_le {G B V F : Type*} [Group G] [Group B]
    [AddCommGroup V] [Field F] [Module F V]
    {K D N : Subgroup G} {a : K →* B} {rho : Representation F B V}
    (hm : HasSectionModel K D N a rho) : ⁅D,D⁆ ≤ N := by
  obtain ⟨hND,_,_,hn,e,_⟩ := hm
  let := hn
  have hcomm : IsMulCommutative (D ⧸ N.subgroupOf D) :=
    ⟨⟨fun x y => e.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
  have hh := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have hh' := map_mono (f := D.subtype) hh
  rwa [map_subtype_commutator,map_subgroupOf_eq_of_le hND] at hh'

private theorem centerIn_centralizes {G : Type*} [Group G] (D : Subgroup G) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn D ≤ centralizer (D : Set G) := by
  rintro x ⟨z,hz,rfl⟩ y hy
  exact congrArg D.subtype (mem_center_iff.mp hz ⟨y,hy⟩)

/-- The third lower commutator of the original C.1.34 core is nontrivial. -/
theorem original_third_ne_bot :
    ⁅⁅msQ L Canonical.U,msQ L Canonical.U⁆,msQ L Canonical.U⁆ ≠ ⊥ := by
  have hD : D ≤ msQ L Canonical.U := by
    change ⁅E,A⁆ ≤ ⁅(L ⊔ Canonical.U).pCoreIn 2,L⁆
    rw [original_join]
    exact commutator_mono E_le_core le_sup_left
  intro hh
  have hm := (commutator_mono (commutator_mono hD hD) hD) h_mem_third
  have h1 : h = 1 := by
    change h ∈ (⊥ : Subgroup Matˣ)
    rwa [← hh]
  exact h_does_not_commute_x (by rw [h1]; simp)

/-- No choice of marking satisfies the five original C.1.34 alternatives. -/
theorem original_no_module_alternatives
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ¬ MSModuleAlternatives L Canonical.U Canonical.U 1 (ZMod 2) e := by
  have noncentral : ¬ msQ L Canonical.U ⊓ centralizer (L : Set Matˣ) ≤
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (L ⊔ Canonical.U) := by
    intro hc
    apply original_core_fixed_factor_not_central
    have hcP : ⁅P.pCoreIn 2,L⁆ ⊓ centralizer (L : Set Matˣ) ≤
        Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn P := by
      simpa only [msQ,original_join] using hc
    exact hcP.trans ((centerIn_centralizes P).trans
      (centralizer_le (pCoreIn_le 2 P)))
  have not_classTwo {N : Subgroup Matˣ}
      (hn : N ≤ centralizer (msQ L Canonical.U : Set Matˣ))
      (hq : ⁅msQ L Canonical.U,msQ L Canonical.U⁆ ≤ N) : False := by
    apply original_third_ne_bot
    exact commutator_eq_bot_iff_le_centralizer.mpr (hq.trans hn)
  intro hh
  rcases hh with h1 | h2 | h3 | h4 | h5
  · exact not_classTwo bot_le (section_commutator_le h1.2.2)
  · exact not_classTwo bot_le (section_commutator_le h2.1)
  · exact not_classTwo (centerIn_centralizes _) (section_commutator_le h3.2.1)
  · exact noncentral h4.2.2.1
  · have hQL : msQ L Canonical.U ≤ L := by
      rw [msQ,original_join]
      have hh := originalInput.commutatorCore_le.trans (map_subtype_le _)
      have hmap := map_mono (f := P.subtype) hh
      rw [map_commutator,map_subgroupOf_eq_of_le L_le_P] at hmap
      exact hmap
    exact not_classTwo (inf_le_right.trans (centralizer_le hQL))
      (section_commutator_le h5.2.2.1)

/-- The currently stated universal earlier-source interface is obstructed by
this actual MS pair, with no residual source hypotheses. -/
theorem not_earlierMSClassifications :
    ¬ EarlierMSClassifications.{0} KnownSimple.IsKnownSimple := by
  intro hc
  obtain ⟨e,he⟩ := hc.linearThree Matˣ L Canonical.U original_smallMSPair 1 (by decide)
    (ZMod 2) (by simp) ⟨QuotientModel.componentQuotientEquiv⟩ Canonical.U
    original_isSylow le_rfl
  exact original_no_module_alternatives e he

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.MS.F4Obstruction
