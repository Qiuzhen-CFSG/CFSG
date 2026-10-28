module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceDouble

public import Theory.GroupTheory.NormalCentralQuotientAction.KernelCriterion

/-!
# Excluding the doubled-natural binary MS row

For the actual constituent extension XQI, the original plane lies in the
local Sylow omega-center, and its centralizer has two-core QI. In the doubled
natural row, the small MS construction gives a simultaneously marked Sylow
and unique common-axis offender. A cubic fixes the Sylow-fixed space and,
by averaging, the original plane. It therefore normalizes QI, whereas it
moves the unique offender in QI, a contradiction.

The original C.2.7 consumer uses the common intrinsic commutator core to
supply the abelian order-64 hypothesis. The radical R of that description
is never identified with QI. This eliminates C.1.34(2) and retains natural
case (1) and the two nonabelian rows (3)--(4). Their exclusion is completed in
NonblockExclusion using NaturalCenter; the earlier Kc orbit premise retains its
geometry and small-parabolic producers and plane-uniqueness final discharge.

Source: Aschbacher--Smith C.1.34(2) and its common-axis argument, pp.136--137;
preliminary 15.2.23, pp.1115--1116, refs/quasithin.pdf. The actual doubled
MS action and Sylow correction are reused from MarkedMS.LinearThree.
AbelianSourceDouble; only the centralizer is changed to the original plane.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open BinaryLinearThree BinaryLinearThree.DoubledOffenders
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem doubled_not_centralizer_core {L R S : Subgroup G}
    (a : DoubledSourceAction L R S) (W : Subgroup G) (hRS : R ≤ S)
    (hlift : L ⊓ centralizer ((msQ L R ⊓ centralizer (S : Set G) : Subgroup G) : Set G) ≤
      centralizer (W : Set G)) :
    R ≠ ((L ⊔ R) ⊓ centralizer (W : Set G)).pCoreIn 2 := by
  intro heq
  obtain ⟨c, hcfix, hcmove⟩ := exists_point_fixer_moving_axis a.frame
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (a.marking.symm c)
  have hlc : a.marking (QuotientGroup.mk' (pCore 2 L) l) = c := by
    rw [hl, MulEquiv.apply_symm_apply]
  let j : (L ⊔ R : Subgroup G) := ⟨l, (show L ≤ L ⊔ R from le_sup_left) l.property⟩
  have hj : a.actor j = δ c := (a.component l).trans (congrArg δ hlc)
  have hlfix : (l : G) ∈ centralizer
      ((msQ L R ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
    intro x hx
    let xQ : msQ L R := ⟨x, hx.1⟩
    have hfixed : (a.coordinates xQ).toAdd ∈ fixedSpace τ
        ((Matrix.PSL3Two.borelSL.map (MulAut.conj a.frame).toMonoidHom).map δ) := by
      rw [← a.componentSylow]
      rintro ⟨_, s, hs, rfl⟩
      exact (a.equivariant s xQ xQ (by
        change x = (s : G) * x * (s : G)⁻¹
        rw [hx.2 s hs.1, mul_inv_cancel_right])).symm
    let y : msQ L R := ⟨(l : G) * x * (l : G)⁻¹,
      (mem_normalizer_iff.mp (a.normalized j.property) x).mp hx.1⟩
    have hy : y = xQ := a.coordinates.injective (Multiplicative.toAdd.injective (by
      rw [a.equivariant j xQ y rfl, hj]
      exact hcfix _ hfixed))
    have hv := congrArg (fun z : msQ L R => (z : G)) hy
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  have hlZ := hlift ⟨l.property, hlfix⟩
  let C := (L ⊔ R) ⊓ centralizer (W : Set G)
  have hlC : (l : G) ∈ C := ⟨j.property, hlZ⟩
  have hlN : (l : G) ∈ normalizer R := by
    rw [heq]
    exact normalizer_le_normalizer_characteristic_image C (pCore 2 C)
      (C.le_normalizer hlC)
  have hjN : j ∈ normalizer (R.subgroupOf (L ⊔ R) : Set (L ⊔ R : Subgroup G)) :=
    (Subgroup.le_normalizer_comap (L ⊔ R).subtype) hlN
  have himage : a.actor j ∈ normalizer ((R.subgroupOf (L ⊔ R)).map a.actor : Set D) :=
    (R.subgroupOf (L ⊔ R)).le_normalizer_map a.actor (mem_map_of_mem a.actor hjN)
  have hnorm := normalizes_unique_offender τ
    (normalizer ((R.subgroupOf (L ⊔ R)).map a.actor : Set D))
    ((R.subgroupOf (L ⊔ R)).map a.actor) ((S.subgroupOf (L ⊔ R)).map a.actor)
    ((BinaryLinearThree.R.map (MulAut.conj a.frame).toMonoidHom).map δ)
    le_rfl a.offender_le (map_mono (comap_mono hRS)) (axis_isOffender a.frame)
    a.unique_offender
  exact hcmove (hj ▸ hnorm himage)


/-- The doubled MS core forbids the radical from being the two-core of the
centralizer of any subgroup of the local Sylow omega-center. -/
theorem doubled_not_plane_centralizer_core {κ : GroupClass} {L R S W : Subgroup G}
    (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S)
    (hW : W ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S) :
    R ≠ ((L ⊔ R) ⊓ centralizer (W : Set G)).pCoreIn 2 := by
  obtain ⟨a⟩ := h.exists_doubledSourceAction e hc hcard hS hRS
  apply doubled_not_centralizer_core a W hRS
  exact (centralizer_omega_le_of_double_split
    (h.abelian_source_double_split e hc hcard hS)).trans (centralizer_le hW)

private theorem binary_smallMSPair {κ : GroupClass} {L R : Subgroup G}
    (h : LinearThreeMSPair κ L R 1 (ZMod 2)) (hodd : MSOddIndex L R)
    (hn : R ≤ normalizer (L : Set G)) : SmallMSPair κ L R := by
  obtain ⟨e⟩ := h.model
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact e.map_eq_one_iff.mp (Matrix.PSL3Two.center_eq_bot.le
      (centerCongr e ⟨x,hx⟩).property)
  have heq := centralPreimage_eq_of_center_quotient_eq_bot (pCore 2 L) hz
  let e' := (QuotientGroup.quotientMulEquivOfEq heq).trans e
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  refine ⟨inferInstance,h.sqtk,h.fitting,?_,h.component.2,Or.inl ⟨?_⟩,
    hodd,h.characteristic⟩
  · intro g hg
    have hm : g ∈ (L : Set G) * (R : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hn]
      exact hg
    exact hm
  · exact e'.trans (topEquiv.symm.trans
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))


/-- The binary full-quotient MS input supplies the actual small MS pair.
The odd-index and product premises refer to the same original radical. -/
theorem linearThree_smallMSPair_of_odd_index {κ : GroupClass} {L R : Subgroup G}
    (h : LinearThreeMSPair κ L R 1 (ZMod 2)) (hodd : MSOddIndex L R)
    (hn : R ≤ normalizer (L : Set G)) : SmallMSPair κ L R :=
  binary_smallMSPair h hodd hn

namespace PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
open Stellmacher Theory.GroupTheory
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual XQI pair cannot have an abelian commutator core of order 64. -/
theorem linearThree_component_no_doubled_core
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    (hout : ¬ X.map I.subtype ≤ Mc)
    (hc : IsMulCommutative (msQ (X.map I.subtype) (planeParabolicCore T H ZS)))
    (hcard : Nat.card (msQ (X.map I.subtype) (planeParabolicCore T H ZS)) = 64) :
    False := by
  have hms := d.linearThree_component_msPair_of_escape hI hfit hX e hout
  obtain ⟨ho,hcore⟩ := d.linearThree_component_ms_odd_index hI hX e hout
  have hQI : planeParabolicCore T H ZS ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hn : planeParabolicCore T H ZS ≤ normalizer (X.map I.subtype : Set G) := by
    rw [←map_subgroupOf_eq_of_le hQI]
    exact (map_mono (d.linearThree_parabolic_core_normalizes_component hI hX e)).trans
      (le_normalizer_map I.subtype)
  have hh := binary_smallMSPair hms ho hn
  obtain ⟨e'⟩ := hms.model
  exact doubled_not_plane_centralizer_core hh e' hc hcard
    (d.linearThree_component_extension_sylow hI hX e)
    (le_inf (d.planeParabolicCore_le_plane hI) le_sup_right)
    (d.plane_extension_omega_contains hI hfit _) hcore.symm


omit d [Finite G] in
private theorem double_section_data {X Q : Subgroup G} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : Chapter1.XiQuotient X ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hm : HasSectionModel X Q ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    IsMulCommutative Q ∧ Nat.card Q = 64 := by
  obtain ⟨_,_,_,hn,φ,_⟩ := hm
  let := hn
  let f : Q ≃* Multiplicative ((Fin 3 → F) × (Fin 3 → F)) :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (show (⊥ : Subgroup Q) = (⊥ : Subgroup G).subgroupOf Q by
          rw [bot_subgroupOf])).trans φ)
  refine ⟨⟨⟨fun a b => f.injective (by simp only [map_mul,mul_comm])⟩⟩,?_⟩
  rw [Nat.card_congr f.toEquiv]
  change Nat.card ((Fin 3 → F) × (Fin 3 → F)) = 64
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,hF]
  norm_num

omit d [Finite G] in
/-- A literal doubled-natural section has commutative carrier
of order 64; the same quotient map supplies both conclusions. -/
theorem binary_doubled_section_data {X Q : Subgroup G} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : Chapter1.XiQuotient X ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hm : HasSectionModel X Q ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    IsMulCommutative Q ∧ Nat.card Q = 64 :=
  double_section_data hF e hm

/-- The original C.2.7 branch cannot satisfy the doubled-natural source row,
including when S exchanges its component with another constituent. -/
theorem LinearThree.Branch.binary_no_doubled_section
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : LinearThree.Branch M I X 1 F)
    (e : Chapter1.XiQuotient X ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    ¬ HasSectionModel X (msQ X (planeParabolicCore T H ZS)) ⊥
      (linearThreeActor e) ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)) := by
  intro hm
  obtain ⟨hc,hcard⟩ := double_section_data (by simpa only [pow_one] using b.field_card) e hm
  let A := X.subgroupOf I
  let a : A ≃* X := subgroupOfEquivOfLe b.input.component.1
  have hA : A.map I.subtype = X := map_subgroupOf_eq_of_le b.input.component.1
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [←Nat.card_eq_fintype_card,pow_one] using b.field_card)).symm
  let eA : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.PSL :=
    (((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e).trans
      (Atlas.fieldEquivSL 3 f)).trans Matrix.PSL3Two.equiv
  apply d.linearThree_component_no_doubled_core hI hfit b.input.component.2 eA
  · simpa only [map_subgroupOf_eq_of_le b.input.component.1] using b.binary_not_le_partner d horbit hI
  · exact (congrArg (fun Y : Subgroup G =>
      IsMulCommutative (msQ Y (planeParabolicCore T H ZS))) hA).mpr hc
  · simpa only [map_subgroupOf_eq_of_le b.input.component.1] using hcard

/-- After excluding the doubled-natural row, the non-block possibilities have
nonabelian intrinsic core. The remaining source rows (3) and (4) retain their
original module sections and radical inequality. -/
theorem LinearThree.Branch.binary_preliminary_reduced_core_cases
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : LinearThree.Branch M I X 1 F) :
    (ChapterC.IsBlock (X.subgroupOf I) ∧ ChapterC.IsSL3EvenBlock X 1 ∧
      ∃ e : Chapter1.XiQuotient X ≃* Matrix.SpecialLinearGroup (Fin 3) F,
        HasSectionModel X (msQ X (planeParabolicCore T H ZS)) ⊥
          (linearThreeActor e) (Representation.specialLinearNatural (k := F) 3)) ∨
    ∃ e : Chapter1.XiQuotient X ≃* Matrix.SpecialLinearGroup (Fin 3) F,
      let Q := msQ X (planeParabolicCore T H ZS)
      let Z := Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
      let C := Q ⊓ centralizer (X : Set G)
      let U := ⁅Z,X⁆
      let Phi := frattiniIn Q
      let D := Q ⊓ centralizer (Phi : Set G)
      let a := linearThreeActor e
      let v := Representation.specialLinearNatural (k := F) 3
      let R := (M ⊓ I).pCoreIn 2
      let S := planeSylow T ZS ⊓ (X ⊔ R)
      (HasSectionModel X Z ⊥ a v ∧ HasSectionModel X Q Z a (v.dual.prod v.dual) ∧
        MSNotCentralizerCore X R S) ∨
      (IsElementaryAbelian 2 C ∧ Nat.card C = 4 ∧
        C ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (X ⊔ R) ∧
        Z = C ⊔ U ∧ C ⊓ U = ⊥ ∧ HasSectionModel X U ⊥ a v ∧
        HasSectionModel X Phi Z a v.dual ∧
        HasSectionModel X D Phi a (v.dual.prod v.dual) ∧
        HasSectionModel X Q D a (v.prod v) ∧ MSNotCentralizerCore X R S) := by
  rcases b.binary_preliminary_core_cases d horbit hI hfit with h | ⟨e,h⟩
  · exact Or.inl h
  · dsimp only [LinearThree.NonblockCoreRows] at h
    rcases h with h | h
    · exact (b.binary_no_doubled_section d horbit hI hfit e h.1).elim
    · exact Or.inr ⟨e,by simpa only [Nat.mul_one, Nat.reducePow] using h⟩

end PlaneUniquenessPreceding

end CFSG.Quasithin.Chapter15.Section02
