module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.DoubleExclusion
public import Theory.Representation.PSL3Two.NaturalSylowFixed
public import Theory.GroupTheory.PResidual.CentralizerCorrection

/-!
# The actual Sylow omega-center in the natural central-layer rows

In C.1.34(3)--(4), the displacement of C_O₂(XQI)(Q) under X lies in
the natural part of Z(Q). Averaging corrects each local Sylow omega-center
element by an X-central element into the natural Sylow-fixed line.
The original plane is moved by X, so it detects that same line. Thus its
centralizer in XQI equals the full local omega-center centralizer, and
both have the already constructed two-core QI.

This is the literal core comparison needed to eliminate rows (3)--(4).
It applies to individual constituents even when the original S exchanges
components; the original C.2.7 radical R is not used or identified with QI.
The row exclusion and earlier C.1.34 input discharge remain with the
block-exclusion and enclosing plane assembly respectively.

Source: Aschbacher--Smith C.1.34(3)--(4), pp.136--137, and preliminary
15.2.23, pp.1115--1116; refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem natural_section_fixed_card {L U : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : HasSectionModel L U ⊥ (linearThreeActor e)
      (specialLinearNatural (k := ZMod 2) 3)) (P : Sylow 2 L) :
    IsElementaryAbelian 2 U ∧
      Nat.card (U ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G) : Subgroup G) ≤ 2 := by
  simp only [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,φ,hφ⟩ := hm
  let := hn
  let f : U ≃* Multiplicative (Fin 3 → ZMod 2) := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (show (⊥ : Subgroup U) = (⊥ : Subgroup G).subgroupOf U by rw [bot_subgroupOf])).trans φ)
  have hf : ∀ (l : L) (u u' : U), (u' : G) = l * (u : G) * (l : G)⁻¹ →
      (f u').toAdd = specialLinearNatural 3 (linearThreeActor e l) (f u).toAdd := hφ
  let : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 2)) :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro v
      apply Multiplicative.toAdd.injective
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      ext i
      exact CharTwo.add_self_eq_zero _)⟩
  have hel : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    f.toMonoidHom f.injective
  refine ⟨hel,?_⟩
  let a := linearThreeActor e
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let PS := P.mapSurjective (f := a) ha
  let C := U ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G)
  let g : C → fixedSpace BinaryLinearThree.W (PS : Subgroup BinaryLinearThree.Group) :=
    fun u => ⟨(f ⟨u,u.property.1⟩).toAdd,by
      intro p
      have hp : (p : BinaryLinearThree.Group) ∈ (P : Subgroup L).map a := p.property
      obtain ⟨l,hl,heq⟩ := hp
      change BinaryLinearThree.W (p : BinaryLinearThree.Group) _ = _
      rw [←heq]
      exact (hf l ⟨u,u.property.1⟩ ⟨u,u.property.1⟩ (by
        rw [u.property.2 l (mem_map_of_mem L.subtype hl),mul_inv_cancel_right])).symm⟩
  have hg : Function.Injective g := by
    intro u v h
    have he := f.injective (Multiplicative.toAdd.injective (congrArg Subtype.val h))
    exact Subtype.ext (congrArg (fun x : U => (x : G)) he)
  exact (Nat.card_le_card_of_injective g hg).trans
    (BinaryLinearThree.card_sylow_natural_fixed_le_two PS)

/-- A natural central layer identifies the centralizer of any moved subgroup
of the literal Sylow omega-center with that whole omega-center centralizer. -/
theorem linearThreeMS_omega_centralizer_eq_of_natural_layer
    {κ : GroupClass} {L R S W U : Subgroup G}
    (hms : LinearThreeMSPair κ L R 1 (ZMod 2))
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S)
    (hRL : R ≤ normalizer (L : Set G))
    (hW : W ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S) (hmove : ¬ W ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : HasSectionModel L U ⊥ (linearThreeActor e)
      (specialLinearNatural (k := ZMod 2) 3))
    (hU : ⁅Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ L R),L⁆ ≤ U) :
    (L ⊔ R) ⊓ centralizer (W : Set G) =
      (L ⊔ R) ⊓ centralizer (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S : Set G) := by
  let J := L ⊔ R
  let N := J.pCoreIn 2
  let A := L.subgroupOf J
  let a : A ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect A := hms.component.2.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hpL : IsPPerfect 2 L := by
    intro B hn ht
    let := hn
    let := ht.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ B)
  obtain ⟨S0,hS0⟩ := hS
  have hSJ : S ≤ J := hS0 ▸ map_subtype_le (S0 : Subgroup J)
  have hNS : N ≤ S := (pCoreIn_le_sylow J S0).trans_eq hS0
  obtain ⟨P0,hP0⟩ := S0.exists_subgroupOf_eq_of_subnormal A hms.component.2.subnormal
  let P : Sylow 2 L := P0.mapSurjective (f := a.toMonoidHom) a.surjective
  have hPS : (P : Subgroup L).map L.subtype ≤ S := by
    rintro _ ⟨l,hl,rfl⟩
    obtain ⟨b,hb,rfl⟩ := hl
    have hbS : (b : J) ∈ S0 := by
      rw [hP0] at hb
      exact hb
    exact hS0 ▸ mem_map_of_mem J.subtype hbS
  obtain ⟨he,hcard⟩ := natural_section_fixed_card e hm P
  let := he
  have hLN : L ≤ normalizer (N : Set G) :=
    (show L ≤ J from le_sup_left).trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hQN : msQ L R ≤ N := le_normalizer_iff_commutator_le_left.mp hLN
  have hZC : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S ≤ centralizer (S : Set G) := by
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff S z).mp hz).2.2
  have hZN : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S ≤ N := by
    intro z hz
    have hzS := ((Stellmacher.mem_omegaOneCenterAmbient_iff S z).mp hz).1
    have hc : (⟨z,hSJ hzS⟩ : J) ∈ centralizer (pCore 2 J : Set J) := by
      intro n hn
      exact Subtype.ext (hZC hz n (hNS (mem_map_of_mem J.subtype hn)))
    have hself : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
      rw [← hms.fitting]
      exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := J)
    exact mem_map_of_mem J.subtype (hself hc)
  have hLC : L ⊓ centralizer (W : Set G) =
      L ⊓ centralizer (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S : Set G) := by
    apply centralizer_eq_of_binary_fixed_corrections L U
      ((P : Subgroup L).map L.subtype) (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S) W hW hmove hcard
    intro z hz
    exact fixed_correction_of_center_commutator L N U hpL
      (isPGroup_pCoreIn 2 J) hLN hm.2.1
      (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu) hU P z
      (hZN hz) (centralizer_le (hQN.trans hNS) (hZC hz))
      (centralizer_le hPS (hZC hz))
  have hRZ : R ≤ centralizer (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S : Set G) :=
    le_centralizer_iff.mp (hZC.trans (centralizer_le hRS))
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hW))
  rintro g ⟨hg,hgc⟩
  have hgprod : g ∈ (L : Set G) * (R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L R hRL]
    exact hg
  obtain ⟨l,hl,r,hr,rfl⟩ := hgprod
  have hlW : l ∈ centralizer (W : Set G) := by
    have hh := (centralizer (W : Set G)).mul_mem hgc
      ((centralizer (W : Set G)).inv_mem (centralizer_le hW (hRZ hr)))
    simpa only [mul_inv_cancel_right] using hh
  exact ⟨hg,(centralizer (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S : Set G)).mul_mem
    ((hLC ▸ (show l ∈ L ⊓ centralizer (W : Set G) from ⟨hl,hlW⟩)).2) (hRZ hr)⟩

namespace PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
open Stellmacher Theory.GroupTheory
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual XQI centralizer has core QI also for its full local Sylow
omega-center, whenever its central commutator layer is natural. -/
theorem linearThree_component_omega_core_of_natural_layer
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : X.IsCComponent)
    (eX : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    (hout : ¬ X.map I.subtype ≤ Mc) {U : Subgroup G}
    (e : ((X.map I.subtype) ⧸ pCore 2 (X.map I.subtype)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : HasSectionModel (X.map I.subtype) U ⊥ (linearThreeActor e)
      (specialLinearNatural (k := ZMod 2) 3))
    (hU : ⁅Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ (X.map I.subtype) (planeParabolicCore T H ZS)),X.map I.subtype⁆ ≤ U) :
    ((X.map I.subtype ⊔ planeParabolicCore T H ZS) ⊓ centralizer
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (planeSylow T ZS ⊓
        (X.map I.subtype ⊔ planeParabolicCore T H ZS)) : Set G)).pCoreIn 2 =
      planeParabolicCore T H ZS := by
  have hQI : planeParabolicCore T H ZS ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hn : planeParabolicCore T H ZS ≤ normalizer (X.map I.subtype : Set G) := by
    rw [←map_subgroupOf_eq_of_le hQI]
    exact (map_mono (d.linearThree_parabolic_core_normalizes_component hI hX eX)).trans
      (le_normalizer_map I.subtype)
  have hmove : ¬ ZS ≤ centralizer (X.map I.subtype : Set G) := by
    intro hh
    exact hout ((le_centralizer_iff.mp hh).trans
      ((d.centralizer_le_intersection hI).trans inf_le_left))
  have he := linearThreeMS_omega_centralizer_eq_of_natural_layer
    (d.linearThree_component_msPair_of_escape hI hfit hX eX hout)
    (d.linearThree_component_extension_sylow hI hX eX)
    (le_inf (d.planeParabolicCore_le_plane hI) le_sup_right) hn
    (d.plane_extension_omega_contains hI hfit _) hmove e hm hU
  rw [← he]
  exact (d.linearThree_component_ms_odd_index hI hX eX hout).2

end PlaneUniquenessPreceding

end CFSG.Quasithin.Chapter15.Section02
