module

public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.PointCentralizer

/-!
# The natural-point exclusions of C.1.37

Restrict the original natural action to the actual MS group J=L Baum(R).
Its quotient map is still the original projection. MS3 excludes a trivial
Thompson image, so the proved point-core and point-radical image identities
apply without extra hypotheses. Cases (3) and (4) force the omega-center
centralizer core to equal the Baumann subgroup, contradicting their literal
C.1.34 inequalities. Case (5) contradicts the original Sylow-fixed point.
Only the natural and doubled-natural commutator-core models remain.

The Chapter14 OriginalSource.ClassificationConsequences and the literal
OriginalInputs.LocalAlternatives.OriginalClassification consumer apply this
reduction. The independent C.1.34 classification remains explicit.

Source: Aschbacher--Smith C.1.37, printed p.143, and C.1.34, pp.136--137.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalPointControl
open Subgroup Theory.GroupTheory ChapterB
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {V : Subgroup G} [V.Normal]
  [IsElementaryAbelian 2 V]
namespace NaturalAction
variable (d : NaturalAction V)

/-- The original natural action restricted through the actual MS group inclusion. -/
noncomputable def inMSGroup : NaturalAction (V.subgroupOf d.J) where
  q := d.qJ
  onto := d.qJ_surjective
  kernel := d.qJ_kernel
  coordinates := (subgroupOfEquivOfLe d.module_le_J).trans d.coordinates
  action j v := d.action j ⟨v.val.val,v.property⟩

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem characteristic_map_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (C : Subgroup X) (hc : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  let b : MulAut X := e.trans (a.trans e.symm)
  exact ⟨b y,(characteristic_iff_le_comap.mp hc b) hy,e.apply_symm_apply _⟩

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- An ambient characteristic obstruction would violate MS3 inside the actual MS group. -/
theorem no_characteristic_of_msInput {κ : GroupClass.{u}}
    (h : BinaryMS.Input κ d.LJ d.BJ) :
    ¬ ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧ (C.map d.B.subtype).Normal := by
  rintro ⟨C,hc,hne,hn⟩
  let e : d.BJ ≃* d.B := subgroupOfEquivOfLe (show d.B ≤ d.J from le_sup_right)
  let D := C.map e.symm.toMonoidHom
  apply h.characteristic D (characteristic_map_equiv e.symm C hc)
    (fun hz => hne ((C.map_eq_bot_iff_of_injective e.symm.injective).mp hz))
  have he : D.map d.BJ.subtype = (C.map d.B.subtype).subgroupOf d.J := by
    apply map_injective d.J.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le C).trans le_sup_right)]
    change ((C.map e.symm.toMonoidHom).map d.BJ.subtype).map d.J.subtype = _
    rw [map_map,map_map]
    rfl
  rw [he]
  let := hn
  infer_instance

/-- MS3 rules out the characteristic obstruction from a trivial Thompson image. -/
theorem thompson_image_ne_bot_of_msInput {κ : GroupClass.{u}}
    (h : BinaryMS.Input κ d.LJ d.BJ) :
    (Stellmacher.elementaryAbelianMaxJ d.R).map d.q ≠ ⊥ :=
  fun hz => d.no_characteristic_of_msInput h (d.characteristic_of_thompson_image_bot hz)

/-- The actual Baumann radical has the original full point-radical image. -/
theorem BJ_image_of_msInput {κ : GroupClass.{u}}
    (h : BinaryMS.Input κ d.LJ d.BJ) : d.BJ.map d.qJ = pointV := by
  rw [qJ, ← map_map,map_subgroupOf_eq_of_le (show d.B ≤ d.J from le_sup_right)]
  exact d.B_image (d.thompson_image_ne_bot_of_msInput h)

/-- The point parabolic in the MS group has precisely the Baumann radical as two-core. -/
theorem PJ_core_of_msInput {κ : GroupClass.{u}}
    (h : BinaryMS.Input κ d.LJ d.BJ) : d.PJ.pCoreIn 2 = d.BJ :=
  d.PJ_core (d.thompson_image_ne_bot_of_msInput h)

end NaturalAction

private theorem natural_section_card {X : Type*} [Group X] {K D : Subgroup X}
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : HasSectionModel K D ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := ZMod 2) 3)) : Nat.card D = 8 := by
  obtain ⟨_,_,_,hn,f,_⟩ := hm
  let := hn
  let q : D ≃* Multiplicative (Fin 3 → ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf D).symm).trans f)
  rw [Nat.card_congr q.toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp

private theorem msQ_eq {X : Type*} [Group X] {κ : GroupClass} {K R : Subgroup X}
    (h : BinaryMS.Input κ K R) : msQ K R = BinaryMS.commutatorCore K := by
  rw [msQ,h.sup_eq_top]
  rw [show (⊤ : Subgroup X).pCoreIn 2 = pCore 2 X from pCore_map_iso 2 topEquiv]

namespace NaturalAction
variable (d : NaturalAction V)

/-- The original point marking contradicts the third alternative's centralizer-core inequality. -/
theorem not_case_three {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R) (hR : R = d.P.pCoreIn 2) (himage : R.map d.q = pointV)
    (S : Sylow 2 G) (hRS : R ≤ (S : Subgroup G))
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hZ : HasSectionModel K (SourceInterface.centerIn (msQ K R)) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := ZMod 2) 3)) :
    ¬ MSNotCentralizerCore K R (S : Subgroup G) := by
  have hc := natural_section_card e hZ
  rw [SourceInterface.centerIn,msQ_eq h] at hc
  have hz := d.center_eq_module_of_card h hc
  have hm : ⁅(center (BinaryMS.commutatorCore K)).map (BinaryMS.commutatorCore K).subtype,K⁆ ≤ V := by
    rw [hz,← h.residual_eq,d.module_commutator]
  have he := d.omega_centralizer_eq_point_of_center_commutator h hm hR himage S hRS
  intro hn
  apply hn
  change R = ((K ⊔ R) ⊓ centralizer (Subgroup.omegaCenterIn (S : Subgroup G) : Set G)).pCoreIn 2
  rw [h.sup_eq_top,top_inf_eq,he]
  exact hR

/-- The order-eight central commutator contradicts the fourth alternative's core inequality. -/
theorem not_case_four {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R) (hR : R = d.P.pCoreIn 2) (himage : R.map d.q = pointV)
    (S : Sylow 2 G) (hRS : R ≤ (S : Subgroup G))
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hU : HasSectionModel K ⁅SourceInterface.centerIn (msQ K R),K⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := ZMod 2) 3)) :
    ¬ MSNotCentralizerCore K R (S : Subgroup G) := by
  have hc := natural_section_card e hU
  rw [SourceInterface.centerIn,msQ_eq h] at hc
  have hm := d.center_commutator_eq_module_of_card h hc
  have he := d.omega_centralizer_eq_point_of_center_commutator h hm.le hR himage S hRS
  intro hn
  apply hn
  change R = ((K ⊔ R) ⊓ centralizer (Subgroup.omegaCenterIn (S : Subgroup G) : Set G)).pCoreIn 2
  rw [h.sup_eq_top,top_inf_eq,he]
  exact hR

/-- The exact five-way source proposition leaves only the natural and doubled-natural cores. -/
theorem ms_natural_or_double {κ : GroupClass.{u}}
    (h : BinaryMS.Input κ d.LJ d.BJ)
    (S : Sylow 2 d.J) (hRS : d.BJ ≤ (S : Subgroup d.J))
    (e : (d.LJ ⧸ pCore 2 d.LJ) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : MSModuleAlternatives d.LJ d.BJ (S : Subgroup d.J) 1 (ZMod 2) e) :
    HasSectionModel d.LJ (msQ d.LJ d.BJ) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := ZMod 2) 3) ∨
    HasSectionModel d.LJ (msQ d.LJ d.BJ) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural (k := ZMod 2) 3)) := by
  let : IsElementaryAbelian 2 (V.subgroupOf d.J) := IsElementaryAbelian.subgroupOf d.module_le_J
  have hR : d.BJ = d.inMSGroup.P.pCoreIn 2 := (d.PJ_core_of_msInput h).symm
  have hi : d.BJ.map d.inMSGroup.q = pointV := d.BJ_image_of_msInput h
  rcases hm with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1.2.2
  · exact Or.inr h2.1
  · exact False.elim (d.inMSGroup.not_case_three h hR hi S hRS e h3.1 h3.2.2)
  · exact False.elim (d.inMSGroup.not_case_four h hR hi S hRS e h4.2.2.2.2.2.1 h4.2.2.2.2.2.2.2.2.2)
  · apply False.elim
    apply d.inMSGroup.omega_not_central S
    have hz := h5.2.2.2.1
    rw [h.sup_eq_top] at hz
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hz hx
    exact (mem_center_iff.mpr (fun g => congrArg Subtype.val (mem_center_iff.mp hz ⟨g,mem_top _⟩)))

end NaturalAction
end CFSG.Quasithin.ChapterC.NaturalPointControl
