module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.Action
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ComponentSelection.GroupCases
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components.Selection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Faithfulness
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The small subnormal witness in 14.7.70

The full native adequate B.5.6 alternatives on the actual offender subgroup
supply an ordinary component, S₃, or S₃ × S₃. In the product case the first
factor gives a subnormal S₃ in the literal plus quotient I/O₂(I).

In the component case, lift through the actual two-core quotient. Some
I-conjugate of the lift moves the original central involution z: otherwise
all conjugates centralize ⟨z⟩, so the lift centralizes V_I = ⟨⟨z⟩ᴵ⟩ and lies
in O₂(I), contradicting nonsolvability. The moving conjugate belongs to the
actual faithful local family. The full earlier 14.3.4(1–2) restriction then
identifies its intrinsic two-core quotient with A₅ or L₃(2). The canonical
C-component quotient equivalence realizes this as an actual subnormal
subgroup of I/O₂(I), with the original quotient map unchanged.

The universal earlier classification is the existing
`EarlierFaithfulClassification` contract, produced by qt-14-03-prelim.
Its discharge, CoreFacts, and construction of the native adequate alternative
remain with the source assembly owners. This module completes the conditional
witness-extraction contract; it does not assert the whole of 14.7.70.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.70, printed pp.1074–1075 (PDF pp.1091–1092); 14.3.4(1–2), p.990;
B.5.6, p.105. GroupCases.lean records the adapted intrinsic calculations.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ComponentSelection
open Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u

private theorem centralizes_span_of_conjugates {X : Type*} [Group X]
    (A Z H : Subgroup X)
    (hc : ∀ i ∈ H, A.map (MulAut.conj i).toMonoidHom ≤ centralizer (Z : Set X)) :
    A ≤ centralizer (conjugateSpanBy Z H : Set X) := by
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro _ ⟨i, hi, z, hz, rfl⟩
  apply mem_centralizer_iff.mpr
  intro a ha
  have hh := mem_centralizer_iff.mp
    (hc i⁻¹ (H.inv_mem hi) (mem_map_of_mem _ ha)) z hz
  change z * (i⁻¹ * a * (i⁻¹)⁻¹) = (i⁻¹ * a * (i⁻¹)⁻¹) * z at hh
  have hh' := congrArg (MulAut.conj i) hh
  simpa [MulAut.conj_apply, mul_assoc] using hh'.symm

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (h : Geometry d c) (k : CoreFacts c)

include h k in
private theorem exists_moving_conjugate (D : Subgroup (I c)) (hD : D.IsCComponent) :
    ∃ i : I c, ¬ (D.map (MulAut.conj i).toMonoidHom).map (I c).subtype ≤
      centralizer ({d.z} : Set G) := by
  classical
  by_contra! hall
  have hc : ∀ i ∈ I c, (D.map (I c).subtype).map (MulAut.conj i).toMonoidHom ≤
      centralizer (F.Vi 1 : Set G) := by
    intro i hi
    rw [d.point, zpowers_eq_closure, centralizer_closure]
    have he : (I c).subtype.comp (MulAut.conj (⟨i, hi⟩ : I c)).toMonoidHom =
        (MulAut.conj i).toMonoidHom.comp (I c).subtype := rfl
    simpa only [map_map, he] using hall (⟨i, hi⟩ : I c)
  have hspan := centralizes_span_of_conjugates (D.map (I c).subtype) (F.Vi 1) (I c) hc
  have hcore : D ≤ pCore 2 (I c) := by
    rw [h.core_eq_centralizer k.centralizes]
    intro a ha
    apply mem_centralizer_iff.mpr
    intro v hv
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hspan (mem_map_of_mem _ ha)) (v : G) hv
  let : Group.IsNilpotent D := (pCore_isPGroup.to_le hcore).isNilpotent
  exact hD.not_isSolvable inferInstance

include c k in
private theorem seed_in_omegaCenter : d.z ∈ omegaOneCenterAmbient (T : Subgroup G) := by
  have hz : d.z ∈ F.Vi 1 := d.point ▸ mem_zpowers d.z
  let := k.elementary
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨((F.le_seed 1).trans d.natural.chosen.le_sylow) hz,
      elemPow_eq_one_of_isElementaryAbelian d.z
        (show d.z ∈ VI c from le_conjugateSpanBy _ _ hz),
      fun t ht => (mem_centralizer_iff.mp
        (group_centralizes_point d (mem_sup_right ht)) d.z hz).symm⟩

include d h k in
/-- A conjugate of every lifted C-component belongs to the actual faithful
local family, detected by its action on the original central involution. -/
theorem exists_faithful_conjugate (D : Subgroup (I c)) (hD : D.IsCComponent) :
    ∃ C : Subgroup (I c), C.IsCComponent ∧
      C.map (I c).subtype ∈ MainForward.faithfulLocalComponents T := by
  obtain ⟨i, hi⟩ := exists_moving_conjugate d c h k D hD
  let C := D.map (MulAut.conj i).toMonoidHom
  have hC : C.IsCComponent := hD.map_equiv (MulAut.conj i)
  refine ⟨C, hC, ?_⟩
  apply Chapter13.Section06.CentralizerReduction.ComponentSelection.faithful_of_moving_cComponent
    T (d.counterexample.qtke.evenCharacteristic T) d.z (seed_in_omegaCenter d c k)
    (I c) (C.map (I c).subtype) (Geometry.local_and_sqtk (d := d) (c := c) k.nontrivial).1
    ⟨map_subtype_le C, ?_⟩ hi
  simpa only [subgroupOf, comap_map_eq_self_of_injective (I c).subtype_injective] using hC

include d h k in
/-- Lift through the literal plus map, select a faithful conjugate, and
apply the full universal earlier 14.3.4 contract. -/
theorem smallSubnormal_of_component
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    {B : Subgroup ((I c) ⧸ pCore 2 (I c))} (hB : IsComponent _ B) :
    SmallSubnormal c := by
  let : Group.IsNilpotent (pCore 2 (I c)) := pCore_isPGroup.isNilpotent
  obtain ⟨D, hD, _⟩ := hB.isCComponent.exists_map_quotient_eq (pCore 2 (I c))
  obtain ⟨C, hC, hf⟩ := exists_faithful_conjugate d c h k D hD
  obtain ⟨hloc, hfaith⟩ :=
    (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T (C.map (I c).subtype)).mp hf
  have hclass := (earlier _ hloc hfaith).1
  let e := C.equivMapOfInjective (I c).subtype (I c).subtype_injective
  let eq : (C ⧸ pCore 2 C) ≃* ((C.map (I c).subtype) ⧸ pCore 2 (C.map (I c).subtype)) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let imageEquiv := (cComponentTwoCoreQuotientEquiv hC).symm.trans eq
  refine ⟨C.map (plusMap c), hC.subnormal.map (QuotientGroup.mk'_surjective _), ?_⟩
  rcases hclass with ha | hl
  · obtain ⟨ea⟩ := ha
    exact Or.inr (Or.inr ⟨imageEquiv.trans ea⟩)
  · obtain ⟨el⟩ := hl
    exact Or.inr (Or.inl ⟨imageEquiv.trans (el.trans Matrix.PSL3Two.equiv.symm)⟩)

/-- The first direct factor is a genuine subnormal S₃ in the plus quotient. -/
theorem smallSubnormal_of_symmetricThreePair
    (e : letI := module_elementary d c k
      offenderSubgroup (action d c h k) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : SmallSubnormal c := by
  let := module_elementary d c k
  let J := offenderSubgroup (action d c h k)
  let A := (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (⊥ : Subgroup (Equiv.Perm (Fin 3)))
  let B := A.map e.symm.toMonoidHom
  have hB : B.IsSubnormal := (inferInstance : A.Normal).isSubnormal.map e.symm.surjective
  let ea : A ≃* Equiv.Perm (Fin 3) :=
    ((prodEquiv _ _).trans MulEquiv.prodUnique).trans topEquiv
  let eb : B ≃* Equiv.Perm (Fin 3) :=
    (A.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans ea
  exact ⟨B.map J.subtype, hB.trans' (offenderSubgroup_normal (action d c h k)).isSubnormal,
    Or.inl ⟨(B.equivMapOfInjective J.subtype J.subtype_injective).symm.trans eb⟩⟩

/-- The complete native adequate B.5.6 alternative on the literal restricted
representation produces the small subnormal subgroup required on p.1075.
The only additional earlier input is the full universal 14.3.4(1–2) contract. -/
theorem smallSubnormal_of_adequate
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (alternative : letI := module_elementary d c k
      ChapterB.SourceInduction.NontrivialAdequateAlternative
        ((action d c h k).comp (offenderSubgroup (action d c h k)).subtype)) :
    SmallSubnormal c := by
  let := module_elementary d c k
  let J := offenderSubgroup (action d c h k)
  rcases adequate_group_cases ((action d c h k).comp J.subtype) alternative with
    ⟨B, hB⟩ | he | he
  · let := hB.2
    have hcomp : IsComponent ((I c) ⧸ pCore 2 (I c)) (B.map J.subtype) :=
      ⟨hB.1.trans' (offenderSubgroup_normal (action d c h k)).isSubnormal,
        IsQuasisimple.of_mulEquiv (B.equivMapOfInjective J.subtype J.subtype_injective)⟩
    exact smallSubnormal_of_component d c h k earlier hcomp
  · exact ⟨J, (offenderSubgroup_normal (action d c h k)).isSubnormal, Or.inl he⟩
  · obtain ⟨e⟩ := he
    exact smallSubnormal_of_symmetricThreePair d c h k e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ComponentSelection
