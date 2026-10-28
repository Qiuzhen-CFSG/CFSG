module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalComponents
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.SolvableConclusion
public import Theory.GroupTheory.CComponent.NormalPair
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryBorelKernel
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.NumberTheory.BinaryTorusParity

/-!
# The central cubic of an original component

The component center embeds in the local Fitting subgroup. The original
three-core bound and 14.7.27 identify any nontrivial such center with the
image of L₁, of order three. Two-perfectness lifts containment through O₂(I),
which normalizes the component, and lifts normality of the point residual.
This argument uses only the earlier structural inputs on the same G,T;
the full original-point application retains their multiple-overgroup guard.

The original inverter in T∩L inverts this entire center, so its action on
the intrinsic component quotient is outer. The quotient formulas are
checked on actual component elements. In particular, every even-degree
SL₃ component has this central cubic and this original outer inverter.
Distinguishing the graph action and excluding the resulting module are
subsequent steps of the special-linear branch.

Source: Aschbacher–Smith 14.7.27–28, 14.7.44 and 14.7.47,
printed pp.1054–1055,1062,1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_mk)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A nontrivial component center is precisely the original point cubic,
with containment and normality lifted through the original two-core. -/
theorem local_nontrivial_component_center_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hz : center (C ⧸ pCore 2 C) ≠ ⊥) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let B := C.map q
    F.Li L 1 ≤ C.map I.subtype ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ((F.Li L 1).subgroupOf I).map q = (center B).map B.subtype ∧
      Nat.card (center (C ⧸ pCore 2 C)) = 3 := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let Z := (center B).map B.subtype
  let A := (F.Li L 1).subgroupOf I
  let e := cComponentTwoCoreQuotientEquiv hC
  have hcZ : Nat.card Z = Nat.card (center (C ⧸ pCore 2 C)) := by
    rw [card_map_of_injective B.subtype_injective]
    exact (Nat.card_congr (centerCongr e).toEquiv).symm
  have hZne : Z ≠ ⊥ := by
    intro hb
    apply hz
    apply card_eq_one.mp
    rw [←hcZ,hb]
    exact Nat.card_unique
  have hcomp := WholeResidualAssembly.GuardedSource.local_component_star_isComponent
    h hab structural previous faithful I hI C hC
  have hZP : Z ≤ pCore 3 (HStar I) := by
    rw [←WholeResidualAssembly.GuardedSource.local_fitting_eq_threeCore
      h hab structural previous faithful I hI]
    exact hcomp.center_map_le_fitting
  have hcP : Nat.card (pCore 3 (HStar I)) ≤ 3 :=
    WholeResidualAssembly.GuardedSource.local_threeCore_card_le_three
      d h hab structural previous faithful earlier I hI
  have hZ3 : IsPGroup 3 Z := pCore_isPGroup.to_le hZP
  have hZcard : Nat.card Z = 3 := by
    have hd := card_le_of_le hZP
    obtain ⟨n,hn⟩ := hZ3.exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hZne (card_eq_one.mp (by rw [hn,hn0,pow_zero]))
    have hl : 3 ≤ Nat.card Z := by
      rw [hn]
      exact Nat.le_of_dvd (pow_pos (by decide) _) (dvd_pow_self 3 hn0)
    exact le_antisymm (hd.trans hcP) hl
  have hZeq : Z = pCore 3 (HStar I) := eq_of_le_of_card_ge hZP (by rw [hZcard]; exact hcP)
  have hAeq : A.map q = Z := by
    rcases WholeResidualAssembly.GuardedSource.local_threeCore_eq_bot_or_point
      d h hab structural previous faithful earlier I hI with hb | ha
    · exact (hZne (hZeq.trans hb)).elim
    · exact ha.symm.trans hZeq.symm
  have hAn : A.Normal := by
    apply WholeResidualAssembly.GuardedSource.local_point_normal_of_star_normal h structural I
      (sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI))
    rw [show ((F.Li L 1).subgroupOf I).map q = pCore 3 (HStar I) from hAeq.trans hZeq]
    infer_instance
  have hAp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI)).symm.toMonoidHom
    (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI)).symm.surjective
  have hAC : A ≤ C := isPPerfect_le_of_map_le_of_kernel_normalizes q A C hAp
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (by rw [QuotientGroup.ker_mk']; exact hC.pCore_le_normalizer 2)
    (by rw [hAeq]; exact map_subtype_le _)
  have hin : F.Li L 1 ≤ C.map I.subtype := by
    have hh := map_mono (f := I.subtype) hAC
    rwa [map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hI)] at hh
  exact ⟨hin,hAn,hAeq,hcZ.symm.trans hZcard⟩

/-- The same inverter in T∩L inverts the entire nontrivial component center.
In particular its action on the intrinsic component quotient is outer. -/
theorem local_nontrivial_component_center_inverter
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hz : center (C ⧸ pCore 2 C) ≠ ⊥) :
    ∃ hCN : C.Normal, letI := hCN
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
        let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
        (∀ z ∈ center (C ⧸ pCore 2 C),
          normalQuotientAction C (pCore 2 C) tI z = z⁻¹) ∧
        normalQuotientAction C (pCore 2 C) tI ∉ MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
  obtain ⟨_,hAn,hAZ,hZcard⟩ := local_nontrivial_component_center_at
    d h hab (structural.at T) (previous.at T) faithful earlier I hI C hC hz
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let A := (F.Li L 1).subgroupOf I
  let := hAn
  have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  let hCN : C.Normal := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using
      local_cComponent_normal d h hab structural previous faithful earlier I
        (C.map I.subtype) hI (map_subtype_le _) hC'
  let := hCN
  let e := cComponentTwoCoreQuotientEquiv hC
  obtain ⟨t,hti⟩ := exists_point_core_inverter (F := F) h structural
  let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  let tA : normalizer (F.Li L 1 : Set G) :=
    ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) t.property.1⟩
  have hqA (a : I) (ha : a ∈ A) : q (tI*a*tI⁻¹) = (q a)⁻¹ := by
    let a' : F.Li L 1 := ⟨a,ha⟩
    have he := hti (QuotientGroup.mk' (pCore 2 (F.Li L 1)) a')
    rw [coreAction_mk] at he
    have hp : (F.Li L 1).normalizerMonoidHom tA a' * a' ∈ pCore 2 (F.Li L 1) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 (F.Li L 1)) (_ * _) = 1
      rw [map_mul,he,inv_mul_cancel]
    let ea := (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI)).symm
    have hpA := (pCore_map_iso 2 ea).le (mem_map_of_mem ea.toMonoidHom hp)
    have hpI : tI*a*tI⁻¹*a ∈ pCore 2 I := by
      exact pCoreIn_le_of_subnormal 2 hAn.isSubnormal (mem_map_of_mem A.subtype hpA)
    apply eq_inv_of_mul_eq_one_left
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hpI
  have haction (x : C ⧸ pCore 2 C) :
      (e (normalQuotientAction C (pCore 2 C) tI x) : HStar I) =
        q tI * (e x : HStar I) * (q tI)⁻¹ := by
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C) x
    rw [normalQuotientAction_apply_mk]
    change q (tI*(c : I)*tI⁻¹) = q tI * q (c : I) * (q tI)⁻¹
    rw [map_mul,map_mul,map_inv]
  have hi : ∀ z ∈ center (C ⧸ pCore 2 C),
      normalQuotientAction C (pCore 2 C) tI z = z⁻¹ := by
    intro z hz
    have hez : e z ∈ center B := (centerCongr e ⟨z,hz⟩).property
    have hmem : (e z : HStar I) ∈ A.map q :=
      hAZ.symm ▸ mem_map_of_mem B.subtype hez
    obtain ⟨a,ha,he⟩ := hmem
    apply e.injective
    apply Subtype.ext
    rw [map_inv]
    change (e (normalQuotientAction C (pCore 2 C) tI z) : HStar I) = (e z : HStar I)⁻¹
    rw [haction,←he,←map_inv,←map_mul,←map_mul]
    exact hqA a ha
  refine ⟨hCN,t,hi,?_⟩
  rintro ⟨c,hc⟩
  apply hz
  apply eq_bot_iff.mpr
  intro z hzc
  have hfixed : MulAut.conj c z = z := by
    change c*z*c⁻¹ = z
    rw [mem_center_iff.mp hzc c,mul_inv_cancel_right]
  have hzi : z = z⁻¹ := by rw [hc] at hfixed; exact hfixed.symm.trans (hi z hzc)
  have htwo : z^2 = 1 := by
    rw [pow_two]
    exact (congrArg (z * ·) hzi).trans (mul_inv_cancel _)
  have hthree : z^3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hzc⟩ : center (C ⧸ pCore 2 C)))
    rw [hZcard] at hh
    exact congrArg Subtype.val hh
  simpa [pow_succ,htwo] using hthree

/-- In every even-degree special-linear-three row, the original point is
the scalar center and its original Sylow inverter acts outer. In particular
this supplies the central-cubic premise in the SL₃(4) branch of 14.7.44. -/
theorem local_even_special_linearThree_center_and_inverter
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E]
    {n : ℕ} (hE : Nat.card E = 2^n) (heven : Even n)
    (e : (C ⧸ pCore 2 C) ≃* SL(3,E)) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let B := C.map q
    F.Li L 1 ≤ C.map I.subtype ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ((F.Li L 1).subgroupOf I).map q = (center B).map B.subtype ∧
      ∃ hCN : C.Normal, letI := hCN
        ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
          let α := MulAut.congr e (normalQuotientAction C (pCore 2 C)
            ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩)
          (∀ z ∈ center SL(3,E), α z = z⁻¹) ∧
          α ∉ MulAut.innerSubgroup SL(3,E) := by
  have hzM : center SL(3,E) ≠ ⊥ := by
    intro hzM
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three E).mp hzM
    apply hh
    rw [hE,Nat.BinaryTorusParity.two_pow_mod_three,if_pos (Nat.even_iff.mp heven)]
  have hz : center (C ⧸ pCore 2 C) ≠ ⊥ := by
    intro hz
    apply hzM
    apply card_eq_one.mp
    rw [←Nat.card_congr (centerCongr e).toEquiv,hz]
    exact Nat.card_unique
  obtain ⟨hin,hAn,hAZ,_⟩ := local_nontrivial_component_center_at
    d h hab (structural.at T) (previous.at T) faithful earlier I hI C hC hz
  obtain ⟨hCN,t,hi,hout⟩ := local_nontrivial_component_center_inverter
    d h hab structural previous faithful earlier I hI C hC hz
  let := hCN
  refine ⟨hin,hAn,hAZ,hCN,t,?_,?_⟩
  · intro z hz
    have hz' : e.symm z ∈ center (C ⧸ pCore 2 C) := (centerCongr e.symm ⟨z,hz⟩).property
    change e (normalQuotientAction C (pCore 2 C) _ (e.symm z)) = z⁻¹
    rw [hi _ hz',map_inv,e.apply_symm_apply]
  · rintro ⟨x,hx⟩
    apply hout
    refine ⟨e.symm x,?_⟩
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj,e.apply_symm_apply]
    exact hx

/-- The original full point normalizer satisfies the central-cover reduction
using only the same-G,T guarded earlier inputs. This is the literal consumer
needed before the all-component 14.7.47 assembly. -/
theorem original_nontrivial_component_center_of_many_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (hz : center (C ⧸ pCore 2 C) ≠ ⊥) :
    let q := QuotientGroup.mk' (pCore 2 F.H)
    let B := C.map q
    F.Li L 1 ≤ C.map F.H.subtype ∧
      ((F.Li L 1).subgroupOf F.H).Normal ∧
      ((F.Li L 1).subgroupOf F.H).map q = (center B).map B.subtype ∧
      Nat.card (center (C ⧸ pCore 2 C)) = 3 := by
  exact local_nontrivial_component_center_at d h hab (structural hmany) (previous hmany)
    faithful earlier F.H (h.point_mem_Hz_at F (previous hmany)) C hC hz

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
