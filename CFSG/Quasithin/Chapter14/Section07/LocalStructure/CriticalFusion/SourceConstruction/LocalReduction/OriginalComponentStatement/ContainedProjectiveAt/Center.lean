module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.Borel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.NonnormalAt
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Nontrivial component centers at the fixed original Sylow

A nonnormal original component has binary PSL₂ quotient and hence trivial
center. Thus a nontrivial center forces normality. The existing same-G,T
center theorem identifies it with the actual point cubic; its original
Sylow inverter inverts this center and is outer.
Source: Aschbacher--Smith 14.7.28,32,44, printed pp.1055--1062.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_mk coreAction_eq_one_iff)
open AlternatingSevenSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem local_nontrivial_component_center_normal_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hz : center (C ⧸ pCore 2 C) ≠ ⊥) : C.Normal := by
  by_contra hn
  obtain ⟨n,_,E,_,_,hE,⟨e⟩⟩ := local_nonnormal_component_binary_at
    d h hab structural previous faithful earlier I hI C hC hn
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  apply hz
  apply card_eq_one.mp
  rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot]
  exact Nat.card_unique

/-- The same inverter in T∩L inverts the entire nontrivial component center.
In particular its action on the intrinsic component quotient is outer. -/
theorem local_nontrivial_component_center_inverter_at
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
    ∃ hCN : C.Normal, letI := hCN
      ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
        let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
        (∀ z ∈ center (C ⧸ pCore 2 C),
          normalQuotientAction C (pCore 2 C) tI z = z⁻¹) ∧
        normalQuotientAction C (pCore 2 C) tI ∉ MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
  obtain ⟨_,hAn,hAZ,hZcard⟩ := local_nontrivial_component_center_at
    d h hab structural previous faithful earlier I hI C hC hz
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let A := (F.Li L 1).subgroupOf I
  let := hAn
  let hCN : C.Normal := local_nontrivial_component_center_normal_at
    d h hab structural previous faithful earlier I hI C hC hz
  let := hCN
  let e := cComponentTwoCoreQuotientEquiv hC
  obtain ⟨t,hti⟩ := AlternatingSevenSource.exists_point_core_inverter_at (F := F) h structural
  let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  let tA : normalizer (F.Li L 1 : Set G) :=
    ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) t.property.1⟩
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
  apply _root_.eq_bot_iff.mpr
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
theorem local_even_special_linearThree_center_and_inverter_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    d h hab structural previous faithful earlier I hI C hC hz
  obtain ⟨hCN,t,hi,hout⟩ := local_nontrivial_component_center_inverter_at
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


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
