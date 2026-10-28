module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCenterMovement
public import Theory.GroupTheory.ElementaryThompsonFixedIndex
public import Theory.Representation.BinaryConjugationSection.OffenderQuotientIndex
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# Center control in the original Heisenberg branch

The moved center D = [Z(O₂(K)),K], if nontrivial, is the actual faithful
six-dimensional chief factor constructed in ExtraspecialCenterMovement.
Its coordinates have trivial kernel, and its H-action has kernel exactly
O₂(H).

Every elementary subgroup of the point-core image has order at most two
and centralizes the point cubic. The latter acts without fixed points on
the chief module. Both the whole module and each such actor's fixed space
therefore have even dimension, excluding an FF offender. The maximum
elementary subgroup index bound now puts J(R₁) in O₂(H). Consequently
D lies in Ω₁(Z(J(R₁))), so Baum(R₁) lies in C_H(D) = O₂(H).
Baumann heredity gives Baum(R₁) = Baum(O₂(H)), normalized by H.
This contradicts the original Baumann-normalizer bound of 14.7.16(7).
Thus the whole center of O₂(K) is central in K.

This proves the center clause 14.7.21(2) of Aschbacher–Smith, printed
p.1050, refs/quasithin.pdf. The maximal-overgroup clause 14.7.21(1)
and the subsequent residual exclusion remain separate source steps.
The genuine earlier structural, faithful-classification and 14.7.10
inputs remain explicit with their existing producers; their final
source discharge belongs to qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

private theorem centerControl_not_offender {X W : Type*} [Group X]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) X W) (hf : Function.Injective σ)
    (Z A : Subgroup X) (hZ : IsPGroup 3 Z)
    (hz : invariants (σ.comp Z.subtype) = ⊥)
    (hc : A ≤ centralizer (Z : Set X)) (hcard : Nat.card A ≤ 2) : ¬ IsOffender σ A := by
  intro hA
  let I : Subrepresentation (σ.comp Z.subtype) := {
    toSubmodule := fixedSpace σ A
    apply_mem_toSubmodule z v hv a := by
      change σ a (σ z v)=σ z v
      have he := congrArg (fun x => σ x v) (hc a.property z z.property)
      simp only [map_mul,Module.End.mul_apply] at he
      rw [←he]
      exact congrArg (σ z) (hv a) }
  have hI : invariants I.toRepresentation = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    have hh : (v : W) ∈ invariants (σ.comp Z.subtype) :=
      fun z => congrArg Subtype.val (hv z)
    change (v : W) = 0
    simpa only [hz,Submodule.mem_bot] using hh
  have hdim := orderOf_two_dvd_finrank_of_isPGroup (σ.comp Z.subtype)
    Nat.prime_three (by decide) hZ hz
  have hfixed := orderOf_two_dvd_finrank_of_isPGroup I.toRepresentation
    Nat.prime_three (by decide) hZ hI
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at hdim hfixed
  have heq := fixedCodim_add_finrank σ A
  have hpos := fixedCodim_pos_of_faithful σ hf hA.1.1
  have hr : rank A ≤ 1 := by
    simpa only [rank,show Nat.log 2 2 = 1 from rfl] using
      (Nat.log_mono_right (b := 2) hcard)
  have hb := hA.2
  change 2 ∣ Module.finrank (ZMod 2) (fixedSpace σ A) at hfixed
  omega

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem centerControl_point_not_offender
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W) [σ.IsIrreducible]
    (hf : Function.Injective σ) (A : Subgroup (HStar F.H))
    (hAR : A ≤ star F (F.Ri L 1)) : ¬ IsOffender σ A := by
  intro hA
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  let Z := star F (F.Li L 1)
  let : Z.Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZcard : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hn
  have hZ : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hz : invariants (σ.comp Z.subtype) = ⊥ := by
    by_contra hfix
    have hk := le_ker_of_normal_invariants_ne_bot σ Z hfix
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf] at hk
    have hb : Z = ⊥ := le_bot_iff.mp hk
    rw [hb,Nat.card_unique] at hZcard
    contradiction
  have hsmall : Nat.card A ≤ 2 := by
    let := hA.1.2
    have ha := (primeRank_le_iff_elementary_card_le (star F (F.Ri L 1))).mp
      (point_core_rank_one_of_extraspecial_residual h structural hex hcard)
      (A.subgroupOf (star F (F.Ri L 1))) (IsElementaryAbelian.subgroupOf hAR)
    simpa only [Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv,pow_one] using ha
  exact centerControl_not_offender σ hf Z A hZ hz
    (hAR.trans (point_core_star_centralizes_of_normal h structural hn)) hsmall hA


private theorem centerControl_baumann_eq
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W) [σ.IsIrreducible]
    (hf : Function.Injective σ) (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hDQ : D ≤ F.H.pCoreIn 2)
    (hn : F.H ≤ normalizer (D : Set G))
    (hker : (D.normalizerMonoidHom.comp (inclusion hn)).ker = pCore 2 F.H)
    (s : BinaryConjugationSection F.H D ⊥ (σ.comp (starMap F))) :
    ChapterB.baumann (F.Ri L 1) = ChapterB.baumann (F.H.pCoreIn 2) := by
  have hkerC : (centralizer (D : Set G)).subgroupOf F.H = pCore 2 F.H := by
    rw [←hker,←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  have hQC : F.H.pCoreIn 2 = F.H ⊓ centralizer (D : Set G) := by
    change (pCore 2 F.H).map F.H.subtype = _
    rw [←hkerC,subgroupOf_map_subtype,inf_comm]
  have hDC : D ≤ centralizer (F.H.pCoreIn 2 : Set G) := by
    apply le_centralizer_iff.mp
    rw [hQC]
    exact inf_le_right
  have hRQ : F.H.pCoreIn 2 ≤ F.Ri L 1 := core_le_point_core
  have hRH : F.Ri L 1 ≤ F.H := (pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hJ : Stellmacher.elementaryAbelianMaxJ (F.Ri L 1) ≤ F.H.pCoreIn 2 := by
    apply sSup_le
    intro A hA
    by_contra hAQ
    let : IsElementaryAbelian 2 A := hA.2.1
    have hAH : A ≤ F.H := hA.1.trans hRH
    have hEA : IsElementaryTwo (star F A) := by
      let : IsElementaryAbelian 2 (A.subgroupOf F.H) := IsElementaryAbelian.subgroupOf hAH
      refine ⟨?_,IsElementaryAbelian.map (starMap F)⟩
      intro hb
      have hh : A.subgroupOf F.H ≤ pCore 2 F.H := by
        simpa only [CriticalFusion.Source.star,Subgroup.map_eq_bot_iff,starMap,QuotientGroup.ker_mk'] using hb
      apply hAQ
      change A ≤ (pCore 2 F.H).map F.H.subtype
      simpa only [map_subgroupOf_eq_of_le hAH] using map_mono (f := F.H.subtype) hh
    have hi : (centralizer (A : Set G)).relIndex D ≤ Nat.card (star F A) := by
      have hh := Stellmacher.maxElementary_fixedIndex_le_relIndex (F.Ri L 1)
        (F.H.pCoreIn 2) A D hRQ hDQ hDC hA
      apply (hh.1.trans hh.2).trans_eq
      change _ = Nat.card ((A.subgroupOf F.H).map (starMap F))
      rw [←relIndex_ker,show (starMap F).ker = pCore 2 F.H from QuotientGroup.ker_mk' _]
      have hc : (F.H.pCoreIn 2).subgroupOf F.H = pCore 2 F.H :=
        comap_map_eq_self_of_injective F.H.subtype_injective _
      rw [←hc,relIndex_subgroupOf hAH]
    have ho := s.offender_of_section_index σ (starMap F) A (centralizer (A : Set G))
      (by rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr le_rfl]) hEA hi
    exact centerControl_point_not_offender h hab structural previous he σ hf (star F A)
      (map_mono (subgroupOf_mono _ hA.1)) ho
  have hDα := Stellmacher.elementary_centralizer_maxJ_le_omegaCenter (F.Ri L 1) D
    (hDQ.trans hRQ) (hDC.trans (centralizer_le hJ))
  have hB : ChapterB.baumann (F.Ri L 1) ≤ F.H.pCoreIn 2 := by
    rw [hQC]
    exact le_inf (inf_le_left.trans hRH) (inf_le_right.trans (centralizer_le hDα))
  exact (Stellmacher.baumann_eq_of_intermediate (F.Ri L 1) (F.H.pCoreIn 2) hB hRQ).symm

open NoncentralChiefRefinement in
/-- The source center conclusion, for the original Heisenberg residual. -/
theorem extraspecial_core_center_central
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype ≤
      (center (K F)).map (K F).subtype := by
  by_contra hnc
  obtain ⟨N,B,hNB,hUN,hBC,hm,_,_,hDB,_,_,hDe,hn,hker,e,heq⟩ :=
    extraspecial_noncentral_core_center h hab structural previous faithful he hnc
  let D := ⁅(center ((K F).pCoreIn 2)).map ((K F).pCoreIn 2).subtype,K F⁆
  let : IsElementaryAbelian 2 D := hDe
  let : IsElementaryAbelian 2 (Section N B) := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let ρ := binarySectionRepresentation N B
  let s := ambientBinarySection F.H N B hNB.le
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  have hecopy := he
  obtain ⟨ee⟩ := hecopy
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv ee.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr ee.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv ee).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ,hfaith,_,_⟩ := extraspecial_point_noncentral_chief h hab structural previous
    hex hcard hexp hBC hUN s hm
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (starMap F) (QuotientGroup.mk'_surjective _) σ).mp
      (hσ.symm ▸ inferInstanceAs ρ.IsIrreducible)
  have hDH : D ≤ F.H := hDB.trans (map_subtype_le _)
  let sd : BinaryConjugationSection F.H D ⊥ (σ.comp (starMap F)) := {
    section_le := hDH
    kernel_le := bot_le
    normalized := hn
    coordinates := {
      toFun := fun x => Multiplicative.ofAdd (Additive.ofMul (e x))
      map_one' := e.map_one
      map_mul' := e.map_mul }
    onto := e.surjective
    kernel_eq := by
      ext x
      change e x = 1 ↔ (x : G) = 1
      exact e.map_eq_one_iff.trans Subtype.val_inj.symm
    equivariant := by
      intro a x
      rw [hσ]
      exact congrArg Additive.ofMul (heq a x) }
  have hDQ : D ≤ F.H.pCoreIn 2 := by
    let := h.chosen.elementary
    let := hab
    let := elementary_U F
    obtain ⟨ρ₀,⟨s₀⟩⟩ := exists_section F
    exact hDB.trans (hBC.trans
      (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) s₀))
  have hBaum := centerControl_baumann_eq h hab structural previous he σ hfaith D hDQ hn hker sd
  apply h.flag_escape F previous
  apply le_trans ?_ (extraspecial_baumann_normalizer d h hab structural previous earlier he)
  rw [hBaum]
  exact (F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))).trans
      (Stellmacher.normalizer_le_normalizer_baumann _)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
