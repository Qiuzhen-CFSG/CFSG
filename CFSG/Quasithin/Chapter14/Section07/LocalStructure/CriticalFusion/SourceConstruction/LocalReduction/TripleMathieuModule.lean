module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuAction
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.Sporadic.TripleWhole

/-!
# Whole-section recognition in the reduced triple-Mathieu local

The quadratic actor cannot invert the normal point cubic: that would force
binary dimension at most four, contradicting the faithful minimum of twelve.
The proved point-centralizer identity therefore puts this actor in the actual
triple-cover component image. Its central cubic is fixed-free on the whole
literal U_I/V₁ section. Whole-module recognition now proves irreducibility,
degree twelve and an actual intertwiner, including the no-rank-two conclusion
for every ambient involution. The final theorem applies this to the original
component's constructed C T reduction, with the quotient maps unchanged.

The Sylow fixed line and escaping solvable overgroup still require their
source geometry. This module does not assert the triple-cover exclusion.
Source: Aschbacher–Smith 14.7.36, printed p.1059; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.RankTwo
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u
open scoped IsMulCommutative
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Recognition of the entire given action, including every ambient involution. -/
@[expose] def TripleMathieuAction {H : Type*} [Group H]
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (B : Subgroup H) : Prop :=
  IsIrreducible (ρ.comp B.subtype) ∧ Module.finrank (ZMod 2) E = 12 ∧
    ∃ eB : B ≃* Sporadic.Mathieu.M22TripleCover,
      Nonempty (Representation.Equiv (ρ.comp B.subtype)
        (Sporadic.Mathieu.M22TripleCover.representationOfEquiv eB)) ∧
      (∀ t : H, t ^ 2 = 1 → Module.finrank (ZMod 2) (movedSpace ρ t) ≠ 2)

/-- The whole literal section of the reduced triple-Mathieu local is the
faithful irreducible twelve-dimensional module, with its actual component
isomorphism and intertwiner. No degree or irreducibility input is required. -/
theorem reduced_triple_mathieu_module
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    let B := C.map (QuotientGroup.mk' (pCore 2 I))
    ∃ hU : IsElementaryAbelian 2 (F.UH I), let := hU
      ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        TripleMathieuAction a.representation B := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let X := ((F.Li L 1).subgroupOf I).map q
  obtain ⟨hnB,⟨eB⟩,_,_,hpn,hz⟩ := reduced_triple_mathieu_star_structure
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hnB
  let := hpn
  let hnX : X.Normal := hpn.map q (QuotientGroup.mk'_surjective _)
  obtain ⟨hU,a,_,hd,_,_,A,hAR,hA,hq,hb,_⟩ := reduced_triple_mathieu_action
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hU
  let W := Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))
  let : Nontrivial W := Module.nontrivial_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 12) hd)
  let zB := eB.symm Sporadic.Mathieu.M22TripleCover.scalar
  let z : HStar I := zB
  have hcX : Nat.card X = 3 :=
    local_point_star_card_of_normal h structural I (F.Li_one_le_of_mem_Hz hI) hpn
  have hoz : orderOf z = 3 := (orderOf_injective B.subtype B.subtype_injective zB).trans
    (Sporadic.Mathieu.M22TripleCover.scalar_order_of_equiv eB)
  have hzX : z ∈ X := by
    change X = (center B).map B.subtype at hz
    rw [hz]
    exact mem_map_of_mem B.subtype
      (Sporadic.Mathieu.M22TripleCover.scalar_mem_center_of_equiv eB)
  have hzx : zpowers z = X := eq_of_le_of_card_ge (zpowers_le.mpr hzX)
    (by rw [Nat.card_zpowers,hoz,hcX])
  have hfree : ∀ v, a.representation z v = v → v = 0 := by
    intro v hv
    have hf : v ∈ fixedSpace a.representation (zpowers z) :=
      (mem_fixedSpace_zpowers_iff _ _ _).mpr hv
    rw [hzx,local_point_fixedSpace_eq_bot h structural I
      (F.Li_one_le_of_mem_Hz hI) hpn a] at hf
    exact hf
  have hpoly := Representation.RankTwo.quadratic_of_cubic_fixed_free (a.representation z)
    (show a.representation z ^ 3 = 1 by
      rw [←map_pow,show z ^ 3 = 1 from by simpa only [hoz] using pow_orderOf_eq_one z,map_one]) hfree
  have hmove : subspaceCommutator a.representation ⊤ X = ⊤ := by
    have hinj : Function.Injective (a.representation z - 1 : W →ₗ[ZMod 2] W) := by
      apply LinearMap.ker_eq_bot.mp
      apply bot_unique
      intro v hv
      exact hfree v (sub_eq_zero.mp hv)
    have hs := LinearMap.surjective_of_injective hinj
    apply top_unique
    intro v _
    obtain ⟨w,rfl⟩ := hs v
    exact Submodule.subset_span ⟨z,hzX,w,Submodule.mem_top,rfl⟩
  change fixedCodim a.representation (A.map q) ≤ 2 * rank (A.map q) at hb
  have hAC : A.map q ≤ centralizer (X : Set (HStar I)) := by
    by_contra hn
    obtain ⟨hr,he⟩ := normalThree_quadratic_rank_fixedCodim a.representation a.faithful
      X hnX hcX hmove (A.map q) hA hq hn
    omega
  have hAB : A.map q ≤ B := by
    rwa [reduced_triple_mathieu_point_centralizer d h hab structural previous faithful earlier
      I hI C hC e hgen] at hAC
  let A₀ := (A.map q).subgroupOf B
  let σ := a.representation.comp B.subtype
  let : IsElementaryAbelian 2 (A.map q) := hA.2
  have hA₀ : IsElementaryTwo A₀ := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAB⟩
    intro hh
    apply hA.1
    rw [←map_subgroupOf_eq_of_le hAB,show (A.map q).subgroupOf B = ⊥ from hh,Subgroup.map_bot]
  have hb₀ : fixedCodim σ A₀ ≤ 2 * rank A₀ := by
    rw [fixedCodim_subgroupOf a.representation hAB,rank_subgroupOf hAB]
    exact hb
  obtain ⟨hi,hdim,⟨E⟩⟩ :=
    ChapterB.SmallRatioClassification.Sporadic.triple_polynomial_recognition eB
    ((local_star_sqtk h I hI).subgroup B) σ hpoly A₀ hA₀
    (fun x hx y hy v => hq x hx y hy v) hb₀
  exact ⟨hU,a,hi,hdim,eB,⟨E⟩,fun t ht =>
    Representation.RankTwo.TripleCover.no_rank_two_of_component_equiv
      a.representation B eB E t ht⟩

/-- Apply whole-section recognition to the original component's actual C T
reduction. The same quotient maps, component image and binary section are
retained, including the exclusion of rank-two displacement for every involution. -/
theorem original_triple_mathieu_reduced_module
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) :
    let D := C.map F.H.subtype
    let J := D ⊔ (T : Subgroup G)
    let B := (D.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
    J ≤ F.H ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH J), let := hU
        ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
          TripleMathieuAction a.representation B := by
  let D := C.map F.H.subtype
  let J := D ⊔ (T : Subgroup G)
  obtain ⟨hJH,hJ,hDJ,_,_,_,_,_,_,_,_⟩ :=
    original_triple_mathieu_reduced_residual d h hab structural previous faithful earlier C hC e
  let b := equivMapOfInjective C F.H.subtype F.H.subtype_injective
  let eD := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans e
  let c := subgroupOfEquivOfLe (show D ≤ J from le_sup_left)
  let eJ := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans eD
  have hg : D.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show D ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  exact ⟨hJH,hJ,reduced_triple_mathieu_module
    d h hab structural previous faithful earlier J hJ (D.subgroupOf J) hDJ eJ hg⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
