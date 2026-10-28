module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedPoint
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.InvolutionRank
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.Source
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# The original flag in the rank and centralizer arguments

The central quotient of U inside H is identified with the original U/Z(U),
and the action is transported through the proved equality of its kernel
with O₂(H). The literal subgroup images agree with the original hat spaces.
Applying the marked model inspection therefore gives 14.4.6 on the original
flag, and excludes the low-rank alternative in its G.11 fixed-space clause.

Applying 12.8.9(5) at the inverse of the original conjugator supplies the
symmetric quotient-action kernel. Together with the original line,
hyperplane and displaced centers, this constructs every field of the
EarlierGeometry used in the first paragraph of 14.4.7. Extraspeciality gives
Qᵍ = Uᵍ C_{Hᵍ}(Uᵍ), and the marked action gives the literal centralizer
containment and commutator bounds. Orthogonal.FlagAction applies these
results to the natural Ω₄⁺(4) row without any additional geometric input.

This does not prove U=O₂(H). The residual-generation and natural-complement
construction, the orthogonal selected involution and the exhaustive marked
catalogue remain source obligations. The model alternative here is an
explicit action hypothesis, not a classification theorem.

Source: Aschbacher--Smith, 12.8.9(5), G.11.1(3), 14.4.2(3--6),
14.4.6--7, printed pp.853,364,1006--1009.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (F : InvariantFlag T V 3) [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
local instance : (F.U.subgroupOf F.H).Normal := F.U_normal

/-- The faithful two-core quotient action on the original central quotient. -/
@[expose] noncomputable def sourceAction
    (hk : F.terminalHatAction.ker = pCore 2 F.H) :
    RankCore.SourceAction F.H (F.U.subgroupOf F.H) (Additive F.Uhat) := by
  let e := subgroupOfEquivOfLe F.U_le_H
  let c := QuotientGroup.congr _ _ e (Theory.GroupTheory.map_center_equiv e)
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  refine ⟨c, F.terminalRepresentation.comp q.toMonoidHom,
    F.terminalRepresentation_injective.comp q.injective, ?_⟩
  intro h a
  change Additive.ofMul (c (QuotientGroup.mk' _ (MulAut.conjNormal h a))) =
    F.terminalRepresentation (q (QuotientGroup.mk' _ h)) (Additive.ofMul (c (QuotientGroup.mk' _ a)))
  simp only [c]
  change Additive.ofMul (QuotientGroup.mk' (center F.U) (e (MulAut.conjNormal h a))) =
    Additive.ofMul (F.uhatAction h (QuotientGroup.mk' (center F.U) (e a)))
  rw [F.uhatAction_apply_mk]
  rfl

omit [Finite G] in
/-- Quotient representatives retain their original flag coordinates. -/
theorem sourceAction_vector
    (hk : F.terminalHatAction.ker = pCore 2 F.H) (a : F.U.subgroupOf F.H) :
    (sourceAction F hk).vector a = hatElement F (subgroupOfEquivOfLe F.U_le_H a) := rfl

omit [Finite G] in
/-- The relative subgroup image is the literal hat space of the original flag. -/
theorem sourceAction_image
    (hk : F.terminalHatAction.ker = pCore 2 F.H) (A : Subgroup G) :
    (sourceAction F hk).image (A.subgroupOf F.H) = hatSpace F A := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨a,ha,rfl⟩
    exact ⟨subgroupOfEquivOfLe F.U_le_H a,ha,rfl⟩
  · intro v hv
    obtain ⟨a,ha,rfl⟩ := (show v.toMul ∈ hatImage F A from hv)
    exact Submodule.subset_span ⟨(subgroupOfEquivOfLe F.U_le_H).symm a,ha,rfl⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension
universe u w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (F : InvariantFlag T V 3) [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
local instance : (F.U.subgroupOf F.H).Normal := F.U_normal

/-- The model rank obstruction at the original Sylow-invariant flag line. -/
theorem sourceAction_rank_obstruction
    (hk : F.terminalHatAction.ker = pCore 2 F.H)
    (hc : V ⊓ F.ZU = F.Vi 1)
    (models : RankCore.ActionAlternative.{w} (sourceAction F hk))
    (a : F.H ⧸ pCore 2 F.H) (ha : orderOf a = 2) :
    2 < (sourceAction F hk).movedRank a ∨
      ((sourceAction F hk).movedRank a = 2 ∧
        ¬ hatSpace F (F.Vi 2) ≤ (sourceAction F hk).moved a) := by
  have hn : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H) ≤
      normalizer ((F.Vi 2).subgroupOf F.H : Set F.H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp (F.invariant 2 ht) (v : G)
  have hd : finrank (ZMod 2) ((sourceAction F hk).image ((F.Vi 2).subgroupOf F.H)) = 1 := by
    rw [sourceAction_image]
    exact finrank_hatSpace_plane F (by decide) hc
  simpa only [sourceAction_image] using
    (sourceAction F hk).rank_obstruction models (T.subtype (F.invariant 1))
      ((F.Vi 2).subgroupOf F.H) hn hd a ha

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry


open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem conjugate_mem_iff (A : Subgroup G) (g w : G) :
    w ∈ conjugate A g ↔ MulAut.conj g w ∈ A := by
  change w ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  rw [mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv, MulAut.conj_apply]

/-- The symmetric form of the literal 12.8.9(5) kernel. -/
theorem source_symmetric_quotient_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    RankCore.CentralizerGeometry.QuotientKernel F.U (conjugate F.U g) (F.Vi 2) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  have hc := (source_closure d earlier hq chosen structural alternatives F hne).2.2
  have hgiP := (F.P L).inv_mem hgP
  have hgiH : g⁻¹ ∉ F.H := fun hg => hgH (inv_mem_iff.mp hg)
  have hgi := F.P_le_G₂ (by decide) L chosen.normalizes hgiP
  have hk := (F.binary_source_parabolic_action_clauses (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural)
    hcomm hsquare hspan hne hc g⁻¹ hgiP hgiH).2.1.1
  have hX : RankCore.CentralizerGeometry.W (conjugate F.U g) (F.Vi 2) = F.X g := by
    have hgn := F.P_le_G₂ (by decide) L chosen.normalizes hgP
    change conjugate F.U g ⊓ centralizer (F.Vi 2 : Set G) = conjugate F.W g
    rw [W, conjugate_inf]
    congr 1
    apply Eq.symm
    exact (conjugate_eq_iff _ g).mpr ((normalizer_le_normalizer_centralizer _) hgn)
  have hz : RankCore.CentralizerGeometry.Z (conjugate F.U g) = conjugate F.ZU g :=
    centerIn_conjugate F.U g
  intro w hw
  rw [hz,hX]
  change (∀ u ∈ conjugate F.U g, ⁅w,u⁆ ∈ conjugate F.ZU g) ↔ w ∈ F.W ⊓ F.X g
  have hw' : MulAut.conj g w ∈ F.X g⁻¹ := by
    change MulAut.conj g w ∈ F.W.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
    rw [inv_inv]
    exact mem_map_of_mem _ hw
  have criterion : (∀ u ∈ conjugate F.U g, ⁅w,u⁆ ∈ conjugate F.ZU g) ↔
      MulAut.conj g w ∈ F.E g⁻¹ := by
    rw [← hk, F.mem_xHatKernel]
    constructor
    · intro hh
      refine ⟨hw', ?_⟩
      intro a ha
      have hm : MulAut.conj g⁻¹ a ∈ conjugate F.U g := mem_map_of_mem _ ha
      have he := (conjugate_mem_iff F.ZU g _).mp (hh _ hm)
      simpa [map_commutatorElement, MulAut.conj_apply, mul_assoc] using he
    · rintro ⟨_,hh⟩ u hu
      apply (conjugate_mem_iff F.ZU g _).mpr
      rw [map_commutatorElement]
      exact hh _ ((conjugate_mem_iff F.U g u).mp hu)
  rw [criterion]
  change (MulAut.conj g w ∈ F.W ∧ MulAut.conj g w ∈ F.X g⁻¹) ↔
    (w ∈ F.W ∧ w ∈ F.X g)
  constructor
  · rintro ⟨hh,_⟩
    exact ⟨hw,(conjugate_mem_iff F.W g w).mpr hh⟩
  · rintro ⟨_,hh⟩
    exact ⟨(conjugate_mem_iff F.W g w).mp hh,hw'⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension
universe u w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- All preceding 12.8 geometry in the first paragraph of 14.4.7 is supplied
by the original flag, including the symmetric action kernel. -/
@[expose] def earlierGeometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.CentralizerGeometry.EarlierGeometry (V := Additive F.Uhat)
      F.H F.U (F.Vi 1) (F.Vi 2) L g := by
  let := chosen.elementary
  let := F.U_normal
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  have hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  have hcomm := (source_commutator_squares d earlier hq chosen structural alternatives F).1
  let B := F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  refine {
    U_le_H := F.U_le_H
    H_eq_centralizer := ?_
    center_eq := hZ
    V₂_le_U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
    A_le_V₂ := F.monotone (by decide)
    g_normalizes := F.P_le_G₂ (by decide) L chosen.normalizes hgP
    g_mem_L := hg
    g_not_mem_H := hgH
    disjoint := ?_
    quotient_kernel := source_symmetric_quotient_kernel d earlier hq chosen
      structural alternatives F hne g hgP hgH
    action := sourceAction F hk
    hyperplane := ?_
    line := ?_ }
  · have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    exact le_antisymm (normalizer_le_centralizer_of_card_two _ hc) (Subgroup.centralizer_le_normalizer _)
  · have hh := F.conjugate_point_inf_ZU (by decide) c.seed_center g (chosen.normalizes hg) hgH
    simpa only [hZ, inf_comm, RankCore.CentralizerGeometry.conjugate,
      Chapter12.Section08.conjugate] using hh
  · rw [sourceAction_image]
    exact F.finrank_quotient_hat_centralizer (by decide) c.seed_center B
  · rw [sourceAction_image]
    exact finrank_hatSpace_plane F (by decide) c.seed_center

/-- The marked 14.4.2 action gives the actual centralizer bounds from the
original flag. Neither U=O₂(H) nor a chosen involution is assumed. -/
theorem source_centralizer_bounds (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (models : letI := chosen.elementary
      letI := F.U_normal
      RankCore.ActionAlternative.{w} (sourceAction F
        (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ))) :
    let D := conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)
    D ≤ F.H.pCoreIn 2 ∧ ⁅D,F.U⁆ ≤ F.Vi 1 ∧ ⁅D,F.W⁆ = ⊥ := by
  let := chosen.elementary
  let := F.U_normal
  let e := earlierGeometry d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  have hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  have heact : e.action = sourceAction F hk := rfl
  have hr : ∀ a : F.H ⧸ pCore 2 F.H, orderOf a = 2 →
      2 < e.action.movedRank a ∨ (e.action.movedRank a = 2 ∧
        ¬ e.action.image ((F.Vi 2).subgroupOf F.H) ≤ e.action.moved a) := by
    intro a ha
    rw [heact, sourceAction_image]
    exact sourceAction_rank_obstruction F hk
      (source_closure d earlier hq chosen structural alternatives F hne).2.2 models a ha
  exact e.centralizer_bounds hr

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension
universe u w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original extraspecial closure splits the conjugate two-core as the
product of its conjugate with the literal centralizer. -/
theorem source_conjugate_core_product (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate (F.H.pCoreIn 2) g = conjugate F.U g ⊔
      (conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)) := by
  let := chosen.elementary
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point (by decide) c.two c.frattini_point
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  let := F.U_normal
  exact (earlierGeometry d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH).core_lift

/-- The low-rank alternative in G.11.1(3) cannot occur in any marked large
source row. The remaining fixed space is exactly the original flag line. -/
theorem source_fixed_space_of_marked_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (models : letI := chosen.elementary
      letI := F.U_normal
      RankCore.ActionAlternative.{w} (sourceAction F
        (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ))) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) := by
  let := chosen.elementary
  let := F.U_normal
  have hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  obtain ⟨_,hx,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := hx
  rcases source_terminal_fixed_point_alternative d earlier hq chosen structural alternatives
      F hne g hgP hgH v hline with hf | ⟨a,hane,hr,hm⟩
  · exact hf.trans hline
  · have ha2 : (a : F.TerminalHdot)^2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (F.terminalDot (F.X g))) a)
    have ha : orderOf (a : F.TerminalHdot) = 2 := orderOf_eq_prime_iff.mpr
      ⟨ha2,fun he => hane (Subtype.ext he)⟩
    have hqa : orderOf (q.symm a) = 2 := (q.symm.orderOf_eq a).trans ha
    have he : (sourceAction F hk).representation (q.symm a) = F.terminalRepresentation a := by
      change F.terminalRepresentation (q (q.symm a)) = _
      rw [q.apply_symm_apply]
    have hr' : (sourceAction F hk).movedRank (q.symm a) ≤ 2 := by
      change finrank (ZMod 2) (LinearMap.range
        ((sourceAction F hk).representation (q.symm a) - LinearMap.id)) ≤ 2
      have heR : (sourceAction F hk).moved (q.symm a) =
          LinearMap.range (F.terminalRepresentation a - LinearMap.id) := by
        simp only [RankCore.SourceAction.moved, he]
      exact (LinearEquiv.ofEq _ _ heR).finrank_eq.le.trans hr
    have hm' : hatSpace F (F.Vi 2) ≤ (sourceAction F hk).moved (q.symm a) := by
      rw [← hline]
      apply Submodule.span_le.mpr
      intro z hz
      have hz : z = v := hz
      rw [hz]
      change v ∈ LinearMap.range ((sourceAction F hk).representation (q.symm a) - LinearMap.id)
      rw [he]
      exact hm
    rcases sourceAction_rank_obstruction F hk
        (source_closure d earlier hq chosen structural alternatives F hne).2.2
        models (q.symm a) hqa with hrank | ⟨_,hout⟩
    · omega
    · exact (hout hm').elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CoreGeometry
