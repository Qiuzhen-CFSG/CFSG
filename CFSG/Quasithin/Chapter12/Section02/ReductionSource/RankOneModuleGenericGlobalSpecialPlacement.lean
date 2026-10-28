module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2RootPair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityRootPair

/-!
# The two special-core placements in the chosen-module setup

For G₂ and genuine triality, the actual marked root pair supplies U with
Φ(U) = Z(K). Its centralization of a fused root and the elementary
rank-one Sylow quotient permit the two source Sylow conjugations. Both
placements use one final representative. The second conjugator is retained
on the involution, root pair and mover; the mover then lies in the conjugate
of the original S, which is not asserted to equal S.

The remaining source premise C_T(Z(K)) ≤ S is explicit. Proving it, and
recovering movement in the original S after the second conjugation, remain
with the generic-global assembly. These conditional placements do not
establish nonfusion or ambient recognition. Original uniqueness and the
actual compatible amalgam comparison also remain inputs.
Source: Aschbacher–Smith F.4.35, printed p.292, and the Chapter12 application
on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Construct both source placements for the actual g2 root pair, retaining
the unresolved Sylow-centralizer identity and the changed representative. -/
theorem rankOne_global_g2_special_core_placements
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse))
    (hCS : (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ Global.sourceS L H) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q,
      (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val = v ∧ (e.right w).val = Atlas.G2.rootC (1 : F)) ∧
      v ∉ Z ∧ orderOf v = 2 ∧ (∃ x ∈ Global.sourceS L H, ⁅x,v⁆ ∉ Z) ∧
      ∃ r s : G,
      let U := Z.conjBy r ⊔ Z.conjBy s
      U ≤ Q ∧ (frattini U).map U.subtype = Z ∧
      ∀ g : G, v ∈ Z.conjBy g →
        ∃ c g' : G, c ∈ centralizer (Z : Set G) ∧
          c*v*c⁻¹ ∈ Q ∧ c*v*c⁻¹ ∉ Z ∧ orderOf (c*v*c⁻¹) = 2 ∧
          c*v*c⁻¹ ∈ Z.conjBy g' ∧ Z ≤ Q.conjBy g' ∧
          Q.conjBy g' ⊓ centralizer (Z : Set G) ≤ Global.sourceS L H ∧
          U.conjBy c ≤ Q ∧ (frattini (U.conjBy c)).map (U.conjBy c).subtype = Z ∧
          U.conjBy c ≤ centralizer (Z.conjBy g' : Set G) ∧
          ∃ x ∈ (Global.sourceS L H).conjBy c, ⁅x,c*v*c⁻¹⁆ ∉ Z := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hf := d.g2_right_center_fusion hi hH hp F he
  have hPhiS := d.g2_source_frattini_le_core hi hH.1.1.2 hp F he
  obtain ⟨e,v,hv,hmark,hvZ,hv2,hmoved,r,s,hUQ,_,hPhiU,hUC,_⟩ :=
    d.g2_special_core_root_pair hi hH hp F he
  refine ⟨e,v,hv,hmark,hvZ,hv2,hmoved,r,s,hUQ,hPhiU,?_⟩
  intro g hvg
  obtain ⟨c,g',hc,hcQ,hcZ,hc2,hcg,hZQ,hRS,hUQc,hPhiUc,hUCc,hm⟩ :=
    Global.source_special_core_placements hH.1.1.2 hPhiS hf.2.2 hCS _ hUQ hPhiU
      v hv hvZ g hvg (hUC g hvg)
  refine ⟨c,g',hc,hcQ,hcZ,hc2.trans hv2,hcg,hZQ,hRS,hUQc,hPhiUc,hUCc,?_⟩
  obtain ⟨x,hx,hxv⟩ := hmoved
  exact ⟨c*x*c⁻¹,(hm x hx hxv).1,(hm x hx hxv).2⟩

/-- Construct both source placements for the actual triality root pair, retaining
the unresolved Sylow-centralizer identity and the changed representative. -/
theorem rankOne_global_triality_special_core_placements
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse))
    (hCS : (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ Global.sourceS L H) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse,
      ∃ v ∈ Q,
      (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val = v ∧ (e.right w).val = _root_.Triality.Standard.RadicalCoordinates.LeviCommutators.short
          (_root_.Triality.Standard.binaryParameters m hm) rfl 2 1) ∧
      v ∉ Z ∧ orderOf v = 2 ∧ (∃ x ∈ Global.sourceS L H, ⁅x,v⁆ ∉ Z) ∧
      ∃ r s : G,
      let U := Z.conjBy r ⊔ Z.conjBy s
      U ≤ Q ∧ (frattini U).map U.subtype = Z ∧
      ∀ g : G, v ∈ Z.conjBy g →
        ∃ c g' : G, c ∈ centralizer (Z : Set G) ∧
          c*v*c⁻¹ ∈ Q ∧ c*v*c⁻¹ ∉ Z ∧ orderOf (c*v*c⁻¹) = 2 ∧
          c*v*c⁻¹ ∈ Z.conjBy g' ∧ Z ≤ Q.conjBy g' ∧
          Q.conjBy g' ⊓ centralizer (Z : Set G) ≤ Global.sourceS L H ∧
          U.conjBy c ≤ Q ∧ (frattini (U.conjBy c)).map (U.conjBy c).subtype = Z ∧
          U.conjBy c ≤ centralizer (Z.conjBy g' : Set G) ∧
          ∃ x ∈ (Global.sourceS L H).conjBy c, ⁅x,c*v*c⁻¹⁆ ∉ Z := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hf := d.triality_right_center_fusion hi hH hp m hm he
  have hPhiS := d.triality_source_frattini_le_core hi hH.1.1.2 hp m hm he
  obtain ⟨e,v,hv,hmark,hvZ,hv2,hmoved,r,s,hUQ,_,hPhiU,hUC,_⟩ :=
    d.triality_special_core_root_pair hi hH hp m hm he
  refine ⟨e,v,hv,hmark,hvZ,hv2,hmoved,r,s,hUQ,hPhiU,?_⟩
  intro g hvg
  obtain ⟨c,g',hc,hcQ,hcZ,hc2,hcg,hZQ,hRS,hUQc,hPhiUc,hUCc,hm⟩ :=
    Global.source_special_core_placements hH.1.1.2 hPhiS hf.2.2 hCS _ hUQ hPhiU
      v hv hvZ g hvg (hUC g hvg)
  refine ⟨c,g',hc,hcQ,hcZ,hc2.trans hv2,hcg,hZQ,hRS,hUQc,hPhiUc,hUCc,?_⟩
  obtain ⟨x,hx,hxv⟩ := hmoved
  exact ⟨c*x*c⁻¹,(hm x hx hxv).1,(hm x hx hxv).2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
