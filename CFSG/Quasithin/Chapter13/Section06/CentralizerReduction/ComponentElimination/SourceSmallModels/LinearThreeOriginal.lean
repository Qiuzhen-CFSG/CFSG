module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThree
public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Original ordinary linear-three block exclusion

The original invariant four-group has a two-dimensional image in the natural
three-space. Its stabilizer is an actual conjugate line parabolic. The source
Sylow image has order eight, and the residual image has order divisible by
three, so together they fill that stabilizer. Sylow normalization puts the
whole parabolic two-residual in the residual image. Its natural fixed space
vanishes, giving the literal ambient centralizer comparison.

The checked short-block endgame then centralizes the original marked a;
13.6.17 gives the contradiction. The final theorem retains precisely the
original flag, local, fusion and reduced-catalogue inputs. It introduces no
module marking, parabolic placement or B.2.14 supplement premise. This closes
the ordinary IsLinearTwoBlock K 3 case. The nonshort C.1.34 alternatives,
including the nonabelian center calculation, remain separate obligations.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.22,
printed pp.932–933, using the marked flag on p.926.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open BinaryLinearThree Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination
open SourceSmallModels SourceSmallModels.BinaryRankTwo
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch

private theorem natural_placement (S : Sylow 2 BinaryLinearThree.Group)
    (D : Subgroup BinaryLinearThree.Group) (h3 : 3 ∣ Nat.card D)
    (e : MovingPlane W S D) :
    ∃ g : BinaryLinearThree.Group, D ⊔ (S : Subgroup BinaryLinearThree.Group) =
      lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := NaturalPlaneStabilizer.exists_stabilizer_eq e.plane e.dimension
  have hstab : D ⊔ (S : Subgroup BinaryLinearThree.Group) ≤
      NaturalPlaneStabilizer.stabilizer e.plane := by
    intro a ha
    exact (NaturalPlaneStabilizer.mem_stabilizer _ _).mpr (e.invariant ha)
  have hle : D ⊔ (S : Subgroup BinaryLinearThree.Group) ≤
      lineParabolicSL.map (MulAut.conj g).toMonoidHom := hg ▸ hstab
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  have h8 : 8 ∣ Nat.card (D ⊔ (S : Subgroup BinaryLinearThree.Group) : Subgroup BinaryLinearThree.Group) := by
    have hS : Nat.card S = 8 := by
      rw [S.card_eq_multiplicity, card_SL]
      decide +kernel
    simpa only [hS] using Subgroup.card_dvd_of_le
      (show (S : Subgroup BinaryLinearThree.Group) ≤ D ⊔ (S : Subgroup BinaryLinearThree.Group) from le_sup_right)
  have h3P := h3.trans (Subgroup.card_dvd_of_le
    (show D ≤ D ⊔ (S : Subgroup BinaryLinearThree.Group) from le_sup_left))
  have h24 := (by decide : Nat.Coprime 8 3).mul_dvd_of_dvd_of_dvd h8 h3P
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_lineParabolicSL]
  exact Nat.le_of_dvd Nat.card_pos h24

private theorem residual_sup_sylow_le (S : Sylow 2 BinaryLinearThree.Group)
    (D : Subgroup BinaryLinearThree.Group)
    (hn : (S : Subgroup BinaryLinearThree.Group) ≤ normalizer (D : Set BinaryLinearThree.Group)) :
    residual (D ⊔ (S : Subgroup BinaryLinearThree.Group)) ≤ D := by
  let P := D ⊔ (S : Subgroup BinaryLinearThree.Group)
  let N := D.subgroupOf P
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hn)
  have hsup : N ⊔ (S : Subgroup BinaryLinearThree.Group).subgroupOf P = ⊤ := by
    rw [← subgroupOf_sup (show D ≤ P from le_sup_left)
      (show (S : Subgroup BinaryLinearThree.Group) ≤ P from le_sup_right)]
    exact subgroupOf_self P
  have hq : IsPGroup 2 (P ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N _ S.isPGroup'.comap_subtype hsup
  have hres : pResidual 2 P ≤ N := sInf_le ⟨inferInstance, hq⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hres hx

private theorem natural_fixed_of_movingPlane (S : Sylow 2 BinaryLinearThree.Group)
    (D : Subgroup BinaryLinearThree.Group)
    (hn : (S : Subgroup BinaryLinearThree.Group) ≤ normalizer (D : Set BinaryLinearThree.Group))
    (h3 : 3 ∣ Nat.card D) (e : MovingPlane W S D)
    (w : Vector) (hw : ∀ d ∈ D, W d w = w) : w = 0 := by
  obtain ⟨g, hg⟩ := natural_placement S D h3 e
  have hres := residual_sup_sylow_le S D hn
  rw [hg] at hres
  have hm : (residual lineParabolicSL).map (MulAut.conj g).toMonoidHom ≤ D := by
    simpa only [MarkedAutomorphisms.residual, map_embedded_pResidual] using hres
  have hz : W g⁻¹ w = 0 := by
    apply ParabolicFixedFree.natural_fixed_eq_zero
    intro a ha
    have h := hw (g * a * g⁻¹) (hm (mem_map_of_mem (MulAut.conj g).toMonoidHom ha))
    have hh := congrArg (W g⁻¹) h
    change W g⁻¹ (W (g * a * g⁻¹) w) = W g⁻¹ w at hh
    simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using hh
  have hh := congrArg (W g) hz
  simpa only [Representation.self_inv_apply, map_zero] using hh

variable {G : Type*} [_root_.Group G] [Finite G] {L K V T : Subgroup G} {v : G}
/-- The original source line determines the actual natural fixed-space comparison. -/
theorem natural_source_centralizer_eq
    (d : SourceLineData L K V T v) (h : IsLinearTwoBlock K 3) :
    BinaryRankTwo.sourceU K ⊓ centralizer (Lv L v : Set G) =
      BinaryRankTwo.sourceU K ⊓ centralizer (K : Set G) := by
  obtain ⟨σ, ⟨b⟩, hσ⟩ := h.2.2.2
  let m := Models.blockQuotientModel K W σ b hσ
  have hf := Models.blockQuotientModel_actor_surjective K W σ b hσ
  have hk := Models.blockQuotientModel_actor_kernel K W σ b hσ
  obtain ⟨S, hS⟩ := SourceActors.exists_source_sylow d.normalizes_K d.sylow d.sylow_eq
  have hl : ⁅V, Lv L v⁆ ≤ Models.ambientU K := by
    rw [← BinaryRankTwo.sourceU_eq K h.2.1]
    exact d.line_le
  let e := SourcePlane.movingPlane m hf T S hS d.lv_le hl d.line_moved
    d.line_card d.line_invariant
  have hn : ((S.mapSurjective hf : Sylow 2 BinaryLinearThree.Group) : Subgroup _) ≤
      normalizer (((Lv L v).subgroupOf K).map m.actor : Set BinaryLinearThree.Group) := by
    rw [SourceActors.sylow_image m.actor hf S hS]
    exact SourceActors.image_normalizes m.actor d.normalizes_Lv
  have h3 := SourceActors.three_dvd_image m.actor d.lv_le
    (by rw [hk]; exact pCore_isPGroup) d.three_dvd
  rw [BinaryRankTwo.sourceU_eq K h.2.1]
  apply m.centralizer_eq (Lv L v) d.lv_le
  intro w hw
  apply natural_fixed_of_movingPlane (S.mapSurjective hf) _ hn h3 e w
  rintro _ ⟨k, hk, rfl⟩
  exact hw ⟨k, hk⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch

open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceContainment
universe u
variable {G : Type u} [_root_.Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The ordinary linear block centralizes the same marked conjugate supplied by the source. -/
theorem linear_centralizes_markedA_of_localConfiguration
    (d : FlagSource T L V V₁ V₂)
    (c : LocalConfiguration (normalizer (L : Set G)) d.flag)
    (h : IsLinearTwoBlock K 3)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    K ≤ Gv (markedA d.flag.module) := by
  obtain ⟨e⟩ := sourceLineData_of_localConfiguration d c h.2.1 hK hn hLK hchar hTL
  have hf := natural_source_centralizer_eq e h
  rw [BinaryRankTwo.sourceU_eq K h.2.1] at hf
  exact short_centralizes_markedA d c h.2.1 hK hn hLK hchar hTL hf

/-- The ordinary L₃(2) block is excluded from the original 13.6.22 configuration. -/
theorem not_linearTwoBlock_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    ¬ IsLinearTwoBlock K 3 := by
  intro h
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz model).1
  have hc := linear_centralizes_markedA_of_localConfiguration d c h hK hn hLK hchar
    earlier.T_normalizes_L
  have hnc := (SourceTransferFields.noncentrality_and_field_exclusions_original_source
    d V₃ earlier standing hm hfusion hform hfailure h1332 h63 K hK hL hz
    ChapterB.QuasisimpleSource.BinaryField.two).1 c.aPoint
  have hconj : ∃ g : G, (c.aPoint : G) = MulAut.conj g (markedZ d.flag.module) := by
    obtain ⟨g, hg⟩ := c.a_conjugate
    exact ⟨g, c.aPoint_val.trans hg.symm⟩
  apply hnc hconj c.a_checked_central
  simpa only [c.aPoint_val, Gv] using hc
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
