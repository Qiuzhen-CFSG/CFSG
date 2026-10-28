module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalNormalizedResidualExclusion
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.SourceSolvabilityReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanMovingControl
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The original moving A₅ context constructs its cubic source pair

Two original chosen modules exclude the normalized residual branch. Local
Cartan escape would centralize the original omega-center, so movement gives
local control. The compatible cubic Cartan therefore constructs a zero-core
F.1.1 pair with an actual symmetric-three quotient at its left factor.
This is a construction from the original hypotheses; the remaining mixed
pair obstruction is not supplied as an assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric Chapter12.Section02
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H W W₁ W₂ W₃ : Subgroup G}

private theorem a5_not_linear_three_four {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : ¬ ClassicalGroup.IsPSL X 3 4 := by
  rintro ⟨F,_,_,hF,⟨f⟩⟩
  have hx : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF,←Nat.card_congr f.toEquiv,hx] at hc
  norm_num [Fin.prod_univ_succ] at hc

/-- The same original mover, with its actual residual module, supplies
the compatible Cartans and the cubic zero-core source pair. -/
theorem original_moving_cubic_source_pair
    (d : Context T L V V₁ V₂ V₃)
    (e : Context T (residual H) W W₁ W₂ W₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      alternatingGroup (Fin 5)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ∃ A B R : Subgroup G,
      CartanPair T L H A B ∧ CartanPrimeActor A H 3 A ∧
      LocalData T L H B A R ∧ SelectedSourceModels H R ∧
      (Prime.generated L H A R).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![A ⊔ Global.sourceS L H,R] (Global.sourceS L H) ∧
      Nonempty (((A ⊔ Global.sourceS L H : Subgroup G) ⧸
        pCore 2 (A ⊔ Global.sourceS L H : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  have h := Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient
  have hpsl := (source523_setup_of_context d).linear
  have hi := d.chosen.rankOne_generic_input_of_many h hmany (by decide : 1 < 2) hpsl
  obtain ⟨A,B,c⟩ := d.chosen.rankOne_exists_cartanPair h (by decide : 1 < 2) hpsl hH hgen
  have hescape : ¬ A ≤ normalizer (residual H : Set G) := by
    intro hA
    apply original_residual_borel_not_normalizes d e hH hgen hm
    rw [←localBorel_eq_map]
    exact (c.normalizes_residual_iff d.normalizes_L hH.1.1.2).mp hA
  have hd := cubic_cartanActor_of_omega_movement hi hH hgen c hZ hescape
  obtain ⟨R,r,hr,hcore,hF11⟩ := cubic_source_pair_of_omega_movement hi hH hgen
    (a5_not_linear_three_four hm.some) c hZ hescape
  refine ⟨A,B,R,c,hd,r,hr,hcore,hF11,?_⟩
  rcases r.prime_left_quotient_cases hi hH c hd with ⟨_,hm⟩ | ⟨hf,_⟩
  · exact hm
  · omega

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
