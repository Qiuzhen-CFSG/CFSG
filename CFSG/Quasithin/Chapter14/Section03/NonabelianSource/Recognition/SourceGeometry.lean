module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Preparation
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.TerminalAction.Defs
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Assembly

/-!
# The earlier geometry for the actual rank-two terminal action

The original rank-two hypothesis supplies the full LT action and its literal
two-core kernel. The proved parabolic calculation then gives the elementary
quotient, action kernel and outside-W stabilizer. Its center calculation
gives both intersections used by the transvection argument. All seven fields
of TerminalEarlierData are therefore derived from the nonabelian original
closure and its preceding Frattini and commutator data.

Source: Aschbacher--Smith, 12.8.9--10 and the setup preceding 14.3.11.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {L M : Subgroup G}

/-- All earlier geometry needed by G.10 comes from the original rank-two source. -/
theorem rankTwo_terminal_earlier (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F)
    (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U,u^2 ∈ F.Vi 1)
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    TerminalEarlierData F g (F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP) := by
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e,_,hgen,_,_,_,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  have hqn := F.binary_source_E_normal_in_core L h.L_normalizes_seed g hgP hgen.symm hcomm
  let := hqn
  have hqe := F.binary_source_quotient_elementary L h.L_normalizes_seed g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  have hpair : ∃ hn : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal,
      letI := hn
      IsElementaryAbelian 2 (((F.I₂ L).pCoreIn 2 : Subgroup G) ⧸
        (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := ⟨hqn,hqe⟩
  rw [hsplit] at hpair
  obtain ⟨hn,he⟩ := hpair
  let := hn
  obtain ⟨_,hk,hstab⟩ := F.binary_source_parabolic_action_clauses (by decide) L
    h.L_normalizes_seed (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare
    hspan hne d.seed_center g hgP hgH
  let B : F.UhatCommutatorForm hcomm := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hc := F.binary_source_center_calculations (by decide) L h.L_normalizes_seed
    ((pResidual_eq_top_iff 2 L).mp h.L_residual) h.sylow_normalizes_L
    (h.binarySeedAction_surjective F) (fun hn => by omega) h.centralizer d.seed_center
    hcomm hsquare hspan hne g hgP hgH d.tilde_kernel B
  refine ⟨hn,he,?_,hk.1,hstab,hc.1,?_⟩
  · exact disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L
      h.L_normalizes_seed d.seed_center g hgP hgH).1
  · have hh := hc.2.2.2.2.2.2.2.2.1
    simpa only [inf_comm] using hh

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
