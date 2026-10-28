module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinarySpanKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Neighborhood
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel
public import Theory.Frattini.QuadraticCentralizer

/-!
# The elementary quotient by the actual second ball kernel

Natural-center faithfulness at the opposite endpoint, together with the
common-Sylow placement, identifies C_(Q_beta)(V_beta) with
Q_beta intersect G_beta^(2). The forward containment uses relative normality
and the second-ball normal-core formula. In the reverse direction, the
kernel-Sylow theorem places every two-subgroup fixing a neighboring first
ball in that neighbor's core, which centralizes its center.

The source identity [V_beta,Q_beta] <= Z_beta then puts the Frattini subgroup
of Q_beta in G_beta^(2). Thus the literal quotient by the restriction of the
full second kernel is elementary abelian. No elementary quotient, action,
or order bound is assumed. The source's separate full containment
G_beta^(2) <= Q_beta is not asserted by these results.

The common-Sylow placement and neighboring natural center are earlier
(12.1)(c,e) inputs; the commutator bound is (12.1)(f). SecondKernelAction
applies these results to the original local quotient and its conjugation.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(6.2)(d), (12.1), (12.6), printed pp.119,178,183.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The core action kernel is the intersection with the full second ball kernel. -/
theorem source_core_span_centralizer_eq_second_kernel (h : HypothesisF11 L S) (i : Bool)
    (hplace : Q (reducedFamily L S) (base (reducedFamily L S) i) ≤ ReducedLayer.star L S (!i))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i)))) :
    let F := reducedFamily L S
    let v := base F i
    Q F v ⊓ centralizer (V F v 1 : Set (G₀ L S)) = Q F v ⊓ ballKernel F v 2 := by
  let F := reducedFamily L S
  let v := base F i
  let w := base F (!i)
  let C := Q F v ⊓ centralizer (V F v 1 : Set (G₀ L S))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj : (graph F).Adj v w :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun z => (source_Z_Q_U (reduced_triple h) z).1
  have hQU := fun z => (source_Z_Q_U (reduced_triple h) z).2
  have hn : stabilizer F v ≤ normalizer (C : Set (G₀ L S)) :=
    (le_inf (CommutingTrivial.stabilizer_normalizes_Q F v)
      ((stabilizer_normalizes_V F v 1).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hCv : C ≤ stabilizer F v := inf_le_left.trans (Q_le_stabilizer F v)
  have hCw : C ≤ Q F w := by
    intro x hx
    exact natural_center_centralizer_le_core _ _ _ hnat
      ⟨hplace hx.1, centralizer_le (Z_neighbor_le_V F hadj) hx.2⟩
  have hC2 : C ≤ ballKernel F v 2 := by
    let : (C.subgroupOf (stabilizer F v)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hCv).mpr hn
    have hh : C.subgroupOf (stabilizer F v) ≤
        (ballKernel F v 2).subgroupOf (stabilizer F v) := by
      rw [ballKernel_two_eq_normalCore F hadj]
      apply normal_le_normalCore.mpr
      intro x hx
      exact ⟨hQU v hx.1, hQU w (hCw hx)⟩
    intro x hx
    exact hh (show (⟨x,hCv hx⟩ : stabilizer F v) ∈ C.subgroupOf (stabilizer F v) from hx)
  apply le_antisymm (le_inf inf_le_left hC2)
  have hp : IsPGroup 2 (Q F v ⊓ ballKernel F v 2 : Subgroup (G₀ L S)) :=
    (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hcw : ∀ z, (graph F).Adj v z → Q F v ⊓ ballKernel F v 2 ≤ Q F z := by
    intro z hz
    exact CommutingTrivial.two_subgroup_le_Q F z (reduced_kernel_sylow h z) hp
      (inf_le_right.trans (ballKernel_succ_le F hz 1))
  intro x hx
  refine ⟨hx.1,?_⟩
  have hc : V F v 1 ≤ centralizer ({x} : Set (G₀ L S)) := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    have hxz : x ∈ Q F z := by
      rcases (mem_ball_one F v z).mp hz with hz | rfl
      · exact hcw z hz hx
      · exact hx.1
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (Z_centralizes_Q F z (hZ z) ha x hxz).symm
  intro a ha
  exact mem_centralizer_singleton_iff.mp (hc ha)

/-- The source commutator identity makes the literal second-kernel quotient elementary. -/
theorem source_second_kernel_elementary (h : HypothesisF11 L S) (i : Bool)
    (hplace : Q (reducedFamily L S) (base (reducedFamily L S) i) ≤ ReducedLayer.star L S (!i))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let v := base F i
    let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
    IsElementaryAbelian 2 (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v)) := by
  let F := reducedFamily L S
  let v := base F i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (Q F v) := Finite.of_injective (inclusion (Q_le_stabilizer F v))
    (inclusion_injective _)
  let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  have hZ := (source_Z_Q_U (reduced_triple h) v).1
  let := Z_elementary F (fun z => (source_Z_Q_U (reduced_triple h) z).1) v
  have hphi := frattini_image_le_centralizer_of_elementary_commutator
    (Q F v) (V F v 1) (Z F v) (isPGroup_pCoreIn 2 _)
    (by rwa [commutator_comm]) (le_centralizer_iff.mp (Z_centralizes_Q F v hZ))
  change IsElementaryAbelian 2 (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v))
  have hp : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 _
  apply elementary_quotient_of_frattini_le hp ((ballKernel F v 2).subgroupOf (Q F v))
  intro x hx
  have hc : (x : G₀ L S) ∈ Q F v ⊓ centralizer (V F v 1 : Set (G₀ L S)) :=
    ⟨x.property,hphi (mem_map_of_mem (Q F v).subtype hx)⟩
  exact ((source_core_span_centralizer_eq_second_kernel h i hplace hnat).le hc).2


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
