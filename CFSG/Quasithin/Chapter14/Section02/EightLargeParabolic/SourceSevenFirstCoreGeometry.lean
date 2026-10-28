module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreIntersection
import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanPaths
public import Theory.GroupAction.ThreePointKernelSeparation

/-!
# The original seven-centralizer fixing a second binary neighbor

Fixing two neighbors at the cubic binary vertex forces fixation of its
entire star. The original kernel Sylow theorem then places the actual
 two-subgroup in the full binary core. The proved first-core intersection
identifies it with the original center plane, which centralizes that core.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreGeometry
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction Noncommuting NoncommutingProfile

private theorem two_subgroup_le_cubic_core_of_two_fixed
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S)
    {α β γ : Vertex (reducedFamily L S)}
    (hαβ : (graph (reducedFamily L S)).Adj α β)
    (hαγ : (graph (reducedFamily L S)).Adj α γ) (hne : β ≠ γ)
    (hthree : Nat.card ((graph (reducedFamily L S)).neighborSet α) = 3)
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hDα : D ≤ stabilizer (reducedFamily L S) α)
    (hDβ : D ≤ stabilizer (reducedFamily L S) β)
    (hDγ : D ≤ stabilizer (reducedFamily L S) γ) : D ≤ Q (reducedFamily L S) α := by
  let F := reducedFamily L S
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  apply CommutingTrivial.two_subgroup_le_Q F α (reduced_kernel_sylow h α) hD
  intro x hx z hz
  have hfix : ∀ w ∈ (graph F).neighborSet α, x • w = w :=
    MulAction.fixes_three_point_set _ hthree x (fun w => by
      change (graph F).Adj α w ↔ (graph F).Adj α (x • w)
      simpa only [Subgroup.CosetGeometry.translationGraphIso_apply,
        show x • α = α from hDα hx] using
        ((Subgroup.CosetGeometry.translationGraphIso F x).map_adj_iff
          (v := α) (w := w)).symm) hαβ hαγ hne (hDβ hx) (hDγ hx)
  rcases (mem_ball_one F α z).mp hz with hz | rfl
  · exact hfix z hz
  · exact hDα hx

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ

set_option maxHeartbeats 800000 in
/-- A member of the actual seven-fixed eight-core which fixes another
neighbor of the binary base belongs to its original center plane. -/
theorem source_seven_core_neighbor_stabilizer
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ))
    (γ : Vertex Fₛ) (hαγ : (graph Fₛ).Adj (base Fₛ false) γ)
    (hne : base Fₛ true ≠ γ) :
    let h : HypothesisF11 Lₛ Sₛ := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
    let A := (cartan c).map (bOne_tree_map h)
    (Q Fₛ (base Fₛ true) ⊓ centralizer (A : Set (G₀ Lₛ Sₛ))) ⊓
      stabilizer Fₛ γ = Z Fₛ (base Fₛ false) := by
  let h : HypothesisF11 Lₛ Sₛ := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  let α := base Fₛ false
  let β := base Fₛ true
  let A := (cartan c).map (bOne_tree_map h)
  let E := Q Fₛ β ⊓ centralizer (A : Set (G₀ Lₛ Sₛ))
  let D := E ⊓ stabilizer Fₛ γ
  let cov := bOne_tree_cover h
  let a := base (Universal.cosetFamily (reducedAmalgam Lₛ Sₛ)) false
  have hαβ : (graph Fₛ).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hthree : Nat.card ((graph Fₛ).neighborSet α) = 3 := by
    have he := Nat.card_congr (Equiv.ofBijective (cov.hom.mapNeighborSet a)
      (cov.neighbor_bijective a))
    change Nat.card ((sourceGraph (reducedAmalgam Lₛ Sₛ)).neighborSet a) =
      Nat.card ((graph Fₛ).neighborSet (cov.vertex a)) at he
    have ha : cov.vertex a = α := cov.vertex_base false
    rw [ha] at he
    exact he.symm.trans (SourceCartanPaths.source_tree_neighbor_cards
      hG T hempty hM hu hmany hcard e H hH eR a)
  have hDβ : D ≤ Q Fₛ β := inf_le_left.trans inf_le_left
  have hDα : D ≤ stabilizer Fₛ α := hDβ.trans
    ((source_Z_Q_U (reduced_triple h) β).2.trans
      ((ballKernel_one_le_edge _ hαβ.symm).trans inf_le_right))
  have hDq : D ≤ Q Fₛ α := two_subgroup_le_cubic_core_of_two_fixed h hαβ hαγ hne hthree
    D ((isPGroup_pCoreIn 2 (stabilizer Fₛ β)).to_le hDβ) hDα
    (hDβ.trans (Q_le_stabilizer Fₛ β)) inf_le_right
  have hi := SourceSevenFirstCoreIntersection.source_seven_first_core_intersection
    hG T hempty hM hu hmany hcard e H hH eR c
  change E ⊓ Q Fₛ α = Z Fₛ α at hi
  change D = Z Fₛ α
  apply le_antisymm
  · exact (le_inf inf_le_left hDq).trans_eq hi
  · have hZq : Z Fₛ α ≤ Q Fₛ α :=
      (source_Z_Q_U (reduced_triple h) α).1.trans (map_subtype_le _)
    exact le_inf (hi.symm.le.trans inf_le_left)
      (hZq.trans ((source_Z_Q_U (reduced_triple h) α).2.trans
        ((ballKernel_one_le_edge _ hαγ).trans inf_le_right)))

set_option maxHeartbeats 800000 in
/-- The original seven-fixed conjugator centralizes the full binary core
whenever it fixes the second neighbor used by the six-path root. -/
theorem source_seven_core_fixed_neighbor_centralizes
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ))
    (γ : Vertex Fₛ) (hαγ : (graph Fₛ).Adj (base Fₛ false) γ)
    (hne : base Fₛ true ≠ γ)
    (v : G₀ Lₛ Sₛ)
    (hv : v ∈ Q Fₛ (base Fₛ true) ⊓ centralizer
      ((cartan c).map (bOne_tree_map (show HypothesisF11 Lₛ Sₛ from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap)) : Set (G₀ Lₛ Sₛ)))
    (hfix : v • γ = γ) :
    v ∈ centralizer (Q Fₛ (base Fₛ false) : Set (G₀ Lₛ Sₛ)) := by
  let h : HypothesisF11 Lₛ Sₛ :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  have he := source_seven_core_neighbor_stabilizer hG T hempty hM hu hmany hcard e H hH eR c γ hαγ hne
  have hz : v ∈ Z Fₛ (base Fₛ false) := he ▸ ⟨hv,hfix⟩
  exact le_centralizer_iff.mp (graph_Q_centralizes_Z
    (reduced_triple h)
    (base Fₛ false)) hz

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenFirstCoreGeometry
