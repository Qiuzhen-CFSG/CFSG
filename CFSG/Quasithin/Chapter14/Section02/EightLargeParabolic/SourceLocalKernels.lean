module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReducedPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TorusKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PairReorientation

/-!
# The full local kernels on the original mixed edges

The original eight endpoint and its intrinsic actor both map onto H. Thus
its full permutation kernel equals its two-core. The intersection of the two
full kernels along any edge is then a two-group, and equals the intersection
of the two original cores. The binary full permutation kernel remains intact.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceLocalKernels
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

private theorem eight_local_full (h : HypothesisF11 L S)
    (e8 : (L 1 ⧸ pCore 2 (L 1)) ≃* Theory.PSL2.BinaryGroup 3)
    (hfull : P₀ L S 1 ≤ starredParabolic L S 1) :
    ∀ v : Vertex F, v.type=true →
      graphLocalGroup F v=stabilizer F v ∧ U F v=Q F v := by
  have hb : graphLocalGroup F (base F true)=stabilizer F (base F true) := by
    apply map_injective (G₀ L S).subtype_injective
    rw [reduced_graphLocalGroup_image h true]
    have hs : stabilizer F (base F true)=(P₀ L S 1).subgroupOf (G₀ L S) :=
      Subgroup.CosetGeometry.stabilizer_base F true
    rw [hs]
    change enlargedEndpoint L S 1=((P₀ L S 1).subgroupOf (G₀ L S)).map _
    rw [map_subgroupOf_eq_of_le (show P₀ L S 1≤G₀ L S from le_sup_right),
      reduced_enlargedEndpoint_eq_starred_of_linear h 1 e8]
    exact le_antisymm le_sup_left hfull
  intro v hv
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  change g • base F v.type=v at hg
  rw [hv] at hg
  have hJ : graphLocalGroup F v=stabilizer F v := by
    have hj : graphLocalGroup F (g • base F true)=
        (graphLocalGroup F (base F true)).map (MulAut.conj g).toMonoidHom :=
      graphLocalGroup_conjugate (reduced_triple h) g (base F true)
    rw [←hg,hj,hb,stabilizer_translate]
  obtain ⟨w,hw⟩ : ∃ w, (graph F).Adj v w := by
    change ((graph F).neighborSet v).Nonempty
    apply Set.nonempty_of_ncard_ne_zero
    have hval := source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) v.type
    change 3≤((F (!v.type)).subgroupOf (F v.type)).index at hval
    rw [←Nat.card_coe_set_eq,card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    omega
  obtain ⟨e⟩ := Assembly.linear_graph_quotient h true e8 v hv
  have hi := CommutingTrivial.nonbinary_local_kernel_intersection (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hw e
    (by norm_num [GaloisField.card 2 3 (by decide)])
  change graphLocalGroup F v ⊓ ballKernel F v 1=Q F v at hi
  rw [hJ,inf_eq_right.mpr (ballKernel_le_stabilizer F v 1)] at hi
  exact ⟨hJ,hi⟩

private theorem mixed_intersection (h : HypothesisF11 L S)
    (h8 : ∀ v : Vertex F, v.type=true → U F v=Q F v)
    {v w : Vertex F} (hw : (graph F).Adj v w) :
    U F v ⊓ U F w=Q F v ⊓ Q F w := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hp : IsPGroup 2 (U F v ⊓ U F w : Subgroup (G₀ L S)) := by
    cases hv : v.type
    · have ht : w.type=true := by
        cases ht : w.type
        · exact (hw.1 (hv.trans ht.symm)).elim
        · rfl
      rw [h8 w ht]
      exact (isPGroup_pCoreIn 2 _).to_le inf_le_right
    · rw [h8 v hv]
      exact (isPGroup_pCoreIn 2 _).to_le inf_le_left
  exact le_antisymm
    (le_inf (CommutingTrivial.two_subgroup_le_Q F v (reduced_kernel_sylow h v) hp inf_le_left)
      (CommutingTrivial.two_subgroup_le_Q F w (reduced_kernel_sylow h w) hp inf_le_right))
    (inf_le_inf (source_Z_Q_U (reduced_triple h) v).2
      (source_Z_Q_U (reduced_triple h) w).2)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
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


set_option maxHeartbeats 800000 in
/-- At every original eight vertex (reversed type true), the full endpoint
is its intrinsic actor and its full permutation kernel is its whole two-core. -/
theorem source_eight_local_kernel :
    ∀ v : Vertex (reducedFamily Lₛ (T : Subgroup G)), v.type=true →
      graphLocalGroup (reducedFamily Lₛ (T : Subgroup G)) v=
        stabilizer (reducedFamily Lₛ (T : Subgroup G)) v ∧
      U (reducedFamily Lₛ (T : Subgroup G)) v=Q (reducedFamily Lₛ (T : Subgroup G)) v := by
  have h := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  have hstar : starredParabolic Lₛ (T : Subgroup G) 1=H :=
    (source_starredParabolics hG T hempty hM hu hmany hcard e H hH eR).1
  have hpar : parabolic Lₛ (T : Subgroup G) 1=H :=
    (source_parabolics hG T hempty hM hu hmany hcard e H hH eR).1
  exact eight_local_full h (residualQuotientEquiv H eR)
    (by rw [hstar]; exact (P₀_le h 1).trans_eq hpar)

set_option maxHeartbeats 800000 in
/-- Every actual mixed edge has exactly the intersection of the original
two-cores as its full adjacent-kernel intersection. -/
theorem source_adjacent_kernel_intersection
    {v w : Vertex (reducedFamily Lₛ (T : Subgroup G))}
    (hw : (graph (reducedFamily Lₛ (T : Subgroup G))).Adj v w) :
    U (reducedFamily Lₛ (T : Subgroup G)) v ⊓ U (reducedFamily Lₛ (T : Subgroup G)) w=
      Q (reducedFamily Lₛ (T : Subgroup G)) v ⊓ Q (reducedFamily Lₛ (T : Subgroup G)) w := by
  exact mixed_intersection
    (show HypothesisF11 Lₛ (T : Subgroup G) from
      (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap)
    (fun v hv => (source_eight_local_kernel hG T hempty hM hu hmany hcard e H hH eR v hv).2) hw

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceLocalKernels
