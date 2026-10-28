/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co2LocalNormal.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co2PairSplitting
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalSimpleKernel
public import Theory.AtlasPort.OtherSporadic.Sporadic.Mathieu22
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22Simplicity

/-!
Normal subgroups of the local marked-pair group containing the explicit swap.
The proof uses its simple Mathieu kernel and the concrete section onto the pair permutation group.

Source: Gerald Höhn, `Atlas/Conway/Co2LocalNormal.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

abbrev Co2MarkedM22 := Mathieu22PointModel ((0,0),0)
  (⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ : Mathieu23Points ((0,0),0))

abbrev Co2Marked22Points := Mathieu22Points ((0,0),0)
  (⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ : Mathieu23Points ((0,0),0))

theorem co2LocalSwap_noncentral : ∃ k : co2PairRestriction.ker,
    co2LocalSwap*k.val ≠ k.val*co2LocalSwap := by
  let x : Co2Marked22Points := ⟨⟨((0,0),2),by change ((0,0),2) ≠ ((0,0),0); decide⟩,
    by change (⟨((0,0),2),_⟩ : Mathieu23Points ((0,0),0)) ≠ ⟨((0,0),1),_⟩; decide⟩
  let y : Co2Marked22Points := ⟨⟨((0,0),3),by change ((0,0),3) ≠ ((0,0),0); decide⟩,
    by change (⟨((0,0),3),_⟩ : Mathieu23Points ((0,0),0)) ≠ ⟨((0,0),1),_⟩; decide⟩
  let z : Co2Marked22Points := ⟨⟨((0,1),0),by change ((0,1),0) ≠ ((0,0),0); decide⟩,
    by change (⟨((0,1),0),_⟩ : Mathieu23Points ((0,0),0)) ≠ ⟨((0,0),1),_⟩; decide⟩
  have := mathieu22_three_transitive ((0,0),0)
    ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩
  have ht : MulAction.IsMultiplyPretransitive Co2MarkedM22 Co2Marked22Points 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 3)
      (by rw [mathieu22_degree]; decide)
  obtain ⟨g,hx,hy⟩ := (MulAction.is_two_pretransitive_iff.mp ht)
    (by decide : x ≠ y) (by decide : x ≠ z)
  let k := mathieu22_to_pair ((0,0),0)
    ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ g
  have hk : k ∈ co2PairRestriction.ker := by
    change k ∈ (mathieu22PairRestriction _ _).ker
    rw [← mathieu22_to_pair_range]
    exact ⟨g,rfl⟩
  refine ⟨⟨k,hk⟩,?_⟩
  intro he
  have hp := congrArg (fun h : Co2MarkedPairGroup => h.val.val ((0,0),2)) he
  have hxx : k.val.val ((0,0),2) = ((0,0),2) :=
    congrArg (fun p : Co2Marked22Points => p.val.val) hx
  have hyy : k.val.val ((0,0),3) = ((0,1),0) :=
    congrArg (fun p : Co2Marked22Points => p.val.val) hy
  change co2PairSwap.val (k.val.val ((0,0),2)) =
    k.val.val (co2PairSwap.val ((0,0),2)) at hp
  have hswap : co2PairSwap.val ((0,0),2) = ((0,0),3) := by decide +kernel
  rw [hxx,hswap,hyy] at hp
  exact (by decide : (((0,0),3) : Omega) ≠ ((0,1),0)) hp

theorem co2PairKernel_simple : IsSimpleGroup co2PairRestriction.ker := by
  have := mathieu22_simple ((0,0),0)
    ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩
  exact (mathieu22PairKernelEquiv _ _).isSimpleGroup

theorem co2Pair_normal_eq_top (N : Subgroup Co2MarkedPairGroup) [N.Normal]
    (hs : co2LocalSwap ∈ N) : N = ⊤ := by
  have := co2PairKernel_simple
  have : IsSimpleGroup (Equiv.Perm Co2MarkedPair) :=
    isSimpleGroup_of_prime_card co2MarkedPair_perms_card
  obtain ⟨k,hk⟩ := co2LocalSwap_noncentral
  have hle := Atlas.GroupTheory.simple_kernel_le_normal_of_noncommuting
    co2PairRestriction N co2LocalSwap hs k hk
  exact Atlas.GroupTheory.normal_eq_top_of_simple_image co2PairRestriction
    (fun p => ⟨co2PairSection p,co2PairSection_rightInverse p⟩) N hle co2LocalSwap hs
    co2PairRestriction_swap_ne

end Atlas.Conway
