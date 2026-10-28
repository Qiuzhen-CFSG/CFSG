module
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# The pair stabilizer action on five hexads

The first five entries in the concrete Witt-design table are precisely the
hexads containing {1,2}. Both pair stabilizers act on this pencil. Two explicit
even design automorphisms induce a transposition and a five-cycle, proving
that both actions have image S₅. Their incidence certificates are checked by
the Lean kernel; the permutations were found with GAP on the standard M₂₂
representation, with no external computation used as a proof oracle.

This supplies the quotient actions used in Aschbacher–Smith, E.4.3(2),
printed pp. 241–242 (PDF pp. 252–253). Identifying their kernels with the
intrinsic two-cores is done in the parent module.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace Sporadic.Mathieu.M22ValueBound.Concrete
open Subgroup Theory.GroupTheory
open scoped Pointwise

@[expose] public noncomputable def pairHexad (i : Fin 5) : Finset (Fin 22) :=
  m22BlockAt ⟨i.val, by omega⟩

public theorem pairHexad_injective : Function.Injective pairHexad := by
  decide +kernel

public theorem pairHexads_complete :
    m22Blocks.filter (m22Pair12 ⊆ ·) = Finset.univ.image pairHexad := by
  decide +kernel

public theorem pairHexad_mem (i : Fin 5) : pairHexad i ∈ m22Blocks ∧ m22Pair12 ⊆ pairHexad i := by
  have h : pairHexad i ∈ m22Blocks.filter (m22Pair12 ⊆ ·) := by
    rw [pairHexads_complete]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  exact Finset.mem_filter.mp h

private abbrev PairHexad := {B : Finset (Fin 22) // B ∈ m22Blocks ∧ m22Pair12 ⊆ B}

private noncomputable def pairHexadEquiv : Fin 5 ≃ PairHexad := Equiv.ofBijective
  (fun i => ⟨pairHexad i, pairHexad_mem i⟩) (by
    constructor
    · intro i j hij
      exact pairHexad_injective (congrArg Subtype.val hij)
    · intro B
      have h : B.val ∈ m22Blocks.filter (m22Pair12 ⊆ ·) := Finset.mem_filter.mpr B.property
      rw [pairHexads_complete] at h
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact ⟨i, Subtype.ext hi⟩)

private theorem outerFirst_smul_pairHexad (g : outerFirst) (B : PairHexad) :
    (g.val : Equiv.Perm (Fin 22)) • B.val ∈ m22Blocks ∧
      m22Pair12 ⊆ (g.val : Equiv.Perm (Fin 22)) • B.val := by
  constructor
  · have hg := g.val.property
    change (g.val : Equiv.Perm (Fin 22)) ∈ m22WittDesign.aut at hg
    rw [SteinerSystem.mem_aut_iff] at hg
    have hm : (g.val : Equiv.Perm (Fin 22)) • B.val ∈
        (g.val : Equiv.Perm (Fin 22)) • (m22WittDesign.blocks : Set (Finset (Fin 22))) :=
      Set.smul_mem_smul_set B.property.1
    rw [hg] at hm
    exact hm
  · have h := Finset.smul_finset_subset_smul_finset
      (a := (g.val : Equiv.Perm (Fin 22))) B.property.2
    have hg : (g.val : Equiv.Perm (Fin 22)) • m22Pair12 = m22Pair12 := g.property
    rwa [hg] at h

private noncomputable instance pairHexadAction : MulAction outerFirst PairHexad where
  smul g B := ⟨(g.val : Equiv.Perm (Fin 22)) • B.val, outerFirst_smul_pairHexad g B⟩
  one_smul B := Subtype.ext (one_smul _ B.val)
  mul_smul g h B := Subtype.ext (mul_smul (g.val : Equiv.Perm (Fin 22))
    (h.val : Equiv.Perm (Fin 22)) B.val)

public noncomputable def outerPairAction : outerFirst →* Equiv.Perm (Fin 5) :=
  pairHexadEquiv.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom outerFirst PairHexad)

public theorem outerPairAction_spec (g : outerFirst) (i : Fin 5) :
    pairHexad (outerPairAction g i) = (g.val : Equiv.Perm (Fin 22)) • pairHexad i := by
  have h := pairHexadEquiv.apply_symm_apply (g • pairHexadEquiv i)
  exact congrArg Subtype.val h

private noncomputable def firstToOuterFirst : first →* outerFirst where
  toFun g := ⟨inclusion g.val, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

public noncomputable def pairAction : first →* Equiv.Perm (Fin 5) :=
  outerPairAction.comp firstToOuterFirst

public theorem pairAction_spec (g : first) (i : Fin 5) :
    pairHexad (pairAction g i) = (g.val : Equiv.Perm (Fin 22)) • pairHexad i :=
  outerPairAction_spec (firstToOuterFirst g) i

private def swapLift : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 2] *
    List.formPerm [3, 21, 20, 4] *
    List.formPerm [5, 14, 19, 6] *
    List.formPerm [7, 10, 15, 18] *
    List.formPerm [9, 17] *
    List.formPerm [11, 12, 13, 16]

private def swapLiftIndexArray : Array (Fin 77) := #[
  1, 0, 2, 3, 4, 24, 36, 29, 31, 23, 22, 21, 26, 34, 25, 28, 30,
  35, 32, 27, 33, 6, 20, 18, 14, 5, 8, 7, 17, 19, 13, 12, 9, 10,
  16, 15, 11, 42, 38, 45, 60, 57, 64, 49, 55, 70, 74, 65, 75, 41, 47,
  37, 40, 46, 48, 44, 39, 43, 63, 50, 73, 66, 67, 71, 51, 59, 61, 62,
  58, 69, 56, 68, 53, 52, 72, 76, 54]

private def swapLiftIndex (i : Fin 77) : Fin 77 :=
  swapLiftIndexArray[i.val]'(by change i.val < 77; exact i.isLt)

private theorem swapLift_mem : swapLift ∈ M22 := by
  constructor
  · change _ ∈ m22WittDesign.aut
    rw [SteinerSystem.mem_aut_iff]
    have he : swapLift • m22Blocks = m22Blocks :=
      m22_blocks_smul_of_index swapLift swapLiftIndex
        (by decide +kernel) (fun i => m22Perm_smul_blockAt_of_bits _ _ _ (by
          have hb : ∀ i : Fin 77, ∀ x : Fin 22,
              (m22BlockMask i).testBit (swapLift.symm x).val =
                (m22BlockMask (swapLiftIndex i)).testBit x.val := by decide +kernel
          exact hb i))
    have hs := congrArg (fun s : Finset (Finset (Fin 22)) => (s : Set (Finset (Fin 22)))) he
    simpa only [m22WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
      Finset.coe_smul_finset] using hs
  · change swapLift ∈ alternatingGroup (Fin 22)
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [swapLift, List.formPerm, Equiv.Perm.sign_swap']

private noncomputable def swapLiftFirst : first :=
  ⟨⟨swapLift, swapLift_mem⟩, by change swapLift • m22Pair12 = m22Pair12; decide +kernel⟩

private def cycleLift : Equiv.Perm (Fin 22) :=
  List.formPerm [3, 21, 14, 9, 11] *
    List.formPerm [4, 19, 0, 16, 20] *
    List.formPerm [5, 17, 12, 18, 15] *
    List.formPerm [6, 8, 13, 10, 7]

private def cycleLiftIndexArray : Array (Fin 77) := #[
  1, 2, 3, 4, 0, 18, 20, 14, 6, 8, 16, 11, 10, 12, 5, 13, 15,
  7, 17, 9, 19, 24, 29, 31, 36, 27, 33, 35, 32, 23, 30, 34, 25, 21,
  22, 28, 26, 65, 57, 64, 74, 38, 60, 55, 49, 42, 45, 75, 70, 73, 62,
  52, 61, 43, 68, 71, 37, 47, 40, 53, 67, 48, 76, 69, 50, 66, 72, 46,
  44, 58, 51, 59, 56, 54, 63, 41, 39]

private def cycleLiftIndex (i : Fin 77) : Fin 77 :=
  cycleLiftIndexArray[i.val]'(by change i.val < 77; exact i.isLt)

private theorem cycleLift_mem : cycleLift ∈ M22 := by
  constructor
  · change _ ∈ m22WittDesign.aut
    rw [SteinerSystem.mem_aut_iff]
    have he : cycleLift • m22Blocks = m22Blocks :=
      m22_blocks_smul_of_index cycleLift cycleLiftIndex
        (by decide +kernel) (fun i => m22Perm_smul_blockAt_of_bits _ _ _ (by
          have hb : ∀ i : Fin 77, ∀ x : Fin 22,
              (m22BlockMask i).testBit (cycleLift.symm x).val =
                (m22BlockMask (cycleLiftIndex i)).testBit x.val := by decide +kernel
          exact hb i))
    have hs := congrArg (fun s : Finset (Finset (Fin 22)) => (s : Set (Finset (Fin 22)))) he
    simpa only [m22WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
      Finset.coe_smul_finset] using hs
  · change cycleLift ∈ alternatingGroup (Fin 22)
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [cycleLift, List.formPerm, Equiv.Perm.sign_swap']

private noncomputable def cycleLiftFirst : first :=
  ⟨⟨cycleLift, cycleLift_mem⟩, by change cycleLift • m22Pair12 = m22Pair12; decide +kernel⟩

private theorem pairAction_swapLift : pairAction swapLiftFirst = Equiv.swap 0 1 := by
  apply Equiv.ext
  intro i
  apply pairHexad_injective
  rw [pairAction_spec]
  change swapLift • pairHexad i = pairHexad (Equiv.swap 0 1 i)
  revert i
  decide +kernel

private theorem pairAction_cycleLift : pairAction cycleLiftFirst = List.formPerm [0, 1, 2, 3, 4] := by
  apply Equiv.ext
  intro i
  apply pairHexad_injective
  rw [pairAction_spec]
  change cycleLift • pairHexad i = pairHexad (List.formPerm [0, 1, 2, 3, 4] i)
  revert i
  decide +kernel

public theorem pairAction_surjective : Function.Surjective pairAction := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← Equiv.Perm.closure_prime_cycle_swap
    (by decide : (Fintype.card (Fin 5)).Prime)
    (List.isCycle_formPerm (by decide : ([0, 1, 2, 3, 4] : List (Fin 5)).Nodup) (by decide))
    (by decide : (List.formPerm [0, 1, 2, 3, 4] : Equiv.Perm (Fin 5)).support = Finset.univ)
    (show (Equiv.swap (0 : Fin 5) 1).IsSwap from ⟨0, 1, by decide, rfl⟩)]
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact ⟨cycleLiftFirst, pairAction_cycleLift⟩
  · exact ⟨swapLiftFirst, pairAction_swapLift⟩

public theorem outerPairAction_surjective : Function.Surjective outerPairAction := by
  intro g
  obtain ⟨h, hh⟩ := pairAction_surjective g
  exact ⟨firstToOuterFirst h, hh⟩

end Sporadic.Mathieu.M22ValueBound.Concrete
