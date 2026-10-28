module

public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.BinaryPermutation.EightSylowFixed
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightCoordinates


/-!
# Sylow-fixed points for the alternating-eight action

The intersection of the binary-tree two-group with A₈ contains the two
Klein generators on each four-point block. Each has a fixed coordinate,
so fixing a class modulo constants forces it to fix every representative.
The four generators force the representative to be constant on both blocks.
Every binary-tree generator then fixes its class. The existing S₈ calculation
identifies the full permutation stabilizer with the four-block stabilizer.
Sylow conjugacy inside A₈ gives the result for every actual alternating Sylow.

This proves the A₈ part without assuming that an A₈ Sylow is an S₈ Sylow.
The quadratic marking is retained from `EightCoordinates`.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.8.13(5), printed pp.855–856, in the G.11.2(5) alternative.
-/

public section

namespace BinaryPermutation.TerminalOrthogonal.Eight
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup

private def evenFixer : Fin 4 → S8 :=
  ![treeGenerator 0 * treeGenerator 1, treeGenerator 4,
    treeGenerator 2 * treeGenerator 3, treeGenerator 5]

private lemma evenFixer_even : ∀ i, evenFixer i ∈ alternatingGroup (Fin 8) := by
  intro i
  rw [Equiv.Perm.mem_alternatingGroup]
  have h : ∀ j, (evenFixer j).sign = 1 := by decide
  exact h i

private lemma evenFixer_mem_tree (i : Fin 4) : evenFixer i ∈ treeGroup := by
  fin_cases i
  · exact treeGroup.mul_mem (treeGenerator_mem 0) (treeGenerator_mem 1)
  · exact treeGenerator_mem 4
  · exact treeGroup.mul_mem (treeGenerator_mem 2) (treeGenerator_mem 3)
  · exact treeGenerator_mem 5

private lemma evenFixer_fixed_point : ∀ j, ∃ i : Fin 8, evenFixer j i = i := by decide

private lemma coordinates (w : Full (Fin 8))
    (h : ∀ i, representation (Fin 8) (evenFixer i) w = w) :
    ∀ i : Fin 8, w i = if i.val < 4 then w 0 else w 4 := by
  have h01 := congrFun (h 0) 0
  have h23 := congrFun (h 0) 2
  have h02 := congrFun (h 1) 0
  have h45 := congrFun (h 2) 4
  have h67 := congrFun (h 2) 6
  have h46 := congrFun (h 3) 4
  change w 1 = w 0 at h01
  change w 3 = w 2 at h23
  change w 2 = w 0 at h02
  change w 5 = w 4 at h45
  change w 7 = w 6 at h67
  change w 6 = w 4 at h46
  intro i
  fin_cases i <;> simp_all

private def blockWord (a b : ZMod 2) : Full (Fin 8) :=
  fun i => if i.val < 4 then a else b

private lemma block_displacement : ∀ (a b : ZMod 2) (j : Fin 7) (i : Fin 8),
    blockWord a b ((treeGenerator j).symm i) - blockWord a b i =
      blockWord a b ((treeGenerator j).symm 0) - blockWord a b 0 := by decide

private lemma fixed_tree_of_evenFixers (v : natural (Fin 8))
    (h : ∀ i, naturalRepresentation (Fin 8) (evenFixer i) v = v) :
    ∀ g ∈ treeGroup, naturalRepresentation (Fin 8) g v = v := by
  obtain ⟨w, _, hw⟩ := v.property
  have hc : w = blockWord (w 0) (w 4) := by
    apply funext
    apply coordinates w
    intro j
    obtain ⟨i, hi⟩ := evenFixer_fixed_point j
    apply (deleted_fixed_iff_of_fixed_point (evenFixer j) w i hi).mp
    rw [hw]
    exact congrArg Subtype.val (h j)
  have hg (j : Fin 7) : naturalRepresentation (Fin 8) (treeGenerator j) v = v := by
    apply Subtype.ext
    change deletedRepresentation (Fin 8) (treeGenerator j) v.val = v.val
    rw [← hw, deleted_fixed_iff]
    refine ⟨blockWord (w 0) (w 4) ((treeGenerator j).symm 0) -
      blockWord (w 0) (w 4) 0, ?_⟩
    intro i
    calc
      _ = blockWord (w 0) (w 4) ((treeGenerator j).symm i) -
          blockWord (w 0) (w 4) i := congrArg₂ (· - ·) (congrFun hc _) (congrFun hc i)
      _ = _ := block_displacement (w 0) (w 4) j i
  intro g hgt
  induction hgt using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hg j
  | one => simp
  | mul x y hx hy hfx hfy =>
    rw [map_mul, Module.End.mul_apply, hfy, hfx]
  | inv x hx hfx =>
    have hh := congrArg (naturalRepresentation (Fin 8) x⁻¹) hfx
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hh
    exact hh.symm

private def evenTree : Subgroup (alternatingGroup (Fin 8)) :=
  treeGroup.comap (alternatingGroup (Fin 8)).subtype

private lemma evenTree_isPGroup : IsPGroup 2 evenTree := by
  let f : evenTree →* treeGroup :=
    { toFun g := ⟨g.val.val, g.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : treeGroup => (z : S8)) h
  exact (IsPGroup.of_card (show Nat.card treeGroup = 2 ^ 7 from card_treeGroup)).of_injective f hf

private lemma inv_apply (r : S8) (v : natural (Fin 8)) :
    naturalRepresentation (Fin 8) r⁻¹ (naturalRepresentation (Fin 8) r v) = v := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

/-- The full permutation stabilizer of an A₈-Sylow-fixed nonzero vector is
a conjugate of the unordered four-plus-four stabilizer. -/
lemma alternating_exists_conjugate_stabilizer (Q : Sylow 2 (alternatingGroup (Fin 8)))
    (v : natural (Fin 8)) (hv : v ≠ 0)
    (hfixed : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val v = v) :
    ∃ r : alternatingGroup (Fin 8), ∀ g : S8,
      naturalRepresentation (Fin 8) g v = v ↔ r.val * g * r.val⁻¹ ∈ fourStabilizer := by
  obtain ⟨Q₀, hQ₀⟩ := evenTree_isPGroup.exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) Q Q₀
  have hmap : (Q : Subgroup (alternatingGroup (Fin 8))).map
      (MulAut.conj r).toMonoidHom = Q₀ := by
    change ((r • Q : Sylow 2 (alternatingGroup (Fin 8))) :
      Subgroup (alternatingGroup (Fin 8))) = (Q₀ : Subgroup (alternatingGroup (Fin 8)))
    rw [hr]
  have hinj : Function.Injective (naturalRepresentation (Fin 8) r.val) := by
    intro a b hab
    have hh := congrArg (naturalRepresentation (Fin 8) r.val⁻¹) hab
    simpa only [inv_apply] using hh
  have hn : naturalRepresentation (Fin 8) r.val v ≠ 0 := by
    intro hz
    apply hv
    apply hinj
    simpa only [map_zero] using hz
  have hc (g : S8) : naturalRepresentation (Fin 8) (r.val * g * r.val⁻¹)
      (naturalRepresentation (Fin 8) r.val v) =
      naturalRepresentation (Fin 8) r.val (naturalRepresentation (Fin 8) g v) := by
    simp only [map_mul, Module.End.mul_apply, inv_apply]
  have hf : ∀ j, naturalRepresentation (Fin 8) (evenFixer j)
      (naturalRepresentation (Fin 8) r.val v) = naturalRepresentation (Fin 8) r.val v := by
    intro j
    have hm : (⟨evenFixer j, evenFixer_even j⟩ : alternatingGroup (Fin 8)) ∈ Q₀ :=
      hQ₀ (evenFixer_mem_tree j)
    change (⟨evenFixer j, evenFixer_even j⟩ : alternatingGroup (Fin 8)) ∈
      (Q₀ : Subgroup (alternatingGroup (Fin 8))) at hm
    rw [← hmap] at hm
    obtain ⟨a, ha, he⟩ := hm
    have he' : r.val * a.val * r.val⁻¹ = evenFixer j := congrArg Subtype.val he
    rw [← he', hc, hfixed a ha]
  refine ⟨r, fun g => ?_⟩
  rw [← EightSylowFixed.tree_fixed_stabilizer _ hn (fixed_tree_of_evenFixers _ hf), hc]
  exact hinj.eq_iff.symm

end BinaryPermutation.TerminalOrthogonal.Eight
