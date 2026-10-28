module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Pointwise Sylow fixers in M₂₂

The intersection of the marked pair and hexad-partition stabilizers is the
certified Sylow subgroup of order 128. Three explicit design permutations
belong to it. Twenty words in these elements reconstruct every point from
the representatives 0, 1 and 3; point-stabilizer constraints leave two
possible images for each representative. Preservation of hexad 5 leaves
only the identity and an even product of eight transpositions. Thus every
design automorphism centralizing this Sylow subgroup lies in M₂₂.

Full automorphism coverage and Sylow conjugacy give innerness for every
pointwise Sylow-fixing abstract automorphism, without an order restriction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.6
and the M₂₂ row 16.1.5(5), printed pp.1171–1172. The tables are discovered
from the repository's degree-22 Steiner model; all memberships, restrictions
and exhaustiveness assertions below are checked by Lean's kernel.
-/

namespace Sporadic.Mathieu.M22SylowPointwise
open Subgroup M22ValueBound.Concrete
open scoped Pointwise
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-- The actual Sylow subgroup obtained from the marked partition geometry. -/
public noncomputable def standardSylow : Sylow 2 M22 :=
  Sylow.ofCard (first ⊓ second) (by
    rw [PartitionStructure.intersection_card, m22_order]
    decide +kernel)

private def generatorTable : Fin 3 → Fin 22 → Fin 22 :=
  ![![6, 2, 1, 3, 9, 11, 16, 8, 5, 19, 10, 7, 4, 15, 13, 17, 21, 14, 20, 12, 18, 0],
    ![0, 2, 1, 3, 5, 4, 21, 19, 9, 8, 10, 12, 11, 13, 15, 14, 16, 17, 20, 7, 18, 6],
    ![0, 1, 2, 18, 7, 6, 5, 4, 8, 9, 20, 16, 13, 12, 19, 21, 11, 17, 3, 14, 10, 15]]

private def generatorInverseTable : Fin 3 → Fin 22 → Fin 22 :=
  ![![21, 2, 1, 3, 12, 8, 0, 11, 7, 4, 10, 5, 19, 14, 17, 13, 6, 15, 20, 9, 18, 16],
    ![0, 2, 1, 3, 5, 4, 21, 19, 9, 8, 10, 12, 11, 13, 15, 14, 16, 17, 20, 7, 18, 6],
    ![0, 1, 2, 18, 7, 6, 5, 4, 8, 9, 20, 16, 13, 12, 19, 21, 11, 17, 3, 14, 10, 15]]

private theorem generator_leftInverse : ∀ (i : Fin 3) (x : Fin 22),
    generatorInverseTable i (generatorTable i x) = x := by decide +kernel

private theorem generator_rightInverse : ∀ (i : Fin 3) (x : Fin 22),
    generatorTable i (generatorInverseTable i x) = x := by decide +kernel

private def generatorPerm (i : Fin 3) : Equiv.Perm (Fin 22) where
  toFun := generatorTable i
  invFun := generatorInverseTable i
  left_inv := generator_leftInverse i
  right_inv := generator_rightInverse i

private def blockIndex : Fin 3 → Fin 77 → Fin 77 :=
  ![![0, 3, 4, 2, 1, 22, 21, 24, 23, 33, 26, 31, 34, 29, 28, 32, 25, 30, 35, 27, 36, 7, 8, 5, 6, 9, 18, 19, 14, 17, 13, 11, 20, 16, 12, 10, 15, 46, 47, 38, 41, 45, 48, 39, 40, 44, 37, 43, 42, 75, 67, 72, 62, 60, 52, 59, 69, 54, 53, 68, 61, 58, 57, 56, 76, 66, 49, 71, 70, 73, 55, 74, 64, 63, 50, 65, 51],
    ![0, 2, 1, 3, 4, 22, 21, 24, 23, 25, 29, 28, 27, 26, 31, 36, 33, 35, 30, 34, 32, 6, 5, 8, 7, 9, 13, 12, 11, 10, 18, 14, 20, 16, 19, 17, 15, 37, 40, 41, 38, 39, 42, 45, 47, 43, 46, 44, 48, 49, 50, 64, 60, 62, 61, 59, 63, 58, 57, 55, 52, 54, 53, 56, 51, 65, 75, 74, 70, 73, 68, 71, 72, 69, 67, 66, 76],
    ![0, 1, 2, 3, 4, 16, 15, 9, 20, 7, 12, 17, 10, 14, 13, 6, 5, 11, 19, 18, 8, 28, 31, 27, 34, 30, 33, 23, 21, 32, 25, 22, 29, 26, 24, 36, 35, 51, 69, 45, 40, 68, 64, 63, 55, 39, 72, 47, 76, 58, 65, 37, 60, 53, 54, 44, 70, 71, 49, 59, 52, 66, 67, 43, 42, 50, 61, 62, 41, 38, 56, 57, 46, 73, 74, 75, 48]]

private theorem generator_mem (i : Fin 3) : generatorPerm i ∈ M22 := by
  constructor
  · change generatorPerm i ∈ m22WittDesign.aut
    rw [Theory.GroupTheory.SteinerSystem.mem_aut_iff]
    have hi : ∀ i : Fin 3, Finset.univ.image (blockIndex i) = Finset.univ := by
      decide +kernel
    have hb : ∀ (i : Fin 3) (j : Fin 77) (x : Fin 22),
        (m22BlockMask j).testBit ((generatorPerm i).symm x).val =
          (m22BlockMask (blockIndex i j)).testBit x.val := by
      decide +kernel
    have he := m22_blocks_smul_of_index (generatorPerm i) (blockIndex i) (hi i)
      (fun j => m22Perm_smul_blockAt_of_bits _ _ _ (hb i j))
    have hs := congrArg (fun s : Finset (Finset (Fin 22)) =>
      (s : Set (Finset (Fin 22)))) he
    simpa only [m22WittDesign, Theory.GroupTheory.SteinerSystem.ofPairwiseIntersection_blocks,
      Finset.coe_smul_finset] using hs
  · change generatorPerm i ∈ alternatingGroup (Fin 22)
    fin_cases i
    · change generatorPerm 0 ∈ alternatingGroup (Fin 22)
      have he : generatorPerm 0 = List.formPerm [0, 6, 16, 21] *
    List.formPerm [1, 2] *
    List.formPerm [4, 9, 19, 12] *
    List.formPerm [5, 11, 7, 8] *
    List.formPerm [13, 15, 17, 14] *
    List.formPerm [18, 20] := by decide +kernel
      rw [he, Equiv.Perm.mem_alternatingGroup]
      simp [List.formPerm, Equiv.Perm.sign_swap']
    · change generatorPerm 1 ∈ alternatingGroup (Fin 22)
      have he : generatorPerm 1 = List.formPerm [1, 2] *
    List.formPerm [4, 5] *
    List.formPerm [6, 21] *
    List.formPerm [7, 19] *
    List.formPerm [8, 9] *
    List.formPerm [11, 12] *
    List.formPerm [14, 15] *
    List.formPerm [18, 20] := by decide +kernel
      rw [he, Equiv.Perm.mem_alternatingGroup]
      simp [List.formPerm, Equiv.Perm.sign_swap']
    · change generatorPerm 2 ∈ alternatingGroup (Fin 22)
      have he : generatorPerm 2 = List.formPerm [3, 18] *
    List.formPerm [4, 7] *
    List.formPerm [5, 6] *
    List.formPerm [10, 20] *
    List.formPerm [11, 16] *
    List.formPerm [12, 13] *
    List.formPerm [14, 19] *
    List.formPerm [15, 21] := by decide +kernel
      rw [he, Equiv.Perm.mem_alternatingGroup]
      simp [List.formPerm, Equiv.Perm.sign_swap']

private noncomputable def generator (i : Fin 3) : M22 :=
  ⟨generatorPerm i, generator_mem i⟩

private theorem generator_mem_standard (i : Fin 3) :
    generator i ∈ standardSylow := by
  change generator i ∈ first ⊓ second
  constructor
  · change generatorPerm i • m22Pair12 = m22Pair12
    revert i
    decide +kernel
  · change generatorPerm i • hexadPartition = hexadPartition
    revert i
    decide +kernel

private def actorWord : Fin 20 → List (Fin 3) :=
  ![[], [0], [2], [0, 0], [1, 0], [2, 0], [2, 1], [0, 2], [2, 0, 0], [2, 1, 0], [1, 2, 0], [2, 0, 2], [0, 2, 0, 0], [1, 2, 0, 0], [0, 2, 1, 0], [1, 2, 1, 0], [0, 1, 2, 0], [0, 0, 2, 0, 0], [1, 0, 2, 0, 0], [2, 1, 2, 0, 0]]

private noncomputable def actor (i : Fin 20) : M22 :=
  ((actorWord i).map generator).prod

private theorem actor_mem_standard (i : Fin 20) : actor i ∈ standardSylow := by
  apply (standardSylow : Subgroup M22).list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  exact generator_mem_standard j

private def actorTable : Fin 20 → Fin 22 → Fin 22 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
    ![6, 2, 1, 3, 9, 11, 16, 8, 5, 19, 10, 7, 4, 15, 13, 17, 21, 14, 20, 12, 18, 0],
    ![0, 1, 2, 18, 7, 6, 5, 4, 8, 9, 20, 16, 13, 12, 19, 21, 11, 17, 3, 14, 10, 15],
    ![16, 1, 2, 3, 19, 7, 21, 5, 11, 12, 10, 8, 9, 17, 15, 14, 0, 13, 18, 4, 20, 6],
    ![21, 1, 2, 3, 8, 12, 16, 9, 4, 7, 10, 19, 5, 14, 13, 17, 6, 15, 18, 11, 20, 0],
    ![5, 2, 1, 18, 9, 16, 11, 8, 6, 14, 20, 4, 7, 21, 12, 17, 15, 19, 10, 13, 3, 0],
    ![0, 2, 1, 18, 6, 7, 15, 14, 9, 8, 20, 13, 16, 12, 21, 19, 11, 17, 10, 4, 3, 5],
    ![6, 2, 1, 20, 8, 16, 11, 9, 5, 19, 18, 21, 15, 4, 12, 0, 7, 14, 3, 13, 10, 17],
    ![11, 1, 2, 18, 14, 4, 15, 6, 16, 13, 20, 8, 9, 17, 21, 19, 0, 12, 3, 7, 10, 5],
    ![15, 1, 2, 18, 8, 13, 11, 9, 7, 4, 20, 14, 6, 19, 12, 17, 5, 21, 3, 16, 10, 0],
    ![4, 1, 2, 20, 8, 16, 12, 9, 21, 15, 18, 5, 19, 6, 11, 17, 14, 7, 10, 13, 3, 0],
    ![5, 2, 1, 10, 8, 11, 16, 9, 6, 14, 3, 15, 21, 7, 13, 0, 4, 19, 18, 12, 20, 17],
    ![7, 2, 1, 20, 13, 9, 17, 16, 21, 15, 18, 5, 19, 14, 0, 12, 6, 4, 3, 8, 10, 11],
    ![12, 2, 1, 20, 15, 5, 14, 21, 16, 13, 18, 9, 8, 17, 6, 7, 0, 11, 3, 19, 10, 4],
    ![17, 2, 1, 20, 5, 15, 7, 19, 8, 9, 18, 13, 16, 12, 4, 14, 11, 0, 3, 21, 10, 6],
    ![14, 2, 1, 20, 9, 13, 12, 8, 19, 5, 18, 15, 21, 7, 11, 17, 4, 6, 3, 16, 10, 0],
    ![9, 2, 1, 18, 5, 21, 4, 19, 0, 17, 20, 11, 12, 16, 7, 14, 13, 8, 10, 15, 3, 6],
    ![8, 1, 2, 18, 15, 19, 14, 21, 0, 17, 20, 11, 12, 13, 6, 4, 16, 9, 3, 5, 10, 7],
    ![19, 1, 2, 18, 13, 8, 17, 16, 6, 14, 20, 4, 7, 15, 0, 11, 21, 5, 3, 9, 10, 12],
    ![13, 2, 1, 10, 21, 6, 19, 15, 11, 12, 3, 9, 8, 17, 5, 4, 0, 16, 18, 14, 20, 7]]

private theorem actor_table : ∀ (i : Fin 20) (x : Fin 22),
    (actor i : Equiv.Perm (Fin 22)) x = actorTable i x := by
  decide +kernel

private def base : Fin 3 → Fin 22 := ![0, 1, 3]
private def baseIndex : Fin 22 → Fin 3 := ![0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0]
private def actorIndex : Fin 22 → Fin 20 := ![0, 0, 1, 0, 10, 5, 1, 12, 17, 16, 11, 8, 13, 19, 15, 9, 3, 14, 2, 18, 7, 4]

private theorem reconstruct_point : ∀ x : Fin 22,
    actorTable (actorIndex x) (base (baseIndex x)) = x := by decide +kernel

private def options : Fin 3 → Finset (Fin 22) := ![{0, 17}, {1, 2}, {3, 10}]

private theorem fixed_options : ∀ (k : Fin 3) (y : Fin 22),
    (∀ i : Fin 20, actorTable i (base k) = base k → actorTable i y = y) →
      y ∈ options k := by decide +kernel

private def seeds (i j k : Fin 2) : Fin 3 → Fin 22 :=
  ![![0, 17] i, ![1, 2] j, ![3, 10] k]

private def reconstruct (i j k : Fin 2) (x : Fin 22) : Fin 22 :=
  actorTable (actorIndex x) (seeds i j k (baseIndex x))

private def centralPerm : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 17] *
    List.formPerm [4, 7] *
    List.formPerm [5, 19] *
    List.formPerm [6, 14] *
    List.formPerm [8, 9] *
    List.formPerm [11, 12] *
    List.formPerm [13, 16] *
    List.formPerm [15, 21]

private theorem centralPerm_even : centralPerm ∈ alternatingGroup (Fin 22) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [centralPerm, List.formPerm, Equiv.Perm.sign_swap']

private theorem reconstruction_check : ∀ (i j k : Fin 2),
    (∃ b : Fin 77, ∀ x ∈ m22BlockAt 5, reconstruct i j k x ∈ m22BlockAt b) →
      reconstruct i j k = id ∨ reconstruct i j k = centralPerm := by
  decide +kernel

/-- The actual design centralizer of the marked Sylow subgroup is even. -/
public theorem designAut_mem_M22_of_centralizes_standard (g : m22DesignAut)
    (hg : ∀ x ∈ standardSylow,
      (g : Equiv.Perm (Fin 22)) * (x : Equiv.Perm (Fin 22)) =
        (x : Equiv.Perm (Fin 22)) * (g : Equiv.Perm (Fin 22))) :
    (g : Equiv.Perm (Fin 22)) ∈ M22 := by
  let f : Equiv.Perm (Fin 22) := g.val
  have hc (i : Fin 20) (x : Fin 22) :
      f (actorTable i x) = actorTable i (f x) := by
    have h := congrArg (fun p : Equiv.Perm (Fin 22) => p x)
      (hg (actor i) (actor_mem_standard i))
    simpa only [Equiv.Perm.mul_apply, actor_table] using h
  have hs (k : Fin 3) : f (base k) ∈ options k := by
    apply fixed_options k
    intro i hi
    rw [← hc, hi]
  have choose0 : ∀ y ∈ options 0, ∃ i : Fin 2, ![0, 17] i = y := by decide +kernel
  have choose1 : ∀ y ∈ options 1, ∃ j : Fin 2, ![1, 2] j = y := by decide +kernel
  have choose2 : ∀ y ∈ options 2, ∃ k : Fin 2, ![3, 10] k = y := by decide +kernel
  obtain ⟨i, hi⟩ := choose0 _ (hs 0)
  obtain ⟨j, hj⟩ := choose1 _ (hs 1)
  obtain ⟨k, hk⟩ := choose2 _ (hs 2)
  have hseeds (s : Fin 3) : seeds i j k s = f (base s) := by
    fin_cases s
    · exact hi
    · exact hj
    · exact hk
  have hf : reconstruct i j k = f := by
    funext x
    rw [reconstruct, hseeds, ← hc, reconstruct_point]
  have hb : f • m22BlockAt 5 ∈ m22Blocks := by
    have hmem : m22BlockAt 5 ∈ m22Blocks :=
      Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
    have hdesign := g.property
    change f ∈ m22WittDesign.aut at hdesign
    rw [Theory.GroupTheory.SteinerSystem.mem_aut_iff] at hdesign
    have h := Set.smul_mem_smul_set (a := f) hmem
    simp only [m22WittDesign,
      Theory.GroupTheory.SteinerSystem.ofPairwiseIntersection_blocks] at hdesign
    rw [hdesign] at h
    exact h
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hb
  have hb' : ∃ b : Fin 77, ∀ x ∈ m22BlockAt 5, f x ∈ m22BlockAt b := by
    refine ⟨b, ?_⟩
    intro x hx
    rw [hb]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  refine ⟨g.property, ?_⟩
  rcases reconstruction_check i j k (hf.symm ▸ hb') with he | he
  · have h1 : f = 1 := Equiv.ext (fun x => congrFun (hf.symm.trans he) x)
    change f ∈ alternatingGroup (Fin 22)
    rw [h1]
    exact (alternatingGroup (Fin 22)).one_mem
  · have hz : f = centralPerm := Equiv.ext (fun x => congrFun (hf.symm.trans he) x)
    change f ∈ alternatingGroup (Fin 22)
    rw [hz]
    exact centralPerm_even

private theorem inner_of_fixes_standard (r : MulAut M22)
    (hS : ∀ x ∈ standardSylow, r x = x) : ∃ g : M22, r = MulAut.conj g := by
  obtain ⟨g, rfl⟩ := m22DesignAutToAut_surjective r
  have hg : (g : Equiv.Perm (Fin 22)) ∈ M22 := by
    apply designAut_mem_M22_of_centralizes_standard g
    intro x hx
    have h := congrArg (fun y : M22 => (y : Equiv.Perm (Fin 22))) (hS x hx)
    rw [m22DesignAutToAut_apply_perm] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  refine ⟨⟨g.val, hg⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [m22DesignAutToAut_apply_perm]
  rfl

/-- Every automorphism fixing a Sylow two-subgroup of M₂₂ pointwise is inner. -/
public theorem automorphism_inner_of_fixes_sylow (r : MulAut M22) (S : Sylow 2 M22)
    (hS : ∀ x ∈ S, r x = x) : ∃ g : M22, r = MulAut.conj g := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 standardSylow S
  let e : MulAut M22 := MulAut.conj g
  have hfixed (x : M22) (hx : x ∈ standardSylow) :
      MulAut.congr e.symm r x = x := by
    have hmem : e x ∈ S := by
      rw [← hg]
      change e x ∈ (standardSylow : Subgroup M22).map e.toMonoidHom
      exact mem_map_of_mem e.toMonoidHom hx
    change e.symm (r (e x)) = x
    rw [hS _ hmem]
    exact e.symm_apply_apply x
  exact (MulAut.congr_inner_iff e.symm r).mp
    (inner_of_fixes_standard _ hfixed)

end Sporadic.Mathieu.M22SylowPointwise
