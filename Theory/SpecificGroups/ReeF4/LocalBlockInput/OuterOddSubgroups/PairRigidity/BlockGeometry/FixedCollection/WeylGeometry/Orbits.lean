module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.PositiveFactors
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylWords
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation


/-!
# The eight positive blocks as relative Weyl conjugates

The two relative reflections have split words `[0,3]` and `[1,2,1,2]`.
Their explicit action on the checked positive root table carries each simple
pair or complete B₂ quartet to one of the eight positive blocks. Simple-root
matrix conjugation transports every parameter, including both nonsimple B₂
roots. Products of the supplied fixed representatives give the conjugating
elements in the actual relative Weyl subgroup.

Source: GLS3, 2.3.2–8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection
open LargeLocalSeeds Parabolics.Binary.FixedGeometry
open Parabolics.RadicalCoordinates Parabolics.RadicalCoordinates.FixedCoordinates
noncomputable section
variable {m : ℕ}

/-- The actual root permutation of a numbered split Weyl word. -/
def wordAction (w : List (Fin 4)) : Equiv.Perm F4Chevalley.Root :=
  (w.map fun i => typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i)).prod

private lemma simpleWord_append (m : ℕ) (w v : List (Fin 4)) :
    simpleWord m (w ++ v) = simpleWord m w * simpleWord m v := by
  simp [simpleWord]

/-- Every root parameter is carried to its reflected root by the split word. -/
theorem simpleWord_conj_root (m : ℕ) (w : List (Fin 4)) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    simpleWord m w * rootGeneratorInGroup m r t * (simpleWord m w)⁻¹ =
      rootGeneratorInGroup m (wordAction w r) t := by
  induction w generalizing r with
  | nil => simp [simpleWord, wordAction]
  | cons i w ih =>
    have hs (r : F4Chevalley.Root) :
        simpleWord m [i] * rootGeneratorInGroup m r t * (simpleWord m [i])⁻¹ =
          rootGeneratorInGroup m (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, simpleWord_coe]
      exact PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj
        (typeF4RootPairing_baseEquiv i) r t
    rw [show i :: w = [i] ++ w from rfl, simpleWord_append]
    calc
      _ = simpleWord m [i] * (simpleWord m w * rootGeneratorInGroup m r t *
          (simpleWord m w)⁻¹) * (simpleWord m [i])⁻¹ := by group
      _ = _ := by rw [ih, hs]; rfl

private def orbitSides : PositiveBlockIndex → List Side
  | .inl 0 => []
  | .inl 1 => [.suzuki]
  | .inl 2 => [.linear, .suzuki]
  | .inl 3 => [.suzuki, .linear, .suzuki]
  | .inr 0 => []
  | .inr 1 => [.linear, .suzuki, .linear]
  | .inr 2 => [.linear]
  | .inr 3 => [.suzuki, .linear]

private def orbitWord (i : PositiveBlockIndex) : List (Fin 4) :=
  (orbitSides i).flatMap sideWord

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]
private lemma reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 2000000 in
private lemma pair_orbit (i : Fin 4) (j : Fin 2) :
    wordAction (orbitWord (.inl i)) ((rootBlocks .positive).roots (.inl ((0 : Fin 4),j))).val =
      ((rootBlocks .positive).roots (.inl (i,j))).val := by
  apply Subtype.ext
  fin_cases i <;> fin_cases j <;> funext k <;> fin_cases k <;>
    norm_num [wordAction, orbitWord, orbitSides, sideWord, Equiv.Perm.mul_apply,
      reflection_val, reflectedVector, rootBlocks_roots_val, RootPartition.index,
      RootPartition.pairRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

set_option maxHeartbeats 2000000 in
private lemma quartet_orbit (i : Fin 4) (j : Fin 4) :
    wordAction (orbitWord (.inr i)) ((rootBlocks .positive).roots (.inr ((0 : Fin 4),j))).val =
      ((rootBlocks .positive).roots (.inr (i,j))).val := by
  apply Subtype.ext
  fin_cases i <;> fin_cases j <;> funext k <;> fin_cases k <;>
    norm_num [wordAction, orbitWord, orbitSides, sideWord, Equiv.Perm.mul_apply,
      reflection_val, reflectedVector, rootBlocks_roots_val, RootPartition.index,
      RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

local instance orbitRootNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The relative simple reflection negates every root of its complete simple block. -/
theorem wordAction_sideWord_neg (s : Side) (r : F4Chevalley.Root)
    (hr : IsSimpleBlockRoot s true r) : wordAction (sideWord s) r = -r := by
  have hv (q : F4Chevalley.Root) : (-q).val = -q.val := by
    change typeF4RootPairing.root (-q) = -typeF4RootPairing.root q
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  have h := (positiveBlockRoots_simple_iff s r).mpr hr
  cases s with
  | linear =>
    obtain ⟨j, rfl⟩ := h
    apply Subtype.ext
    rw [hv]
    fin_cases j <;> funext k <;> fin_cases k <;>
      norm_num [wordAction, sideWord, Equiv.Perm.mul_apply,
        reflection_val, reflectedVector, rootBlocks_roots_val, RootPartition.index,
        RootPartition.pairRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]
  | suzuki =>
    obtain ⟨j, rfl⟩ := h
    apply Subtype.ext
    rw [hv]
    fin_cases j <;> funext k <;> fin_cases k <;>
      norm_num [wordAction, sideWord, Equiv.Perm.mul_apply,
        reflection_val, reflectedVector, rootBlocks_roots_val, RootPartition.index,
        RootPartition.quartetRow, RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

private lemma sidesWord_val (d : LocalBlockInput m) (w : List Side) :
    ((w.map (relativeWeyl d)).prod).val = simpleWord m (w.flatMap sideWord) := by
  induction w with
  | nil => simp [simpleWord]
  | cons s w ih =>
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, relativeWeyl_val,
      List.flatMap_cons, simpleWord_append, ih]

private lemma sidesWord_mem (d : LocalBlockInput m) (w : List Side) :
    (w.map (relativeWeyl d)).prod ∈ relativeWeylSubgroup d := by
  apply list_prod_mem
  intro x hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
  exact relativeWeyl_mem_subgroup d s

/-- All eight complete positive blocks are conjugates of their simple block. -/
theorem positiveBlock_weyl_orbit (d : LocalBlockInput m) (i : PositiveBlockIndex) :
    ∃ s, ∃ n : d.fixedGroup, n ∈ relativeWeylSubgroup d ∧
      splitPositiveBlock m i ≤
        (splitSimpleBlock m s true).map (MulAut.conj n.val).toMonoidHom := by
  let s : Side := match i with | .inl _ => .linear | .inr _ => .suzuki
  let n := ((orbitSides i).map (relativeWeyl d)).prod
  refine ⟨s, n, sidesWord_mem d _, ?_⟩
  apply (closure_le _).mpr
  rintro x ⟨r, t, hr, rfl⟩
  have hn : n.val = simpleWord m (orbitWord i) := sidesWord_val d _
  cases i with
  | inl i =>
    obtain ⟨j, rfl⟩ := hr
    refine ⟨rootGeneratorInGroup m
      ((rootBlocks .positive).roots (.inl ((0 : Fin 4), j))).val t, ?_, ?_⟩
    · apply Subgroup.subset_closure
      refine ⟨_, t, ?_, rfl⟩
      exact (positiveBlockRoots_simple_iff .linear _).mp ⟨j, rfl⟩
    · change n.val * _ * n.val⁻¹ = _
      rw [hn, simpleWord_conj_root, pair_orbit]
  | inr i =>
    obtain ⟨j, rfl⟩ := hr
    refine ⟨rootGeneratorInGroup m
      ((rootBlocks .positive).roots (.inr ((0 : Fin 4), j))).val t, ?_, ?_⟩
    · apply Subgroup.subset_closure
      refine ⟨_, t, ?_, rfl⟩
      exact (positiveBlockRoots_simple_iff .suzuki _).mp ⟨j, rfl⟩
    · change n.val * _ * n.val⁻¹ = _
      rw [hn, simpleWord_conj_root, quartet_orbit]
end
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection
