module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer.Torus

/-!
# Separation of the eight split B₂ normalizer cosets

A two-coroot factor is diagonal with nonzero entries. It cannot change the
root supporting any column of a literal Weyl word. The images of the two
middle simple roots distinguish the eight split B₂ words, as witnessed by
their explicit coordinates. Thus these eight cosets remain distinct for
all coefficient fields, including the binary field.

Source: GLS3, 2.3.4–8 and the type V subsystem of §2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
open Parabolics Binary.FixedGeometry
noncomputable section
variable {m : ℕ}

private theorem sign (w : List typeF4RootPairing_base.support) (r : F4Chevalley.Root) :
    (titsWordSign w r : CoefficientField m) = 1 := by
  induction w with
  | nil => simp [titsWordSign]
  | cons i w ih => simp [titsWordSign, ih, CharTwo.neg_eq]

private theorem root_column (w : List (Fin 4)) (r : F4Chevalley.Root)
    (row : F4Chevalley.BasisIndex) :
    (simpleWord m w).val.val row (.inr r) =
      if row = .inr (reflectionWord (w.map typeF4RootPairing_baseEquiv) r) then 1 else 0 := by
  rw [simpleWord_coe]
  have h := congrFun (titsWord_mulVec_v (w.map typeF4RootPairing_baseEquiv) r) row
  simpa [v, Matrix.mulVec_single_one, Pi.single_apply, specializeMatrix, rootCurveTitsWord, sign] using
    congrArg (Int.castRingHom (CoefficientField m)) h

/-- Diagonal factors cannot change the reflected root of a Weyl word. -/
theorem torus_word_reflection_eq {a b c d : (CoefficientField m)ˣ}
    {l k : List (Fin 4)} (h : torus a b * simpleWord m l = torus c d * simpleWord m k)
    (r : F4Chevalley.Root) :
    reflectionWord (l.map typeF4RootPairing_baseEquiv) r =
      reflectionWord (k.map typeF4RootPairing_baseEquiv) r := by
  have hm := congrArg (fun g : SplitGroup m => g.val.val) h
  change (torus a b).val.val * (simpleWord m l).val.val =
    (torus c d).val.val * (simpleWord m k).val.val at hm
  rw [torus_matrix, torus_matrix] at hm
  let row : F4Chevalley.BasisIndex := .inr (reflectionWord (l.map typeF4RootPairing_baseEquiv) r)
  have he := congrArg (fun A => A row (.inr r)) hm
  simp only [Matrix.diagonal_mul, root_column] at he
  by_contra hne
  simp only [row, ite_true, mul_one, Sum.inr.injEq, if_neg hne, mul_zero] at he
  exact Units.ne_zero _ he

private def reflectionCoordinates (i : Fin 4) (v : Vec 4) : Vec 4 :=
  v - (dot v (typeF4SimpleRoot i) * (if i.val < 2 then 1 else 2)) • typeF4SimpleRoot i

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectionCoordinates i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp [reflectionCoordinates, typeF4SimpleRootIndex_val, mul_comm]

private def coordinateWord : List (Fin 4) → Vec 4 → Vec 4
  | [], v => v
  | i :: w, v => reflectionCoordinates i (coordinateWord w v)

private theorem word_val (w : List (Fin 4)) (r : F4Chevalley.Root) :
    (reflectionWord (w.map typeF4RootPairing_baseEquiv) r).val = coordinateWord w r.val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i)
      (reflectionWord (w.map typeF4RootPairing_baseEquiv) r)).val = _
    rw [reflection_val, ih]
    rfl

private def coordinateTable : Fin 8 → Fin 4 → ℤ :=
  ![![1,-1,0,1], ![-1,1,1,0], ![1,1,0,-1], ![1,1,-1,0],
    ![-1,-1,1,0], ![-1,-1,0,1], ![1,-1,-1,0], ![-1,1,0,-1]]

private def rootCoordinates (k : Fin 8) : Fin 4 → ℝ :=
  ![((reflectionWord ((word k).map typeF4RootPairing_baseEquiv) (typeF4SimpleRootIndex 1)).val) 2,
    ((reflectionWord ((word k).map typeF4RootPairing_baseEquiv) (typeF4SimpleRootIndex 1)).val) 3,
    ((reflectionWord ((word k).map typeF4RootPairing_baseEquiv) (typeF4SimpleRootIndex 2)).val) 2,
    ((reflectionWord ((word k).map typeF4RootPairing_baseEquiv) (typeF4SimpleRootIndex 2)).val) 3]

private theorem rootCoordinates_eq (k : Fin 8) (j : Fin 4) :
    rootCoordinates k j = (coordinateTable k j : ℝ) := by
  simp only [rootCoordinates, word_val, typeF4SimpleRootIndex_val]
  fin_cases k <;> fin_cases j <;>
    norm_num [word, coordinateWord, reflectionCoordinates, coordinateTable,
      typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk]

private theorem reflection_pair_injective : Function.Injective (fun k : Fin 8 =>
    (reflectionWord ((word k).map typeF4RootPairing_baseEquiv) (typeF4SimpleRootIndex 1),
     reflectionWord ((word k).map typeF4RootPairing_baseEquiv) (typeF4SimpleRootIndex 2))) := by
  intro i j h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only at h1 h2
  have hi : Function.Injective coordinateTable := by decide
  apply hi
  funext q
  have he : rootCoordinates i q = rootCoordinates j q := by
    simp only [rootCoordinates, h1, h2]
  rw [rootCoordinates_eq, rootCoordinates_eq] at he
  exact Int.cast_injective he

/-- The eight split B₂ representatives remain distinct after multiplying by
arbitrary two-coroot parameters. -/
theorem representative_unique {a b c d : (CoefficientField m)ˣ} {i j : Fin 8}
    (h : torus a b * representative m i = torus c d * representative m j) : i = j := by
  have h0 := torus_word_reflection_eq h (typeF4SimpleRootIndex 1)
  have h1 := torus_word_reflection_eq h (typeF4SimpleRootIndex 2)
  exact reflection_pair_injective (Prod.ext h0 h1)

end
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
