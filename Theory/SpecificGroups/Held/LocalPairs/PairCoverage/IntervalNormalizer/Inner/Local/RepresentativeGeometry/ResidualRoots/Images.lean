module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Words

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.Orbits

/-!
# Images of the residual words in the marked six-point actions

The image calculation uses the certified action on each literal odd and two
word. In particular the second pair uses the certified outer S₆ twist.
Only products of the last two residual generators are needed for the roots.
-/

public section
open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots

private theorem map_conjugates {G H : Type*} [Group G] [Group H]
    (f : G →* H) (g : Fin 6 → G) (k : Fin 10) :
    f (conjugates g k) = conjugates (fun l => f (g l)) k := by
  fin_cases k <;> simp only [conjugates, map_mul, map_inv]

private theorem map_evalSigned {G H : Type*} [Group G] [Group H]
    (f : G →* H) (g : Fin 10 → G) (w : List (Fin 10 × Bool)) :
    f (evalSigned g w) = evalSigned (fun k => f (g k)) w := by
  simp only [evalSigned, map_list_prod, List.map_map, Function.comp_def, apply_ite, map_inv]

@[expose] def liftGenerator (i : Bool) (j : Fin 2) (k : Fin 8) : localOvergroup i :=
  evalSigned (conjugates (fun t => wordElement i (pairWord i j t))) (generatorWord i j k)

theorem liftGenerator_val (i : Bool) (j : Fin 2) (k : Fin 8) :
    (liftGenerator i j k : Held.He) = generator i j k := by
  change (localOvergroup i).subtype (liftGenerator i j k) = _
  rw [liftGenerator, map_evalSigned]
  simp only [map_conjugates]
  rfl

private theorem action_pairWord (i : Bool) (j : Fin 2) (k : Fin 6) :
    action i j (wordElement i (pairWord i j k)) = imageGenerator i j k := by
  fin_cases k
  · exact action_oddWord i j 0
  · exact action_oddWord i j 1
  · exact action_twoWord i j 0
  · exact action_twoWord i j 1
  · exact action_twoWord i j 2
  · exact action_twoWord i j 3

@[expose] def generatorImage (i : Bool) (j : Fin 2) (k : Fin 8) : Equiv.Perm (Fin 6) :=
  evalSigned (conjugates (imageGenerator i j)) (generatorWord i j k)

theorem action_liftGenerator (i : Bool) (j : Fin 2) (k : Fin 8) :
    action i j (liftGenerator i j k) = generatorImage i j k := by
  rw [liftGenerator, map_evalSigned]
  simp only [map_conjugates, action_pairWord]
  rfl

theorem rootOne_product (i : Bool) (j : Fin 2) :
    ((rootOneWord i j).map (generatorImage i j)).prod = rootOne i j := by
  cases i <;> fin_cases j <;> decide +kernel

theorem rootTwo_product (i : Bool) (j : Fin 2) :
    ((rootTwoWord i j).map (generatorImage i j)).prod = rootTwo i j := by
  cases i <;> fin_cases j <;> decide +kernel

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots
