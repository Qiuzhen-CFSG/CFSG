module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer.Torus

/-!
# The split B₂ Weyl representatives and their Ree twist

The parameter-one middle lifts are involutions. The existing integral B₂
braid identity gives their eight-element multiplication table, uniformly
in the coefficient field. The Ree twist swaps the middle nodes; on this
table its only fixed representatives are the identity and the literal
long word `[1,2,1,2]`.

Source: GLS3, 2.3.4 and 2.4.8, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
open Parabolics Binary.FixedGeometry
noncomputable section
variable {m : ℕ}
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem root_inv (r : F4Chevalley.Root) (t : CoefficientField m) :
    (rootGeneratorInGroup m r t)⁻¹ = rootGeneratorInGroup m r t := by
  apply Subtype.ext
  exact (F4Chevalley.rootCurve_inv r t).trans (congrArg (F4Chevalley.rootCurve r) (CharTwo.neg_eq t))

theorem weyl_inv (r : F4Chevalley.Root) (t : CoefficientField m) :
    (weylWord m r t)⁻¹ = weylWord m r t := by
  simp only [weylWord, mul_inv_rev, root_inv, mul_assoc]

private theorem weyl_cancel (i : Fin 4) (x : SplitGroup m) :
    weylWord m (typeF4SimpleRootIndex i) 1 *
      (weylWord m (typeF4SimpleRootIndex i) 1 * x) = x := by
  simpa only [weyl_inv] using inv_mul_cancel_left (weylWord m (typeF4SimpleRootIndex i) 1) x

private theorem weyl_square (i : Fin 4) :
    weylWord m (typeF4SimpleRootIndex i) 1 * weylWord m (typeF4SimpleRootIndex i) 1 = 1 := by
  simpa only [weyl_inv] using inv_mul_cancel (weylWord m (typeF4SimpleRootIndex i) 1)

theorem middle_braid : simpleWord m [1,2,1,2] = simpleWord m [2,1,2,1] := by
  have h := sideWord_fixed m .suzuki
  rw [reeTwist_simpleWord] at h
  exact h.symm

def leftOne : Fin 8 → Fin 8 := ![1,0,3,2,5,4,7,6]
def leftTwo : Fin 8 → Fin 8 := ![2,4,0,6,1,7,3,5]

theorem left_one (k : Fin 8) :
    simpleWord m [1] * representative m k = representative m (leftOne k) := by
  fin_cases k <;>
    simp [representative, word, leftOne, simpleWord, weyl_cancel, weyl_square]

theorem left_two (k : Fin 8) :
    simpleWord m [2] * representative m k = representative m (leftTwo k) := by
  have hb := middle_braid (m := m)
  simp only [simpleWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] at hb
  fin_cases k <;>
    simp [representative, word, leftTwo, simpleWord, weyl_cancel, weyl_square]
  · exact hb.symm
  · rw [hb, weyl_cancel]

def twistIndex : Fin 8 → Fin 8 := ![0,2,1,4,3,6,5,7]

theorem twist_representative (d : LocalBlockInput m) (k : Fin 8) :
    d.twist (representative m k) = representative m (twistIndex k) := by
  rw [d.twist_eq_reeAutomorphism, reeAutomorphism_apply]
  change reeTwist m (simpleWord m (word k)) = _
  rw [reeTwist_simpleWord]
  fin_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_braid.symm

theorem twistIndex_fixed_iff (k : Fin 8) : twistIndex k = k ↔ k = 0 ∨ k = 7 := by
  fin_cases k <;> decide

end
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
