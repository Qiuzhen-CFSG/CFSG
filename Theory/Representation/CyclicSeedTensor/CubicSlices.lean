module
public import Theory.Representation.CyclicSeedTensor.ThreeSlices

/-!
# A marked cubic on the binary plane

An invertible binary-plane map whose cube is one and which sends the first
basis vector to the second sends the second to their sum. This identifies
all three translates of the marked vector, including the extra trivial
coordinate used in the three-slice tensor product.

Source application: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.29(4), printed p.964. The cube condition distinguishes the required
cyclic choice from a transposition with the same first image.
-/

public section
namespace Representation.CyclicSeedTensor

/-- The first image and cube identity determine the second image. -/
theorem second_of_cube_eq_one (a : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) (ha : a ^ 3 = 1) (hf : a first = second) :
    a second = first + second := by
  have hz : a second ≠ 0 := a.map_ne_zero_iff.mpr (by decide)
  have hs : a second ≠ second := by
    intro he
    have hfs := a.injective (hf.trans he.symm)
    exact (by decide : (first : Fin 2 → ZMod 2) ≠ second) hfs
  have hn : a second ≠ first := by
    intro he
    have hh := congrArg (fun e : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) => e first) ha
    change a (a (a first)) = first at hh
    rw [hf,he,hf] at hh
    exact (by decide : (second : Fin 2 → ZMod 2) ≠ first) hh
  have cases : ∀ v : Fin 2 → ZMod 2, v = 0 ∨ v = first ∨ v = second ∨ v = first + second := by
    decide
  exact (cases (a second)).resolve_left hz |>.resolve_left hn |>.resolve_left hs


end Representation.CyclicSeedTensor
