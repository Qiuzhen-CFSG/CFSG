module

public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Defs

/-!
# Native involutions with octad and empty fixed sets

Use the already certified Witt-design permutations, and check their actual
fixed coordinates. The first fixes precisely the octad obtained by extending
the native heptad. The second fixes no point. Both have order two.

Source: Aschbacher–Smith H.14.4(1), printed p.397. No assertion about
class coverage or Sylow centrality is made here.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad.Involutions
noncomputable section

abbrev z : M24 := M24InvolutionCentralizers.involution2A
abbrev t : M24 := M24InvolutionCentralizers.involution2B

lemma z_fixed_iff (i : Fin 24) : z • i = i ↔ i ∈ LinearFourCore.seedOctad.val := by
  rw [LinearFourCore.mem_seedOctad]
  revert i
  decide +kernel

lemma t_fixedPointFree (i : Fin 24) : t • i ≠ i := by
  revert i
  decide +kernel

/-- The representative with octad fixed set has order exactly two. -/
lemma z_order : orderOf z = 2 := M24InvolutionCentralizers.involution2A_order

/-- The fixed-point-free representative has order exactly two. -/
lemma t_order : orderOf t = 2 := M24InvolutionCentralizers.involution2B_order

lemma fixedPoints_z :
    Finset.univ.filter (fun i : Fin 24 => z • i = i) = LinearFourCore.seedOctad.val := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, z_fixed_iff]

lemma fixedPoints_z_octad :
    Finset.univ.filter (fun i : Fin 24 => z • i = i) ∈ m24Blocks := by
  rw [fixedPoints_z]
  exact LinearFourCore.seedOctad.property

lemma fixedPoints_t : Finset.univ.filter (fun i : Fin 24 => t • i = i) = ∅ := by
  simp [t_fixedPointFree]


end
end MathieuCode.CocodeOctad.Involutions
