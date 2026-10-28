module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.RootActions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Generation by the original marked binary roots

The shear z ↦ zr and the two adjacent swaps of z,r,s generate Aut(Z).
We transport the standard SL₃(2) action through the original marked basis.
Each of its six elementary matrices is a short checked word in these three
operators; elementary generation then proves the assertion for all elements.
This extends the preceding radical root formulas to the full original K/R.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
local instance : IsElementaryAbelian 2 d.space := d.elementary

private noncomputable def markedSL : Matrix.PSL3Two.SL →* MulAut d.space where
  toFun a := MulEquiv.toAdditive.symm
    ((d.markedCoordinates.symm.trans a.toLin').trans d.markedCoordinates).toAddEquiv
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

private theorem markedSL_injective : Function.Injective d.markedSL := by
  intro a b he
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  apply d.markedCoordinates.injective
  have hh := congrArg (fun f : MulAut d.space =>
    Additive.ofMul (f (Additive.toMul (d.markedCoordinates v)))) he
  simpa [markedSL] using hh

private theorem markedSL_surjective : Function.Surjective d.markedSL := by
  apply (Nat.bijective_iff_injective_and_card d.markedSL).mpr
    ⟨d.markedSL_injective,?_⟩ |>.2
  rw [Matrix.PSL3Two.card_SL,card_mulAut_of_elementary_eight d.space d.card]

private def slShear : Matrix.PSL3Two.SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) 1
private def slSwap01 : Matrix.PSL3Two.SL :=
  ⟨!![0,1,0; 1,0,0; 0,0,1], by decide +kernel⟩
private def slSwap12 : Matrix.PSL3Two.SL :=
  ⟨!![1,0,0; 0,0,1; 0,1,0], by decide +kernel⟩

private theorem markedSL_coordinates (a : Matrix.PSL3Two.SL) (v : Fin 3 → ZMod 2) :
    d.markedSL a (Additive.toMul (d.markedCoordinates v)) =
      Additive.toMul (d.markedCoordinates (a.toLin' v)) := by
  simp [markedSL]

private theorem markedSL_point (a : Matrix.PSL3Two.SL) (i : Fin 3) :
    d.markedSL a (d.markedPoint i) =
      Additive.toMul (d.markedCoordinates (a.toLin' (Pi.single i 1))) := by
  simpa only [d.markedCoordinates_single,toMul_ofMul] using d.markedSL_coordinates a (Pi.single i 1)

set_option backward.isDefEq.respectTransparency false in
private theorem markedSL_shear : d.markedSL slShear = d.markedShear := by
  apply d.aut_ext_marked
  intro i
  rw [d.markedSL_point]
  fin_cases i
  · have he : slShear.toLin' (Pi.single 0 1) = Pi.single 0 1 + Pi.single 1 1 := by decide +kernel
    calc
      Additive.toMul (d.markedCoordinates (slShear.toLin' (Pi.single 0 1))) =
          Additive.toMul (Additive.ofMul (d.markedPoint 0) + Additive.ofMul (d.markedPoint 1)) := by rw [he,map_add,d.markedCoordinates_single,d.markedCoordinates_single]
      _ = d.markedPoint 0 * d.markedPoint 1 := rfl
      _ = d.markedShear (d.markedPoint 0) := d.markedShear_points.1.symm
  · have he : slShear.toLin' (Pi.single 1 1) = Pi.single 1 1 := by decide +kernel
    exact (congrArg (fun v => Additive.toMul (d.markedCoordinates v)) he).trans
      ((congrArg Additive.toMul (d.markedCoordinates_single 1)).trans d.markedShear_points.2.1.symm)
  · have he : slShear.toLin' (Pi.single 2 1) = Pi.single 2 1 := by decide +kernel
    exact (congrArg (fun v => Additive.toMul (d.markedCoordinates v)) he).trans
      ((congrArg Additive.toMul (d.markedCoordinates_single 2)).trans d.markedShear_points.2.2.symm)

private theorem markedSL_swap01 : d.markedSL slSwap01 = d.markedPermutation (Equiv.swap 0 1) := by
  apply d.aut_ext_marked
  intro i
  have he : slSwap01.toLin' (Pi.single i 1) = Pi.single ((Equiv.swap 0 1) i) 1 := by
    revert i; decide +kernel
  rw [d.markedPermutation_point,d.markedSL_point,he,d.markedCoordinates_single]
  rfl

private theorem markedSL_swap12 : d.markedSL slSwap12 = d.markedPermutation (Equiv.swap 1 2) := by
  apply d.aut_ext_marked
  intro i
  have he : slSwap12.toLin' (Pi.single i 1) = Pi.single ((Equiv.swap 1 2) i) 1 := by
    revert i; decide +kernel
  rw [d.markedPermutation_point,d.markedSL_point,he,d.markedCoordinates_single]
  rfl

/-- The original shear and two adjacent marked swaps generate the full three-space automorphism group. -/
theorem marked_roots_generate :
    closure ({d.markedShear, d.markedPermutation (Equiv.swap 0 1),
      d.markedPermutation (Equiv.swap 1 2)} : Set (MulAut d.space)) = ⊤ := by
  let H := closure ({d.markedShear, d.markedPermutation (Equiv.swap 0 1),
      d.markedPermutation (Equiv.swap 1 2)} : Set (MulAut d.space))
  have ha : d.markedSL slShear ∈ H := by rw [d.markedSL_shear]; exact subset_closure (by simp)
  have hp : d.markedSL slSwap01 ∈ H := by rw [d.markedSL_swap01]; exact subset_closure (by simp)
  have hq : d.markedSL slSwap12 ∈ H := by rw [d.markedSL_swap12]; exact subset_closure (by simp)
  have hword (w : List Matrix.PSL3Two.SL) (hw : ∀ g ∈ w, g = slShear ∨ g = slSwap01 ∨ g = slSwap12) :
      d.markedSL w.prod ∈ H := by
    rw [map_list_prod]
    exact H.list_prod_mem (fun x hx => by
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
      rcases hw g hg with rfl | rfl | rfl
      · exact ha
      · exact hp
      · exact hq)
  have ht (i j : Fin 3) (hij : i ≠ j) (c : ZMod 2) :
      d.markedSL (Matrix.SpecialLinearGroup.transvection hij c) ∈ H := by
    have hc : c=0 ∨ c=1 := by revert c; decide
    rcases hc with rfl | rfl
    · have he : Matrix.SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 := by
        apply Subtype.ext
        exact Matrix.transvection_zero i j
      rw [he,map_one]; exact H.one_mem
    fin_cases i <;> fin_cases j
    all_goals try contradiction
    · have he : Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1 =
          [slSwap01,slShear,slSwap01].prod := by decide +kernel
      rw [he]; exact hword _ (by simp)
    · have he : Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) 1 =
          [slSwap12,slSwap01,slShear,slSwap01,slSwap12].prod := by decide +kernel
      rw [he]; exact hword _ (by simp)
    · exact ha
    · have he : Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) 1 =
          [slSwap01,slSwap12,slSwap01,slShear,slSwap01,slSwap12,slSwap01].prod := by decide +kernel
      rw [he]; exact hword _ (by simp)
    · have he : Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0) 1 =
          [slSwap12,slShear,slSwap12].prod := by decide +kernel
      rw [he]; exact hword _ (by simp)
    · have he : Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1 =
          [slSwap01,slSwap12,slShear,slSwap12,slSwap01].prod := by decide +kernel
      rw [he]; exact hword _ (by simp)
  apply top_unique
  intro a _
  obtain ⟨g,rfl⟩ := d.markedSL_surjective a
  exact Atlas.sl_elementary_induction (fun g => d.markedSL g ∈ H) ht
    (fun a b ha hb => by rw [map_mul]; exact H.mul_mem ha hb) g

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
