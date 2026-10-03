module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusWitnessActions

/-!
# Fine-coordinate exclusions for the small parity census

For the 59 witnesses not separated by the tail quotient, binary polynomial
normal forms contain the corresponding generator closures but exclude the
witnesses. The free coordinates are the cyclic-four coordinate and selected
core coordinates; the remaining coordinates are polynomials over `ZMod 2`.

The kernel checks reconstruction at the identity and after every positive
generator step. Finite order then supplies inverse steps, and closure induction
proves reconstruction for every subgroup member. Neither reverse containment
nor exact subgroup orders are required.

Source: the root words of `SmallParityCensusNodes` and `SmallParityCensusWitnessActions`,
in the verified Shinoda (1975), (2.3), pp. 81–82, coordinate model. Diagnostic
polynomial interpolation selected these formulas; all identities used below are
checked in Lean, independently of that interpolation.
-/

namespace ReeTwo.SylowModel

private theorem outside_of_reconstruction {α : Type} (k : Fin 97)
    (element : α → SylowModel) (coordinates : SylowModel → α)
    (one : element (coordinates 1) = 1)
    (step : ∀ v j, element (coordinates (smallParityCensusWitnessGenerator k j * element v)) =
      smallParityCensusWitnessGenerator k j * element v)
    (outside : element (coordinates (smallParityCensusWitness k)) ≠ smallParityCensusWitness k) :
    smallParityCensusWitness k ∉ smallParityCensusNode (smallParityCensusWitnessIndex k) := by
  intro hx
  apply outside
  rw [smallParityCensusWitnessGenerator_closure] at hx
  generalize smallParityCensusWitness k = x at hx ⊢
  induction hx using Subgroup.closure_induction_left with
  | one => exact one
  | mul_left x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hx
    simpa only [ih] using step (coordinates y) j
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hx
    let g := smallParityCensusWitnessGenerator k j
    have hp : ∀ n : ℕ, element (coordinates (g ^ n * y)) = g ^ n * y := by
      intro n
      induction n with
      | zero => simpa using ih
      | succ n hn =>
        simpa only [hn, pow_succ', mul_assoc] using step (coordinates (g ^ n * y)) j
    have hinv : g ^ (orderOf g - 1) = g⁻¹ := by
      refine (inv_eq_of_mul_eq_one_right ?_).symm
      rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos (orderOf_pos g), pow_orderOf_eq_one]
    simpa only [hinv] using hp (orderOf g - 1)

-- Witness position 5; census node 21; 9 free binary coordinates.
private abbrev Params5 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element5 (v : Params5) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, v.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2⟩, v.1⟩
private def coordinates5 (x : SylowModel) : Params5 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step5 : ∀ (v : Params5) (j : Fin 9),
    element5 (coordinates5 (smallParityCensusWitnessGenerator 5 j * element5 v)) =
      smallParityCensusWitnessGenerator 5 j * element5 v := by
  decide +kernel
private theorem outside5 : smallParityCensusWitness 5 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 5) :=
  outside_of_reconstruction 5 element5 coordinates5
    (by decide +kernel) left_step5 (by decide +kernel)

-- Witness position 6; census node 24; 9 free binary coordinates.
private abbrev Params6 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element6 (v : Params6) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, v.2.1 + v.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2⟩, v.1⟩
private def coordinates6 (x : SylowModel) : Params6 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step6 : ∀ (v : Params6) (j : Fin 9),
    element6 (coordinates6 (smallParityCensusWitnessGenerator 6 j * element6 v)) =
      smallParityCensusWitnessGenerator 6 j * element6 v := by
  decide +kernel
private theorem outside6 : smallParityCensusWitness 6 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 6) :=
  outside_of_reconstruction 6 element6 coordinates6
    (by decide +kernel) left_step6 (by decide +kernel)

-- Witness position 7; census node 26; 9 free binary coordinates.
private abbrev Params7 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element7 (v : Params7) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2) + v.2.1 + v.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1, v.2.2.2.2.2.2.2⟩, v.1⟩
private def coordinates7 (x : SylowModel) : Params7 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step7 : ∀ (v : Params7) (j : Fin 9),
    element7 (coordinates7 (smallParityCensusWitnessGenerator 7 j * element7 v)) =
      smallParityCensusWitnessGenerator 7 j * element7 v := by
  decide +kernel
private theorem outside7 : smallParityCensusWitness 7 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 7) :=
  outside_of_reconstruction 7 element7 coordinates7
    (by decide +kernel) left_step7 (by decide +kernel)

-- Witness position 23; census node 43; 8 free binary coordinates.
private abbrev Params23 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element23 (v : Params23) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, 0, 0, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates23 (x : SylowModel) : Params23 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step23 : ∀ (v : Params23) (j : Fin 9),
    element23 (coordinates23 (smallParityCensusWitnessGenerator 23 j * element23 v)) =
      smallParityCensusWitnessGenerator 23 j * element23 v := by
  decide +kernel
private theorem outside23 : smallParityCensusWitness 23 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 23) :=
  outside_of_reconstruction 23 element23 coordinates23
    (by decide +kernel) left_step23 (by decide +kernel)

-- Witness position 24; census node 44; 8 free binary coordinates.
private abbrev Params24 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element24 (v : Params24) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, 0, v.2.1 + v.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates24 (x : SylowModel) : Params24 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step24 : ∀ (v : Params24) (j : Fin 9),
    element24 (coordinates24 (smallParityCensusWitnessGenerator 24 j * element24 v)) =
      smallParityCensusWitnessGenerator 24 j * element24 v := by
  decide +kernel
private theorem outside24 : smallParityCensusWitness 24 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 24) :=
  outside_of_reconstruction 24 element24 coordinates24
    (by decide +kernel) left_step24 (by decide +kernel)

-- Witness position 25; census node 46; 8 free binary coordinates.
private abbrev Params25 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element25 (v : Params25) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, v.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates25 (x : SylowModel) : Params25 :=
  (x.right, x.left.b2, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step25 : ∀ (v : Params25) (j : Fin 9),
    element25 (coordinates25 (smallParityCensusWitnessGenerator 25 j * element25 v)) =
      smallParityCensusWitnessGenerator 25 j * element25 v := by
  decide +kernel
private theorem outside25 : smallParityCensusWitness 25 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 25) :=
  outside_of_reconstruction 25 element25 coordinates25
    (by decide +kernel) left_step25 (by decide +kernel)

-- Witness position 26; census node 47; 8 free binary coordinates.
private abbrev Params26 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element26 (v : Params26) : SylowModel :=
  ⟨⟨0, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), v.2.2.1, v.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates26 (x : SylowModel) : Params26 :=
  (x.right, x.left.b2, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step26 : ∀ (v : Params26) (j : Fin 9),
    element26 (coordinates26 (smallParityCensusWitnessGenerator 26 j * element26 v)) =
      smallParityCensusWitnessGenerator 26 j * element26 v := by
  decide +kernel
private theorem outside26 : smallParityCensusWitness 26 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 26) :=
  outside_of_reconstruction 26 element26 coordinates26
    (by decide +kernel) left_step26 (by decide +kernel)

-- Witness position 27; census node 48; 8 free binary coordinates.
private abbrev Params27 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element27 (v : Params27) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates27 (x : SylowModel) : Params27 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step27 : ∀ (v : Params27) (j : Fin 9),
    element27 (coordinates27 (smallParityCensusWitnessGenerator 27 j * element27 v)) =
      smallParityCensusWitnessGenerator 27 j * element27 v := by
  decide +kernel
private theorem outside27 : smallParityCensusWitness 27 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 27) :=
  outside_of_reconstruction 27 element27 coordinates27
    (by decide +kernel) left_step27 (by decide +kernel)

-- Witness position 28; census node 49; 8 free binary coordinates.
private abbrev Params28 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element28 (v : Params28) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1 + v.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates28 (x : SylowModel) : Params28 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step28 : ∀ (v : Params28) (j : Fin 9),
    element28 (coordinates28 (smallParityCensusWitnessGenerator 28 j * element28 v)) =
      smallParityCensusWitnessGenerator 28 j * element28 v := by
  decide +kernel
private theorem outside28 : smallParityCensusWitness 28 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 28) :=
  outside_of_reconstruction 28 element28 coordinates28
    (by decide +kernel) left_step28 (by decide +kernel)

-- Witness position 29; census node 51; 8 free binary coordinates.
private abbrev Params29 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element29 (v : Params29) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates29 (x : SylowModel) : Params29 :=
  (x.right, x.left.b2, x.left.b5, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step29 : ∀ (v : Params29) (j : Fin 9),
    element29 (coordinates29 (smallParityCensusWitnessGenerator 29 j * element29 v)) =
      smallParityCensusWitnessGenerator 29 j * element29 v := by
  decide +kernel
private theorem outside29 : smallParityCensusWitness 29 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 29) :=
  outside_of_reconstruction 29 element29 coordinates29
    (by decide +kernel) left_step29 (by decide +kernel)

-- Witness position 30; census node 52; 8 free binary coordinates.
private abbrev Params30 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element30 (v : Params30) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, v.2.1 + v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates30 (x : SylowModel) : Params30 :=
  (x.right, x.left.b2, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step30 : ∀ (v : Params30) (j : Fin 9),
    element30 (coordinates30 (smallParityCensusWitnessGenerator 30 j * element30 v)) =
      smallParityCensusWitnessGenerator 30 j * element30 v := by
  decide +kernel
private theorem outside30 : smallParityCensusWitness 30 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 30) :=
  outside_of_reconstruction 30 element30 coordinates30
    (by decide +kernel) left_step30 (by decide +kernel)

-- Witness position 31; census node 53; 8 free binary coordinates.
private abbrev Params31 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element31 (v : Params31) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, 0, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates31 (x : SylowModel) : Params31 :=
  (x.right, x.left.b2, x.left.b5, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step31 : ∀ (v : Params31) (j : Fin 9),
    element31 (coordinates31 (smallParityCensusWitnessGenerator 31 j * element31 v)) =
      smallParityCensusWitnessGenerator 31 j * element31 v := by
  decide +kernel
private theorem outside31 : smallParityCensusWitness 31 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 31) :=
  outside_of_reconstruction 31 element31 coordinates31
    (by decide +kernel) left_step31 (by decide +kernel)

-- Witness position 32; census node 54; 8 free binary coordinates.
private abbrev Params32 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element32 (v : Params32) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates32 (x : SylowModel) : Params32 :=
  (x.right, x.left.b2, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step32 : ∀ (v : Params32) (j : Fin 9),
    element32 (coordinates32 (smallParityCensusWitnessGenerator 32 j * element32 v)) =
      smallParityCensusWitnessGenerator 32 j * element32 v := by
  decide +kernel
private theorem outside32 : smallParityCensusWitness 32 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 32) :=
  outside_of_reconstruction 32 element32 coordinates32
    (by decide +kernel) left_step32 (by decide +kernel)

-- Witness position 33; census node 55; 8 free binary coordinates.
private abbrev Params33 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element33 (v : Params33) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.1, v.2.1 + v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates33 (x : SylowModel) : Params33 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step33 : ∀ (v : Params33) (j : Fin 9),
    element33 (coordinates33 (smallParityCensusWitnessGenerator 33 j * element33 v)) =
      smallParityCensusWitnessGenerator 33 j * element33 v := by
  decide +kernel
private theorem outside33 : smallParityCensusWitness 33 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 33) :=
  outside_of_reconstruction 33 element33 coordinates33
    (by decide +kernel) left_step33 (by decide +kernel)

-- Witness position 34; census node 56; 8 free binary coordinates.
private abbrev Params34 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element34 (v : Params34) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.1, v.2.1 + v.2.2.1 + v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates34 (x : SylowModel) : Params34 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step34 : ∀ (v : Params34) (j : Fin 9),
    element34 (coordinates34 (smallParityCensusWitnessGenerator 34 j * element34 v)) =
      smallParityCensusWitnessGenerator 34 j * element34 v := by
  decide +kernel
private theorem outside34 : smallParityCensusWitness 34 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 34) :=
  outside_of_reconstruction 34 element34 coordinates34
    (by decide +kernel) left_step34 (by decide +kernel)

-- Witness position 35; census node 57; 8 free binary coordinates.
private abbrev Params35 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element35 (v : Params35) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.1, v.2.2.1 + v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates35 (x : SylowModel) : Params35 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step35 : ∀ (v : Params35) (j : Fin 9),
    element35 (coordinates35 (smallParityCensusWitnessGenerator 35 j * element35 v)) =
      smallParityCensusWitnessGenerator 35 j * element35 v := by
  decide +kernel
private theorem outside35 : smallParityCensusWitness 35 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 35) :=
  outside_of_reconstruction 35 element35 coordinates35
    (by decide +kernel) left_step35 (by decide +kernel)

-- Witness position 36; census node 58; 8 free binary coordinates.
private abbrev Params36 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element36 (v : Params36) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates36 (x : SylowModel) : Params36 :=
  (x.right, x.left.b2, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step36 : ∀ (v : Params36) (j : Fin 9),
    element36 (coordinates36 (smallParityCensusWitnessGenerator 36 j * element36 v)) =
      smallParityCensusWitnessGenerator 36 j * element36 v := by
  decide +kernel
private theorem outside36 : smallParityCensusWitness 36 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 36) :=
  outside_of_reconstruction 36 element36 coordinates36
    (by decide +kernel) left_step36 (by decide +kernel)

-- Witness position 37; census node 59; 8 free binary coordinates.
private abbrev Params37 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element37 (v : Params37) : SylowModel :=
  ⟨⟨((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.1, v.2.2.1, v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩, v.1⟩
private def coordinates37 (x : SylowModel) : Params37 :=
  (x.right, x.left.b3, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step37 : ∀ (v : Params37) (j : Fin 9),
    element37 (coordinates37 (smallParityCensusWitnessGenerator 37 j * element37 v)) =
      smallParityCensusWitnessGenerator 37 j * element37 v := by
  decide +kernel
private theorem outside37 : smallParityCensusWitness 37 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 37) :=
  outside_of_reconstruction 37 element37 coordinates37
    (by decide +kernel) left_step37 (by decide +kernel)

-- Witness position 39; census node 62; 7 free binary coordinates.
private abbrev Params39 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element39 (v : Params39) : SylowModel :=
  ⟨⟨0, 0, 0, 0, v.2.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates39 (x : SylowModel) : Params39 :=
  (x.right, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step39 : ∀ (v : Params39) (j : Fin 9),
    element39 (coordinates39 (smallParityCensusWitnessGenerator 39 j * element39 v)) =
      smallParityCensusWitnessGenerator 39 j * element39 v := by
  decide +kernel
private theorem outside39 : smallParityCensusWitness 39 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 39) :=
  outside_of_reconstruction 39 element39 coordinates39
    (by decide +kernel) left_step39 (by decide +kernel)

-- Witness position 42; census node 65; 7 free binary coordinates.
private abbrev Params42 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element42 (v : Params42) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.1, v.2.2.1, v.2.1, v.2.1 + v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates42 (x : SylowModel) : Params42 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step42 : ∀ (v : Params42) (j : Fin 9),
    element42 (coordinates42 (smallParityCensusWitnessGenerator 42 j * element42 v)) =
      smallParityCensusWitnessGenerator 42 j * element42 v := by
  decide +kernel
private theorem outside42 : smallParityCensusWitness 42 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 42) :=
  outside_of_reconstruction 42 element42 coordinates42
    (by decide +kernel) left_step42 (by decide +kernel)

-- Witness position 43; census node 66; 7 free binary coordinates.
private abbrev Params43 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element43 (v : Params43) : SylowModel :=
  ⟨⟨0, 0, v.2.1, v.2.1, v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates43 (x : SylowModel) : Params43 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step43 : ∀ (v : Params43) (j : Fin 9),
    element43 (coordinates43 (smallParityCensusWitnessGenerator 43 j * element43 v)) =
      smallParityCensusWitnessGenerator 43 j * element43 v := by
  decide +kernel
private theorem outside43 : smallParityCensusWitness 43 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 43) :=
  outside_of_reconstruction 43 element43 coordinates43
    (by decide +kernel) left_step43 (by decide +kernel)

-- Witness position 47; census node 70; 7 free binary coordinates.
private abbrev Params47 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element47 (v : Params47) : SylowModel :=
  ⟨⟨0, 0, 0, ((v.1.toAdd.val : ℕ) : ZMod 2), v.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates47 (x : SylowModel) : Params47 :=
  (x.right, x.left.b4, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step47 : ∀ (v : Params47) (j : Fin 9),
    element47 (coordinates47 (smallParityCensusWitnessGenerator 47 j * element47 v)) =
      smallParityCensusWitnessGenerator 47 j * element47 v := by
  decide +kernel
private theorem outside47 : smallParityCensusWitness 47 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 47) :=
  outside_of_reconstruction 47 element47 coordinates47
    (by decide +kernel) left_step47 (by decide +kernel)

-- Witness position 50; census node 73; 7 free binary coordinates.
private abbrev Params50 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element50 (v : Params50) : SylowModel :=
  ⟨⟨0, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2) + v.2.1, v.2.2.1, v.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates50 (x : SylowModel) : Params50 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step50 : ∀ (v : Params50) (j : Fin 9),
    element50 (coordinates50 (smallParityCensusWitnessGenerator 50 j * element50 v)) =
      smallParityCensusWitnessGenerator 50 j * element50 v := by
  decide +kernel
private theorem outside50 : smallParityCensusWitness 50 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 50) :=
  outside_of_reconstruction 50 element50 coordinates50
    (by decide +kernel) left_step50 (by decide +kernel)

-- Witness position 51; census node 74; 7 free binary coordinates.
private abbrev Params51 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element51 (v : Params51) : SylowModel :=
  ⟨⟨0, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2) + v.2.1, v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates51 (x : SylowModel) : Params51 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step51 : ∀ (v : Params51) (j : Fin 9),
    element51 (coordinates51 (smallParityCensusWitnessGenerator 51 j * element51 v)) =
      smallParityCensusWitnessGenerator 51 j * element51 v := by
  decide +kernel
private theorem outside51 : smallParityCensusWitness 51 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 51) :=
  outside_of_reconstruction 51 element51 coordinates51
    (by decide +kernel) left_step51 (by decide +kernel)

-- Witness position 54; census node 82; 7 free binary coordinates.
private abbrev Params54 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element54 (v : Params54) : SylowModel :=
  ⟨⟨0, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), v.2.2.1, 0, 0, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates54 (x : SylowModel) : Params54 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step54 : ∀ (v : Params54) (j : Fin 9),
    element54 (coordinates54 (smallParityCensusWitnessGenerator 54 j * element54 v)) =
      smallParityCensusWitnessGenerator 54 j * element54 v := by
  decide +kernel
private theorem outside54 : smallParityCensusWitness 54 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 54) :=
  outside_of_reconstruction 54 element54 coordinates54
    (by decide +kernel) left_step54 (by decide +kernel)

-- Witness position 55; census node 83; 7 free binary coordinates.
private abbrev Params55 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element55 (v : Params55) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.1, 0, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates55 (x : SylowModel) : Params55 :=
  (x.right, x.left.b2, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step55 : ∀ (v : Params55) (j : Fin 9),
    element55 (coordinates55 (smallParityCensusWitnessGenerator 55 j * element55 v)) =
      smallParityCensusWitnessGenerator 55 j * element55 v := by
  decide +kernel
private theorem outside55 : smallParityCensusWitness 55 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 55) :=
  outside_of_reconstruction 55 element55 coordinates55
    (by decide +kernel) left_step55 (by decide +kernel)

-- Witness position 56; census node 84; 7 free binary coordinates.
private abbrev Params56 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element56 (v : Params56) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, 0, v.2.1 + v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates56 (x : SylowModel) : Params56 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step56 : ∀ (v : Params56) (j : Fin 9),
    element56 (coordinates56 (smallParityCensusWitnessGenerator 56 j * element56 v)) =
      smallParityCensusWitnessGenerator 56 j * element56 v := by
  decide +kernel
private theorem outside56 : smallParityCensusWitness 56 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 56) :=
  outside_of_reconstruction 56 element56 coordinates56
    (by decide +kernel) left_step56 (by decide +kernel)

-- Witness position 57; census node 85; 7 free binary coordinates.
private abbrev Params57 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element57 (v : Params57) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, 0, 0, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates57 (x : SylowModel) : Params57 :=
  (x.right, x.left.b2, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step57 : ∀ (v : Params57) (j : Fin 9),
    element57 (coordinates57 (smallParityCensusWitnessGenerator 57 j * element57 v)) =
      smallParityCensusWitnessGenerator 57 j * element57 v := by
  decide +kernel
private theorem outside57 : smallParityCensusWitness 57 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 57) :=
  outside_of_reconstruction 57 element57 coordinates57
    (by decide +kernel) left_step57 (by decide +kernel)

-- Witness position 58; census node 86; 7 free binary coordinates.
private abbrev Params58 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element58 (v : Params58) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, 0, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates58 (x : SylowModel) : Params58 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step58 : ∀ (v : Params58) (j : Fin 9),
    element58 (coordinates58 (smallParityCensusWitnessGenerator 58 j * element58 v)) =
      smallParityCensusWitnessGenerator 58 j * element58 v := by
  decide +kernel
private theorem outside58 : smallParityCensusWitness 58 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 58) :=
  outside_of_reconstruction 58 element58 coordinates58
    (by decide +kernel) left_step58 (by decide +kernel)

-- Witness position 59; census node 87; 7 free binary coordinates.
private abbrev Params59 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element59 (v : Params59) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates59 (x : SylowModel) : Params59 :=
  (x.right, x.left.b2, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step59 : ∀ (v : Params59) (j : Fin 9),
    element59 (coordinates59 (smallParityCensusWitnessGenerator 59 j * element59 v)) =
      smallParityCensusWitnessGenerator 59 j * element59 v := by
  decide +kernel
private theorem outside59 : smallParityCensusWitness 59 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 59) :=
  outside_of_reconstruction 59 element59 coordinates59
    (by decide +kernel) left_step59 (by decide +kernel)

-- Witness position 60; census node 88; 7 free binary coordinates.
private abbrev Params60 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element60 (v : Params60) : SylowModel :=
  ⟨⟨0, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates60 (x : SylowModel) : Params60 :=
  (x.right, x.left.b2, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step60 : ∀ (v : Params60) (j : Fin 9),
    element60 (coordinates60 (smallParityCensusWitnessGenerator 60 j * element60 v)) =
      smallParityCensusWitnessGenerator 60 j * element60 v := by
  decide +kernel
private theorem outside60 : smallParityCensusWitness 60 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 60) :=
  outside_of_reconstruction 60 element60 coordinates60
    (by decide +kernel) left_step60 (by decide +kernel)

-- Witness position 61; census node 90; 7 free binary coordinates.
private abbrev Params61 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element61 (v : Params61) : SylowModel :=
  ⟨⟨0, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates61 (x : SylowModel) : Params61 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step61 : ∀ (v : Params61) (j : Fin 9),
    element61 (coordinates61 (smallParityCensusWitnessGenerator 61 j * element61 v)) =
      smallParityCensusWitnessGenerator 61 j * element61 v := by
  decide +kernel
private theorem outside61 : smallParityCensusWitness 61 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 61) :=
  outside_of_reconstruction 61 element61 coordinates61
    (by decide +kernel) left_step61 (by decide +kernel)

-- Witness position 62; census node 91; 7 free binary coordinates.
private abbrev Params62 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element62 (v : Params62) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates62 (x : SylowModel) : Params62 :=
  (x.right, x.left.b2, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step62 : ∀ (v : Params62) (j : Fin 9),
    element62 (coordinates62 (smallParityCensusWitnessGenerator 62 j * element62 v)) =
      smallParityCensusWitnessGenerator 62 j * element62 v := by
  decide +kernel
private theorem outside62 : smallParityCensusWitness 62 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 62) :=
  outside_of_reconstruction 62 element62 coordinates62
    (by decide +kernel) left_step62 (by decide +kernel)

-- Witness position 63; census node 92; 7 free binary coordinates.
private abbrev Params63 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element63 (v : Params63) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1 + v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates63 (x : SylowModel) : Params63 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step63 : ∀ (v : Params63) (j : Fin 9),
    element63 (coordinates63 (smallParityCensusWitnessGenerator 63 j * element63 v)) =
      smallParityCensusWitnessGenerator 63 j * element63 v := by
  decide +kernel
private theorem outside63 : smallParityCensusWitness 63 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 63) :=
  outside_of_reconstruction 63 element63 coordinates63
    (by decide +kernel) left_step63 (by decide +kernel)

-- Witness position 64; census node 93; 7 free binary coordinates.
private abbrev Params64 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element64 (v : Params64) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, 0, ((v.1.toAdd.val : ℕ) : ZMod 2), v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates64 (x : SylowModel) : Params64 :=
  (x.right, x.left.b2, x.left.b6, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step64 : ∀ (v : Params64) (j : Fin 9),
    element64 (coordinates64 (smallParityCensusWitnessGenerator 64 j * element64 v)) =
      smallParityCensusWitnessGenerator 64 j * element64 v := by
  decide +kernel
private theorem outside64 : smallParityCensusWitness 64 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 64) :=
  outside_of_reconstruction 64 element64 coordinates64
    (by decide +kernel) left_step64 (by decide +kernel)

-- Witness position 65; census node 94; 7 free binary coordinates.
private abbrev Params65 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element65 (v : Params65) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates65 (x : SylowModel) : Params65 :=
  (x.right, x.left.b2, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step65 : ∀ (v : Params65) (j : Fin 9),
    element65 (coordinates65 (smallParityCensusWitnessGenerator 65 j * element65 v)) =
      smallParityCensusWitnessGenerator 65 j * element65 v := by
  decide +kernel
private theorem outside65 : smallParityCensusWitness 65 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 65) :=
  outside_of_reconstruction 65 element65 coordinates65
    (by decide +kernel) left_step65 (by decide +kernel)

-- Witness position 66; census node 95; 7 free binary coordinates.
private abbrev Params66 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element66 (v : Params66) : SylowModel :=
  ⟨⟨((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.1, v.2.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + v.2.2.1, v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩, v.1⟩
private def coordinates66 (x : SylowModel) : Params66 :=
  (x.right, x.left.b3, x.left.b4, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step66 : ∀ (v : Params66) (j : Fin 9),
    element66 (coordinates66 (smallParityCensusWitnessGenerator 66 j * element66 v)) =
      smallParityCensusWitnessGenerator 66 j * element66 v := by
  decide +kernel
private theorem outside66 : smallParityCensusWitness 66 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 66) :=
  outside_of_reconstruction 66 element66 coordinates66
    (by decide +kernel) left_step66 (by decide +kernel)

-- Witness position 73; census node 103; 6 free binary coordinates.
private abbrev Params73 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element73 (v : Params73) : SylowModel :=
  ⟨⟨0, 0, 0, v.2.1, v.2.2.1, 0, 0, 0, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates73 (x : SylowModel) : Params73 :=
  (x.right, x.left.b3, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step73 : ∀ (v : Params73) (j : Fin 9),
    element73 (coordinates73 (smallParityCensusWitnessGenerator 73 j * element73 v)) =
      smallParityCensusWitnessGenerator 73 j * element73 v := by
  decide +kernel
private theorem outside73 : smallParityCensusWitness 73 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 73) :=
  outside_of_reconstruction 73 element73 coordinates73
    (by decide +kernel) left_step73 (by decide +kernel)

-- Witness position 74; census node 104; 6 free binary coordinates.
private abbrev Params74 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element74 (v : Params74) : SylowModel :=
  ⟨⟨0, 0, 0, v.2.1, v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates74 (x : SylowModel) : Params74 :=
  (x.right, x.left.b3, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step74 : ∀ (v : Params74) (j : Fin 9),
    element74 (coordinates74 (smallParityCensusWitnessGenerator 74 j * element74 v)) =
      smallParityCensusWitnessGenerator 74 j * element74 v := by
  decide +kernel
private theorem outside74 : smallParityCensusWitness 74 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 74) :=
  outside_of_reconstruction 74 element74 coordinates74
    (by decide +kernel) left_step74 (by decide +kernel)

-- Witness position 75; census node 105; 6 free binary coordinates.
private abbrev Params75 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element75 (v : Params75) : SylowModel :=
  ⟨⟨0, 0, 0, v.2.1, v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1 + v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates75 (x : SylowModel) : Params75 :=
  (x.right, x.left.b3, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step75 : ∀ (v : Params75) (j : Fin 9),
    element75 (coordinates75 (smallParityCensusWitnessGenerator 75 j * element75 v)) =
      smallParityCensusWitnessGenerator 75 j * element75 v := by
  decide +kernel
private theorem outside75 : smallParityCensusWitness 75 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 75) :=
  outside_of_reconstruction 75 element75 coordinates75
    (by decide +kernel) left_step75 (by decide +kernel)

-- Witness position 76; census node 106; 6 free binary coordinates.
private abbrev Params76 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element76 (v : Params76) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, 0, 0, 0, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates76 (x : SylowModel) : Params76 :=
  (x.right, x.left.b2, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step76 : ∀ (v : Params76) (j : Fin 9),
    element76 (coordinates76 (smallParityCensusWitnessGenerator 76 j * element76 v)) =
      smallParityCensusWitnessGenerator 76 j * element76 v := by
  decide +kernel
private theorem outside76 : smallParityCensusWitness 76 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 76) :=
  outside_of_reconstruction 76 element76 coordinates76
    (by decide +kernel) left_step76 (by decide +kernel)

-- Witness position 77; census node 107; 6 free binary coordinates.
private abbrev Params77 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element77 (v : Params77) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.1, 0, 0, v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates77 (x : SylowModel) : Params77 :=
  (x.right, x.left.b2, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step77 : ∀ (v : Params77) (j : Fin 9),
    element77 (coordinates77 (smallParityCensusWitnessGenerator 77 j * element77 v)) =
      smallParityCensusWitnessGenerator 77 j * element77 v := by
  decide +kernel
private theorem outside77 : smallParityCensusWitness 77 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 77) :=
  outside_of_reconstruction 77 element77 coordinates77
    (by decide +kernel) left_step77 (by decide +kernel)

-- Witness position 78; census node 108; 6 free binary coordinates.
private abbrev Params78 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element78 (v : Params78) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, 0, 0, v.2.1 + v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates78 (x : SylowModel) : Params78 :=
  (x.right, x.left.b2, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step78 : ∀ (v : Params78) (j : Fin 9),
    element78 (coordinates78 (smallParityCensusWitnessGenerator 78 j * element78 v)) =
      smallParityCensusWitnessGenerator 78 j * element78 v := by
  decide +kernel
private theorem outside78 : smallParityCensusWitness 78 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 78) :=
  outside_of_reconstruction 78 element78 coordinates78
    (by decide +kernel) left_step78 (by decide +kernel)

-- Witness position 79; census node 109; 6 free binary coordinates.
private abbrev Params79 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element79 (v : Params79) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, 0, 0, 0, v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates79 (x : SylowModel) : Params79 :=
  (x.right, x.left.b2, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step79 : ∀ (v : Params79) (j : Fin 9),
    element79 (coordinates79 (smallParityCensusWitnessGenerator 79 j * element79 v)) =
      smallParityCensusWitnessGenerator 79 j * element79 v := by
  decide +kernel
private theorem outside79 : smallParityCensusWitness 79 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 79) :=
  outside_of_reconstruction 79 element79 coordinates79
    (by decide +kernel) left_step79 (by decide +kernel)

-- Witness position 80; census node 110; 6 free binary coordinates.
private abbrev Params80 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element80 (v : Params80) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates80 (x : SylowModel) : Params80 :=
  (x.right, x.left.b2, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step80 : ∀ (v : Params80) (j : Fin 9),
    element80 (coordinates80 (smallParityCensusWitnessGenerator 80 j * element80 v)) =
      smallParityCensusWitnessGenerator 80 j * element80 v := by
  decide +kernel
private theorem outside80 : smallParityCensusWitness 80 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 80) :=
  outside_of_reconstruction 80 element80 coordinates80
    (by decide +kernel) left_step80 (by decide +kernel)

-- Witness position 81; census node 111; 6 free binary coordinates.
private abbrev Params81 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element81 (v : Params81) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates81 (x : SylowModel) : Params81 :=
  (x.right, x.left.b2, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step81 : ∀ (v : Params81) (j : Fin 9),
    element81 (coordinates81 (smallParityCensusWitnessGenerator 81 j * element81 v)) =
      smallParityCensusWitnessGenerator 81 j * element81 v := by
  decide +kernel
private theorem outside81 : smallParityCensusWitness 81 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 81) :=
  outside_of_reconstruction 81 element81 coordinates81
    (by decide +kernel) left_step81 (by decide +kernel)

-- Witness position 82; census node 112; 6 free binary coordinates.
private abbrev Params82 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element82 (v : Params82) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1 + v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates82 (x : SylowModel) : Params82 :=
  (x.right, x.left.b2, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step82 : ∀ (v : Params82) (j : Fin 9),
    element82 (coordinates82 (smallParityCensusWitnessGenerator 82 j * element82 v)) =
      smallParityCensusWitnessGenerator 82 j * element82 v := by
  decide +kernel
private theorem outside82 : smallParityCensusWitness 82 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 82) :=
  outside_of_reconstruction 82 element82 coordinates82
    (by decide +kernel) left_step82 (by decide +kernel)

-- Witness position 83; census node 113; 6 free binary coordinates.
private abbrev Params83 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element83 (v : Params83) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, 0, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates83 (x : SylowModel) : Params83 :=
  (x.right, x.left.b2, x.left.b7, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step83 : ∀ (v : Params83) (j : Fin 9),
    element83 (coordinates83 (smallParityCensusWitnessGenerator 83 j * element83 v)) =
      smallParityCensusWitnessGenerator 83 j * element83 v := by
  decide +kernel
private theorem outside83 : smallParityCensusWitness 83 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 83) :=
  outside_of_reconstruction 83 element83 coordinates83
    (by decide +kernel) left_step83 (by decide +kernel)

-- Witness position 84; census node 114; 6 free binary coordinates.
private abbrev Params84 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element84 (v : Params84) : SylowModel :=
  ⟨⟨((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.1, v.2.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + v.2.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.2.1, v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.1 + v.2.2.1 + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates84 (x : SylowModel) : Params84 :=
  (x.right, x.left.b3, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step84 : ∀ (v : Params84) (j : Fin 9),
    element84 (coordinates84 (smallParityCensusWitnessGenerator 84 j * element84 v)) =
      smallParityCensusWitnessGenerator 84 j * element84 v := by
  decide +kernel
private theorem outside84 : smallParityCensusWitness 84 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 84) :=
  outside_of_reconstruction 84 element84 coordinates84
    (by decide +kernel) left_step84 (by decide +kernel)

-- Witness position 85; census node 115; 6 free binary coordinates.
private abbrev Params85 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private def element85 (v : Params85) : SylowModel :=
  ⟨⟨((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.1, v.2.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + v.2.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.1 + v.2.2.1 + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩, v.1⟩
private def coordinates85 (x : SylowModel) : Params85 :=
  (x.right, x.left.b3, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step85 : ∀ (v : Params85) (j : Fin 9),
    element85 (coordinates85 (smallParityCensusWitnessGenerator 85 j * element85 v)) =
      smallParityCensusWitnessGenerator 85 j * element85 v := by
  decide +kernel
private theorem outside85 : smallParityCensusWitness 85 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 85) :=
  outside_of_reconstruction 85 element85 coordinates85
    (by decide +kernel) left_step85 (by decide +kernel)

-- Witness position 86; census node 117; 5 free binary coordinates.
private abbrev Params86 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2
private def element86 (v : Params86) : SylowModel :=
  ⟨⟨0, 0, 0, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.1, v.2.2.2⟩, v.1⟩
private def coordinates86 (x : SylowModel) : Params86 :=
  (x.right, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step86 : ∀ (v : Params86) (j : Fin 9),
    element86 (coordinates86 (smallParityCensusWitnessGenerator 86 j * element86 v)) =
      smallParityCensusWitnessGenerator 86 j * element86 v := by
  decide +kernel
private theorem outside86 : smallParityCensusWitness 86 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 86) :=
  outside_of_reconstruction 86 element86 coordinates86
    (by decide +kernel) left_step86 (by decide +kernel)

-- Witness position 87; census node 118; 5 free binary coordinates.
private abbrev Params87 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2
private def element87 (v : Params87) : SylowModel :=
  ⟨⟨0, 0, 0, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1, v.2.2.1, v.2.2.2⟩, v.1⟩
private def coordinates87 (x : SylowModel) : Params87 :=
  (x.right, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step87 : ∀ (v : Params87) (j : Fin 9),
    element87 (coordinates87 (smallParityCensusWitnessGenerator 87 j * element87 v)) =
      smallParityCensusWitnessGenerator 87 j * element87 v := by
  decide +kernel
private theorem outside87 : smallParityCensusWitness 87 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 87) :=
  outside_of_reconstruction 87 element87 coordinates87
    (by decide +kernel) left_step87 (by decide +kernel)

-- Witness position 90; census node 122; 5 free binary coordinates.
private abbrev Params90 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2
private def element90 (v : Params90) : SylowModel :=
  ⟨⟨0, 0, 0, ((v.1.toAdd.val : ℕ) : ZMod 2), v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1, v.2.2.1, v.2.2.2⟩, v.1⟩
private def coordinates90 (x : SylowModel) : Params90 :=
  (x.right, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step90 : ∀ (v : Params90) (j : Fin 9),
    element90 (coordinates90 (smallParityCensusWitnessGenerator 90 j * element90 v)) =
      smallParityCensusWitnessGenerator 90 j * element90 v := by
  decide +kernel
private theorem outside90 : smallParityCensusWitness 90 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 90) :=
  outside_of_reconstruction 90 element90 coordinates90
    (by decide +kernel) left_step90 (by decide +kernel)

-- Witness position 91; census node 123; 5 free binary coordinates.
private abbrev Params91 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2
private def element91 (v : Params91) : SylowModel :=
  ⟨⟨0, 0, 0, ((v.1.toAdd.val : ℕ) : ZMod 2), v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.1, v.2.2.2⟩, v.1⟩
private def coordinates91 (x : SylowModel) : Params91 :=
  (x.right, x.left.b4, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step91 : ∀ (v : Params91) (j : Fin 9),
    element91 (coordinates91 (smallParityCensusWitnessGenerator 91 j * element91 v)) =
      smallParityCensusWitnessGenerator 91 j * element91 v := by
  decide +kernel
private theorem outside91 : smallParityCensusWitness 91 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 91) :=
  outside_of_reconstruction 91 element91 coordinates91
    (by decide +kernel) left_step91 (by decide +kernel)

-- Witness position 92; census node 126; 5 free binary coordinates.
private abbrev Params92 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2
private def element92 (v : Params92) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.1, v.2.2.2⟩, v.1⟩
private def coordinates92 (x : SylowModel) : Params92 :=
  (x.right, x.left.b2, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step92 : ∀ (v : Params92) (j : Fin 9),
    element92 (coordinates92 (smallParityCensusWitnessGenerator 92 j * element92 v)) =
      smallParityCensusWitnessGenerator 92 j * element92 v := by
  decide +kernel
private theorem outside92 : smallParityCensusWitness 92 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 92) :=
  outside_of_reconstruction 92 element92 coordinates92
    (by decide +kernel) left_step92 (by decide +kernel)

-- Witness position 93; census node 127; 5 free binary coordinates.
private abbrev Params93 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2
private def element93 (v : Params93) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, ((v.1.toAdd.val : ℕ) : ZMod 2) + v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.1, v.2.2.2⟩, v.1⟩
private def coordinates93 (x : SylowModel) : Params93 :=
  (x.right, x.left.b2, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step93 : ∀ (v : Params93) (j : Fin 9),
    element93 (coordinates93 (smallParityCensusWitnessGenerator 93 j * element93 v)) =
      smallParityCensusWitnessGenerator 93 j * element93 v := by
  decide +kernel
private theorem outside93 : smallParityCensusWitness 93 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 93) :=
  outside_of_reconstruction 93 element93 coordinates93
    (by decide +kernel) left_step93 (by decide +kernel)

-- Witness position 94; census node 128; 5 free binary coordinates.
private abbrev Params94 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2 × ZMod 2
private def element94 (v : Params94) : SylowModel :=
  ⟨⟨0, 0, v.2.1, 0, 0, ((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.2.1, v.2.2.2⟩, v.1⟩
private def coordinates94 (x : SylowModel) : Params94 :=
  (x.right, x.left.b2, x.left.b8, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step94 : ∀ (v : Params94) (j : Fin 9),
    element94 (coordinates94 (smallParityCensusWitnessGenerator 94 j * element94 v)) =
      smallParityCensusWitnessGenerator 94 j * element94 v := by
  decide +kernel
private theorem outside94 : smallParityCensusWitness 94 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 94) :=
  outside_of_reconstruction 94 element94 coordinates94
    (by decide +kernel) left_step94 (by decide +kernel)

-- Witness position 95; census node 129; 4 free binary coordinates.
private abbrev Params95 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2
private def element95 (v : Params95) : SylowModel :=
  ⟨⟨((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1 + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.1, v.2.2⟩, v.1⟩
private def coordinates95 (x : SylowModel) : Params95 :=
  (x.right, x.left.b4, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step95 : ∀ (v : Params95) (j : Fin 9),
    element95 (coordinates95 (smallParityCensusWitnessGenerator 95 j * element95 v)) =
      smallParityCensusWitnessGenerator 95 j * element95 v := by
  decide +kernel
private theorem outside95 : smallParityCensusWitness 95 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 95) :=
  outside_of_reconstruction 95 element95 coordinates95
    (by decide +kernel) left_step95 (by decide +kernel)

-- Witness position 96; census node 130; 4 free binary coordinates.
private abbrev Params96 := FiveFour.Cyclic 4 × ZMod 2 × ZMod 2
private def element96 (v : Params96) : SylowModel :=
  ⟨⟨((v.1.toAdd.val : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2), v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1, ((v.1.toAdd.val : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.1, ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) + ((v.1.toAdd.val : ℕ) : ZMod 2) * v.2.1 + ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.1 + ((v.1.toAdd.val : ℕ) : ZMod 2) * ((v.1.toAdd.val / 2 : ℕ) : ZMod 2) * v.2.1, v.2.2⟩, v.1⟩
private def coordinates96 (x : SylowModel) : Params96 :=
  (x.right, x.left.b4, x.left.b9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step96 : ∀ (v : Params96) (j : Fin 9),
    element96 (coordinates96 (smallParityCensusWitnessGenerator 96 j * element96 v)) =
      smallParityCensusWitnessGenerator 96 j * element96 v := by
  decide +kernel
private theorem outside96 : smallParityCensusWitness 96 ∉
    smallParityCensusNode (smallParityCensusWitnessIndex 96) :=
  outside_of_reconstruction 96 element96 coordinates96
    (by decide +kernel) left_step96 (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- Fine coordinates exclude every witness not handled by the tail quotient. -/
public theorem smallParityCensusWitness_not_mem_of_fine_coordinates (k : Fin 97)
    (hk : k.val ∉ ({0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
      21, 22, 38, 40, 41, 44, 45, 46, 48, 49, 52, 53, 67, 68, 69, 70, 71, 72, 88, 89} :
      Finset ℕ)) :
    smallParityCensusWitness k ∉ smallParityCensusNode (smallParityCensusWitnessIndex k) := by
  fin_cases k
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact outside5
  · exact outside6
  · exact outside7
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact outside23
  · exact outside24
  · exact outside25
  · exact outside26
  · exact outside27
  · exact outside28
  · exact outside29
  · exact outside30
  · exact outside31
  · exact outside32
  · exact outside33
  · exact outside34
  · exact outside35
  · exact outside36
  · exact outside37
  · exact (hk (by decide)).elim
  · exact outside39
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact outside42
  · exact outside43
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact outside47
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact outside50
  · exact outside51
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact outside54
  · exact outside55
  · exact outside56
  · exact outside57
  · exact outside58
  · exact outside59
  · exact outside60
  · exact outside61
  · exact outside62
  · exact outside63
  · exact outside64
  · exact outside65
  · exact outside66
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact outside73
  · exact outside74
  · exact outside75
  · exact outside76
  · exact outside77
  · exact outside78
  · exact outside79
  · exact outside80
  · exact outside81
  · exact outside82
  · exact outside83
  · exact outside84
  · exact outside85
  · exact outside86
  · exact outside87
  · exact (hk (by decide)).elim
  · exact (hk (by decide)).elim
  · exact outside90
  · exact outside91
  · exact outside92
  · exact outside93
  · exact outside94
  · exact outside95
  · exact outside96

end ReeTwo.SylowModel
