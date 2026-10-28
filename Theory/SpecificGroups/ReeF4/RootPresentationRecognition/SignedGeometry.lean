module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NormalizerPresentation
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.PositiveRootCharts
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits

/-!
# The literal sixteen-root Ree Weyl table

There are eight signed positions in each of the pair and quartet families.
The two relative reflections preserve every slot of the ordered split blocks;
only their own simple block changes sign. The explicit finite permutations
satisfy the dihedral relations. Checking the Euclidean F4 roots and using the
proved split root-curve conjugation transports every parameter for all m.
The group induction extends the two simple equations to every Weyl word.

This table uses the existing long/short order inside each pair and the
long, short, mixed, high order inside each quartet. It is a table on relative
roots, not a multiplication table for the full model.
Source: GLS3 2.3.6--8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`.
The coordinate calculation follows FixedCollection/WeylGeometry/Orbits.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SignedGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Parabolics.Binary.FixedGeometry
open Parabolics.RadicalCoordinates FixedCoordinates
open LocalBlockInput.PairRigidity.FixedCollection
open WeylPresentation
abbrev Index := Bool × Fin 4

def next (kind s : Bool) : Fin 4 → Fin 4 :=
  match kind, s with
  | false, false => ![0,2,1,3]
  | false, true => ![1,0,3,2]
  | true, false => ![2,3,0,1]
  | true, true => ![0,1,3,2]

def step (kind s : Bool) (r : Index) : Index :=
  (if kind = s ∧ r.2 = 0 then !r.1 else r.1, next kind s r.2)

theorem step_involutive (kind s : Bool) : Function.Involutive (step kind s) := by
  intro ⟨p,i⟩
  cases kind <;> cases s <;> cases p <;> fin_cases i <;> decide

def reflection (kind s : Bool) : Equiv.Perm Index :=
  Function.Involutive.toPerm (step kind s) (step_involutive kind s)

@[simp] theorem reflection_apply (kind s : Bool) (r : Index) :
    reflection kind s r = step kind s r := rfl

theorem reflection_sq (kind s : Bool) : reflection kind s ^ 2 = 1 := by
  apply Equiv.ext
  intro r
  change step kind s (step kind s r) = r
  exact step_involutive kind s r

theorem reflection_mixed (kind : Bool) : (reflection kind false * reflection kind true)^8 = 1 := by
  cases kind <;> decide

def action (kind : Bool) : Weyl →* Equiv.Perm Index :=
  lift (reflection kind) (reflection_sq kind) (reflection_mixed kind)

@[simp] theorem action_simple (kind s : Bool) : action kind (simple s) = reflection kind s :=
  lift_simple ..

def opposition : Weyl := .r 4

theorem action_opposition (kind : Bool) (r : Index) : action kind opposition r = (!r.1,r.2) := by
  rcases r with ⟨p,i⟩
  cases kind <;> cases p <;> fin_cases i <;> decide

local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

abbrev Slots (kind : Bool) : Type := if kind then Fin 4 else Fin 2

def positiveRoot : (kind : Bool) → Fin 4 → Slots kind → F4Chevalley.Root
  | false, i, j => ((rootBlocks .positive).roots (.inl (i,j))).val
  | true, i, j => ((rootBlocks .positive).roots (.inr (i,j))).val

def root (kind : Bool) (r : Index) (j : Slots kind) : F4Chevalley.Root :=
  if r.1 then positiveRoot kind r.2 j else -positiveRoot kind r.2 j

private theorem neg_val (r : F4Chevalley.Root) : (-r).val = -r.val := by
  change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
  simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

private theorem root_val (kind : Bool) (r : Index) (j : Slots kind) :
    (root kind r j).val =
      if r.1 then (positiveRoot kind r.2 j).val else -(positiveRoot kind r.2 j).val := by
  rcases r with ⟨p,i⟩
  cases p
  · exact neg_val _
  · rfl

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 2000000 in
/-- Every slot, including the two nonsimple Suzuki slots, keeps its order. -/
theorem root_reflection (kind s : Bool) (r : Index) (j : Slots kind) :
    wordAction (sideWord (NormalizerPresentation.side s)) (root kind r j) =
      root kind (step kind s r) j := by
  rcases r with ⟨p,i⟩
  apply Subtype.ext
  cases kind <;> (first | change Fin 2 at j | change Fin 4 at j) <;>
    cases s <;> cases p <;> fin_cases i <;> fin_cases j <;> funext k <;> fin_cases k <;>
    simp only [NormalizerPresentation.side, wordAction, sideWord,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Equiv.Perm.mul_apply, reflection_val, root_val]
  all_goals
    norm_num [positiveRoot, step, next, reflectedVector, rootBlocks_roots_val, RootPartition.index,
      RootPartition.pairRow, RootPartition.quartetRow, RootPartition.table,
      Matrix.cons_val_two, Matrix.cons_val_three]

end ReeF4.RootPresentationRecognition.SignedGeometry

namespace ReeF4.RootPresentationRecognition.SignedGeometry
open WeylPresentation

/-- The two finite reflection equations imply every literal Weyl equation. -/
theorem equivariant {G A : Type*} [Group G] (kind : Bool)
    (n : Weyl →* G) (x : Index → A → G)
    (hs : ∀ s r a, n (simple s) * x r a * (n (simple s))⁻¹ =
      x (step kind s r) a) (w : Weyl) (r : Index) (a : A) :
    n w * x r a * (n w)⁻¹ = x (action kind w r) a := by
  have hw : w ∈ Subgroup.closure (Set.range simple) := by rw [simple_generate]; trivial
  induction hw using Subgroup.closure_induction generalizing r with
  | mem w hw =>
    obtain ⟨s,rfl⟩ := hw
    simpa only [action_simple, reflection_apply] using hs s r a
  | one => simp
  | mul u v _ _ hu hv =>
    rw [map_mul, map_mul, Equiv.Perm.mul_apply]
    calc
      _ = n u * (n v * x r a * (n v)⁻¹) * (n u)⁻¹ := by group
      _ = _ := by rw [hv, hu]
  | inv u _ hu =>
    have he := hu ((action kind u)⁻¹ r)
    have he' := congrArg (fun z => (n u)⁻¹ * z * n u) he
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply, inv_inv, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_one] using he'.symm

open Theory.AlgebraicGroup LargeLocalSeeds Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairRigidity.FixedCollection

/-- All sixteen native Weyl words act on every signed split-root slot. -/
theorem split_conjugation (m : ℕ) (kind : Bool) (w : Weyl) (r : Index)
    (j : Slots kind) (a : CoefficientField m) :
    toSplitGroup m (NormalizerPresentation.weyl m w) * rootGeneratorInGroup m (root kind r j) a *
      (toSplitGroup m (NormalizerPresentation.weyl m w))⁻¹ =
        rootGeneratorInGroup m (root kind (action kind w r) j) a := by
  apply equivariant kind ((toSplitGroup m).comp (NormalizerPresentation.weyl m))
    (fun r (a : CoefficientField m) => rootGeneratorInGroup m (root kind r j) a)
  intro s r a
  change toSplitGroup m (NormalizerPresentation.weyl m (simple s)) * _ *
    (toSplitGroup m (NormalizerPresentation.weyl m (simple s)))⁻¹ = _
  rw [NormalizerPresentation.weyl_simple, toSplitGroup_weylLift,
    simpleWord_conj_root, root_reflection]

end ReeF4.RootPresentationRecognition.SignedGeometry

namespace ReeF4.RootPresentationRecognition.SignedGeometry
open WeylPresentation

/-- The simple signed block is the only positive block made negative. -/
theorem step_positive_iff (kind s : Bool) (i : Fin 4) :
    (step kind s (true,i)).1 = true ↔ kind ≠ s ∨ i ≠ 0 := by
  cases kind <;> cases s <;> fin_cases i <;> decide

def alternating (s : Bool) : ℕ → Weyl
  | 0 => 1
  | k+1 => simple s * alternating (!s) k

@[simp] theorem alternating_zero (s : Bool) : alternating s 0 = 1 := rfl

theorem alternating_longest (s : Bool) : alternating s 8 = opposition := by
  cases s <;> decide

/-- The sixteen dihedral elements have the expected reduced alternating labels. -/
theorem alternating_covers (w : Weyl) : ∃ s : Bool, ∃ k : Fin 9, alternating s k = w := by
  revert w
  decide

/-- All ascent positions carry the opposite simple root into a positive block.
This finite table is the ascending case of the forthcoming Bruhat induction. -/
theorem ascent_positive (s : Bool) (k : Fin 8) :
    (action s (alternating (!s) k)⁻¹ (true,0)).1 = true := by
  cases s <;> fin_cases k <;> decide

end ReeF4.RootPresentationRecognition.SignedGeometry

namespace ReeF4.RootPresentationRecognition.SignedGeometry
open WeylPresentation

/-- The finite root table proves the ascending Bruhat transport in every
realization of the simple equations; no native-model map is supplied. -/
theorem ascent_mem {G A : Type*} [Group G] (kind : Bool)
    (n : Weyl →* G) (x : Index → A → G)
    (hs : ∀ s r a, n (simple s) * x r a * (n (simple s))⁻¹ = x (step kind s r) a)
    (B : Subgroup G) (hpos : ∀ i a, x (true,i) a ∈ B) (k : Fin 8) (a : A) :
    (n (alternating (!kind) k))⁻¹ * x (true,0) a * n (alternating (!kind) k) ∈ B := by
  have he := equivariant kind n x hs (alternating (!kind) k)⁻¹ (true,0) a
  simp only [map_inv, inv_inv] at he
  rw [he]
  have hp := ascent_positive kind k
  have hr : action kind (alternating (!kind) k)⁻¹ (true,0) =
      (true,(action kind (alternating (!kind) k)⁻¹ (true,0)).2) := Prod.ext hp rfl
  rw [map_inv] at hr
  rw [hr]
  exact hpos _ a

end ReeF4.RootPresentationRecognition.SignedGeometry
